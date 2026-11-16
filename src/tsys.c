/* Generic pieces of the theta splitting shared by khinchin.c and theodorus.c: binary splitting with an
   efficient merge, the Kronecker sums for starting values, d/db Gamma(b, y), and moment systems built from
   theta-relations between kernel functions (tsys_t). */
#include <math.h>
#include <string.h>
#include <stdlib.h>
#include "tsys.h"


/* ======================= exact/ball binary splitting with an efficient merge =======================
   As bs_eval in engine.c, but the merge computes [M2 M1; S2 M1 + Q2 S1] directly. */
static void kbs_exact(fmpz_mat_t M, fmpz_mat_t S, fmpz_t Q, slong a, slong b, const bs_t * B)
{
    slong d = B->d, s = B->s, i, j;
    if (b - a == 1)
    {
        fmpz_mat_t T;
        fmpz_mat_init(T, d + s, d);
        fmpz_mat_zero(T);
        B->leaf(T, Q, a, B->ctx);
        for (i = 0; i < d; i++) for (j = 0; j < d; j++) fmpz_swap(fmpz_mat_entry(M, i, j), fmpz_mat_entry(T, i, j));
        for (i = 0; i < s; i++) for (j = 0; j < d; j++) fmpz_swap(fmpz_mat_entry(S, i, j), fmpz_mat_entry(T, d + i, j));
        fmpz_mat_clear(T);
        return;
    }
    {
        slong m = a + (b - a) / 2;
        fmpz_mat_t M2, S2, P; fmpz_t Q2;
        fmpz_mat_init(M2, d, d); fmpz_mat_init(S2, s, d); fmpz_init(Q2);
        kbs_exact(M, S, Q, a, m, B);
        kbs_exact(M2, S2, Q2, m, b, B);
        fmpz_mat_scalar_mul_fmpz(S, S, Q2);
        if (s > 0) { fmpz_mat_init(P, s, d); fmpz_mat_mul(P, S2, M); fmpz_mat_add(S, S, P); fmpz_mat_clear(P); }
        fmpz_mat_init(P, d, d); fmpz_mat_mul(P, M2, M); fmpz_mat_swap(M, P); fmpz_mat_clear(P);
        fmpz_mul(Q, Q, Q2);
        fmpz_mat_clear(M2); fmpz_mat_clear(S2); fmpz_clear(Q2);
    }
}

static void kbs_top(arb_mat_t M, arb_mat_t S, arb_t Q, slong a, slong b, const bs_t * B, slong lim, slong prec)
{
    slong d = B->d, s = B->s;
    if (b - a <= lim)
    {
        fmpz_mat_t Me, Se; fmpz_t Qe;
        fmpz_mat_init(Me, d, d); fmpz_mat_init(Se, s, d); fmpz_init(Qe);
        kbs_exact(Me, Se, Qe, a, b, B);
        arb_mat_set_round_fmpz_mat(M, Me, prec);
        if (s > 0) arb_mat_set_round_fmpz_mat(S, Se, prec);
        arb_set_round_fmpz(Q, Qe, prec);
        fmpz_mat_clear(Me); fmpz_mat_clear(Se); fmpz_clear(Qe);
    }
    else
    {
        slong m = a + (b - a) / 2;
        arb_mat_t M2, S2, P; arb_t Q2;
        arb_mat_init(M2, d, d); arb_mat_init(S2, s, d); arb_init(Q2);
        kbs_top(M, S, Q, a, m, B, lim, prec);
        kbs_top(M2, S2, Q2, m, b, B, lim, prec);
        arb_mat_scalar_mul_arb(S, S, Q2, prec);
        if (s > 0) { arb_mat_init(P, s, d); arb_mat_mul(P, S2, M, prec); arb_mat_add(S, S, P, prec); arb_mat_clear(P); }
        arb_mat_init(P, d, d); arb_mat_mul(P, M2, M, prec); arb_mat_swap(M, P); arb_mat_clear(P);
        arb_mul(Q, Q, Q2, prec);
        arb_mat_clear(M2); arb_mat_clear(S2); arb_clear(Q2);
    }
}

/* sums = S x0 / Q over [a, b) */
void kbs_eval(arb_ptr sums, arb_srcptr x0, slong a, slong b, const bs_t * B, slong prec)
{
    slong d = B->d, s = B->s, i, j, lb, lim;
    arb_mat_t M, S; arb_t Q;
    if (b <= a) { _arb_vec_zero(sums, s); return; }
    {
        fmpz_mat_t T; fmpz_t q;
        fmpz_mat_init(T, d + s, d); fmpz_init(q); fmpz_mat_zero(T);
        B->leaf(T, q, b - 1, B->ctx);
        lb = FLINT_ABS(fmpz_mat_max_bits(T)) + fmpz_bits(q) + 1;
        fmpz_mat_clear(T); fmpz_clear(q);
    }
    lim = FLINT_MAX(1, 2 * prec / lb);
    arb_mat_init(M, d, d); arb_mat_init(S, s, d); arb_init(Q);
    kbs_top(M, S, Q, a, b, B, lim, prec);
    for (i = 0; i < s; i++)
    {
        arb_zero(sums + i);
        for (j = 0; j < d; j++) arb_addmul(sums + i, arb_mat_entry(S, i, j), x0 + j, prec);
        arb_div(sums + i, sums + i, Q, prec);
    }
    arb_mat_clear(M); arb_mat_clear(S); arb_clear(Q);
}

/* ======================= kernel coefficients times the incomplete-gamma recurrence =======================
   Kernel functions f are power series sum_n f_n u^n; their coefficients are w_f(n) . G_n, where
   G_{n+1} = (M(n)/q(n)) G_n is a coefficient recurrence of dimension r.

   The moments Z_t[f](c) = int_0^u0 u^-t e^(-c/u) f(u) du = sum_n f_n D_{n - t + 1}(c), with
   D_a(c) = int_0^u0 u^(a-1) e^(-c/u) du = c^a Gamma(-a, c/u0), a D_a + c D_{a-1} = E u0^a, E = e^(-c/u0).
   With a = ab + n, ab = h/2 (h = -1 or 0), D_{ab+n} = al_n D_ab + be_n E u0^ab, and
   D'_{ab+n} = al_n D'_ab + al'_n D_ab + E u0^ab (be_n log u0 + be'_n) for the log-moments
   Z^log_t[f] = int_0^u0 u^-t log(u) e^(-c/u) f(u) du (D' = dD/da).
   The state Delta = (al, be, T) (mode 3) or (al, al', be, be', T) (mode 5), T_n = u0^n; mode 1 is (T) alone,
   for the values f(u0) = sum_n f_n u0^n. An output (f, delta, kind) is sum_n f_n (R_delta(n) Delta_n)[kind],
   where R_delta(n) Delta_n = Delta_{n + delta}. */



/* One run of the Kronecker sums. The al-part and the be-part of Delta are independent recurrences and are
   summed separately: part 0 = (al) or (al, al'), part 1 = (be, T) or (be, be', T), part 2 = (T) alone. */

static slong kron_dD(const kron_t * K) { return K->part == 2 ? 1 : (K->part == 0 ? 1 : 2) + (K->logs ? 1 : 0); }

/* one step of Delta: Delta_{n+1} = N(n) Delta_n (rational) */
static void delta_step(fmpq_mat_t N, const kron_t * K, slong n)
{
    fmpq_t c, u, i1, t, t2;
    fmpq_init(c); fmpq_init(u); fmpq_init(i1); fmpq_init(t); fmpq_init(t2);
    fmpq_mat_zero(N);
    fmpq_set_fmpz_frac(c, K->C, K->D);
    fmpq_set_fmpz_frac(u, U0_NUM, U0_DEN);
    {
        slong td = K->td ? K->td : 2;
        fmpq_set_si(i1, td, td * n + K->h + td);                 /* 1/(a + 1) */
    }
    fmpq_mul(t, c, i1); fmpq_neg(t, t);                         /* -c/(a+1) */
    fmpq_mul(t2, c, i1); fmpq_mul(t2, t2, i1);                  /* c/(a+1)^2 */
    if (K->part == 2)
        fmpq_set(fmpq_mat_entry(N, 0, 0), u);
    else if (K->part == 0)
    {
        fmpq_set(fmpq_mat_entry(N, 0, 0), t);
        if (K->logs) { fmpq_set(fmpq_mat_entry(N, 1, 1), t); fmpq_set(fmpq_mat_entry(N, 1, 0), t2); }
    }
    else if (!K->logs)
    {
        /* (be, T): be_{n+1} = (u T - c be)/(a+1) */
        fmpq_set(fmpq_mat_entry(N, 0, 0), t);
        fmpq_mul(fmpq_mat_entry(N, 0, 1), u, i1);
        fmpq_set(fmpq_mat_entry(N, 1, 1), u);
    }
    else
    {
        /* (be, be', T): be'_{n+1} = (-be_{n+1} - c be'_n)/(a+1) */
        fmpq_set(fmpq_mat_entry(N, 0, 0), t);
        fmpq_mul(fmpq_mat_entry(N, 0, 2), u, i1);
        fmpq_set(fmpq_mat_entry(N, 1, 0), t2);
        fmpq_set(fmpq_mat_entry(N, 1, 1), t);
        fmpq_mul(fmpq_mat_entry(N, 1, 2), u, i1); fmpq_mul(fmpq_mat_entry(N, 1, 2), fmpq_mat_entry(N, 1, 2), i1);
        fmpq_neg(fmpq_mat_entry(N, 1, 2), fmpq_mat_entry(N, 1, 2));
        fmpq_set(fmpq_mat_entry(N, 2, 2), u);
    }
    fmpq_clear(c); fmpq_clear(u); fmpq_clear(i1); fmpq_clear(t); fmpq_clear(t2);
}

/* the leaf, in integer arithmetic: q = qG dN dS, M = MG (dN N) dS, S = (dS S) qG dN */
static void kron_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * vctx)
{
    const kron_t * K = vctx;
    const coef_t * co = K->co;
    slong r = co->r, dD = kron_dD(K), d = r * dD, i, i2, j, j2, o, maxd = 0;
    fmpz_mat_t Mg, Ni; fmpz_t qg, dN, dS, t;
    fmpq_mat_t N, R[4];
    fmpq_mat_t Sr;
    fmpq * w = _fmpq_vec_init(r);
    fmpz_mat_init(Mg, r, r); fmpz_init(qg); fmpz_init(dN); fmpz_init(dS); fmpz_init(t);
    fmpz_mat_zero(Mg);
    co->leaf(Mg, qg, n);
    fmpq_mat_init(N, dD, dD);
    for (o = 0; o < K->nout; o++) maxd = FLINT_MAX(maxd, K->od[o]);
    for (j = 0; j <= maxd; j++) fmpq_mat_init(R[j], dD, dD);
    fmpq_mat_one(R[0]);
    for (j = 1; j <= maxd; j++)
    {
        delta_step(N, K, n + j - 1);
        fmpq_mat_mul(R[j], N, R[j - 1]);
    }
    delta_step(N, K, n);
    /* integer N: Ni = dN N */
    fmpz_mat_init(Ni, dD, dD);
    fmpz_one(dN);
    for (j = 0; j < dD; j++) for (j2 = 0; j2 < dD; j2++) fmpz_lcm(dN, dN, fmpq_denref(fmpq_mat_entry(N, j, j2)));
    for (j = 0; j < dD; j++) for (j2 = 0; j2 < dD; j2++)
    {
        fmpz_divexact(fmpz_mat_entry(Ni, j, j2), dN, fmpq_denref(fmpq_mat_entry(N, j, j2)));
        fmpz_mul(fmpz_mat_entry(Ni, j, j2), fmpz_mat_entry(Ni, j, j2), fmpq_numref(fmpq_mat_entry(N, j, j2)));
    }
    /* rational S, its common denominator dS */
    fmpq_mat_init(Sr, K->nout, d);
    for (o = 0; o < K->nout; o++)
    {
        for (i = 0; i < r; i++) fmpq_zero(w + i);
        co->weight(w, K->of[o], n);
        for (i = 0; i < r; i++)
            if (!fmpq_is_zero(w + i))
                for (j = 0; j < dD; j++)
                    if (!fmpq_is_zero(fmpq_mat_entry(R[K->od[o]], K->ok[o], j)))
                        fmpq_mul(fmpq_mat_entry(Sr, o, i * dD + j), w + i, fmpq_mat_entry(R[K->od[o]], K->ok[o], j));
    }
    fmpz_one(dS);
    for (i = 0; i < K->nout; i++) for (j = 0; j < d; j++) fmpz_lcm(dS, dS, fmpq_denref(fmpq_mat_entry(Sr, i, j)));
    fmpz_mul(q, qg, dN); fmpz_mul(q, q, dS);
    for (i = 0; i < r; i++) for (i2 = 0; i2 < r; i2++)
    {
        if (fmpz_is_zero(fmpz_mat_entry(Mg, i, i2))) continue;
        fmpz_mul(t, fmpz_mat_entry(Mg, i, i2), dS);
        for (j = 0; j < dD; j++) for (j2 = 0; j2 < dD; j2++)
            fmpz_mul(fmpz_mat_entry(T, i * dD + j, i2 * dD + j2), t, fmpz_mat_entry(Ni, j, j2));
    }
    fmpz_mul(t, qg, dN);
    for (i = 0; i < K->nout; i++) for (j = 0; j < d; j++)
    {
        fmpq * e = fmpq_mat_entry(Sr, i, j);
        if (fmpq_is_zero(e)) continue;
        fmpz_divexact(fmpz_mat_entry(T, d + i, j), dS, fmpq_denref(e));
        fmpz_mul(fmpz_mat_entry(T, d + i, j), fmpz_mat_entry(T, d + i, j), fmpq_numref(e));
        fmpz_mul(fmpz_mat_entry(T, d + i, j), fmpz_mat_entry(T, d + i, j), t);
    }
    for (j = 0; j <= maxd; j++) fmpq_mat_clear(R[j]);
    fmpq_mat_clear(N); fmpq_mat_clear(Sr); fmpz_mat_clear(Ni);
    fmpz_mat_clear(Mg); fmpz_clear(qg); fmpz_clear(dN); fmpz_clear(dS); fmpz_clear(t);
    _fmpq_vec_clear(w, r);
}

/* sums[o] for n in [0, N) */
static void kron_sums(arb_ptr sums, kron_t * K, slong N, slong prec)
{
    slong r = K->co->r, dD = kron_dD(K), i;
    fmpq * g0 = _fmpq_vec_init(r);
    arb_ptr x0 = _arb_vec_init(r * dD);
    bs_t B;
    K->co->init(g0);
    for (i = 0; i < r; i++)
    {
        /* Delta_0: al = 1, al' = 0 (part 0); be = be' = 0, T = 1 (parts 1, 2) */
        if (K->part == 0) arb_set_fmpq(x0 + i * dD, g0 + i, prec);
        else arb_set_fmpq(x0 + i * dD + dD - 1, g0 + i, prec);
    }
    B.d = r * dD; B.s = K->nout; B.leaf = kron_leaf; B.ctx = K;
    if (K->nout > 0) kbs_eval(sums, x0, 0, N, &B, prec);
    _fmpq_vec_clear(g0, r); _arb_vec_clear(x0, r * dD);
}

/* ======================= d/db Gamma(b, y) at b = 1/2 and b = 0 ======================= */

/* Legendre's continued fraction for Gamma(a, y), y = p/q, a = an/ad, with the derivative in a by forward mode
   (as in somos.c): Gamma(a, y) = e^-y y^a 2 q ad / X */
typedef struct { slong an, ad; fmpz_t p, q; } cfj_ctx;
typedef struct { fmpz a[4], d[4]; } jblk;

static void jblk_init(jblk * B) { int i; for (i = 0; i < 4; i++) { fmpz_init(B->a + i); fmpz_init(B->d + i); } }
static void jblk_clear(jblk * B) { int i; for (i = 0; i < 4; i++) { fmpz_clear(B->a + i); fmpz_clear(B->d + i); } }

static void m2mul(fmpz * R, const fmpz * X, const fmpz * Y)
{
    fmpz_mul(R + 0, X + 0, Y + 0); fmpz_addmul(R + 0, X + 1, Y + 2);
    fmpz_mul(R + 1, X + 0, Y + 1); fmpz_addmul(R + 1, X + 1, Y + 3);
    fmpz_mul(R + 2, X + 2, Y + 0); fmpz_addmul(R + 2, X + 3, Y + 2);
    fmpz_mul(R + 3, X + 2, Y + 1); fmpz_addmul(R + 3, X + 3, Y + 3);
}
static void m2addmul(fmpz * R, const fmpz * X, const fmpz * Y)
{
    fmpz_addmul(R + 0, X + 0, Y + 0); fmpz_addmul(R + 0, X + 1, Y + 2);
    fmpz_addmul(R + 1, X + 0, Y + 1); fmpz_addmul(R + 1, X + 1, Y + 3);
    fmpz_addmul(R + 2, X + 2, Y + 0); fmpz_addmul(R + 2, X + 3, Y + 2);
    fmpz_addmul(R + 3, X + 2, Y + 1); fmpz_addmul(R + 3, X + 3, Y + 3);
}

static void jleaf(jblk * B, slong n, const cfj_ctx * c)
{
    int i;
    for (i = 0; i < 4; i++) { fmpz_zero(B->a + i); fmpz_zero(B->d + i); }
    if (n % 2 == 0) fmpz_mul_ui(B->a + 0, c->p, 2 * c->ad); else fmpz_set_ui(B->a + 0, 2 * c->ad);
    if (n % 2 == 1)
    {
        fmpz_mul_ui(B->a + 1, c->q, 2 * c->ad);
        fmpz_mul_si(B->a + 1, B->a + 1, (n + 1) * c->ad - 2 * c->an);
        fmpz_mul_si(B->d + 1, c->q, -4 * c->ad * c->ad);
    }
    else
    {
        fmpz_mul_ui(B->a + 1, c->q, 2); fmpz_mul_ui(B->a + 1, B->a + 1, c->ad); fmpz_mul_ui(B->a + 1, B->a + 1, c->ad);
        fmpz_mul_ui(B->a + 1, B->a + 1, n);
    }
    fmpz_one(B->a + 2);
}

static void jbs(jblk * R, slong a, slong b, const cfj_ctx * c)
{
    jblk L, U; slong m;
    if (b - a == 1) { jleaf(R, a, c); return; }
    m = a + (b - a) / 2;
    jblk_init(&L); jblk_init(&U);
    jbs(&L, a, m, c); jbs(&U, m, b, c);
    m2mul(R->a, U.a, L.a);
    m2mul(R->d, U.a, L.d); m2addmul(R->d, U.d, L.a);
    jblk_clear(&L); jblk_clear(&U);
}

static void am2mul(arb_ptr R, arb_srcptr X, arb_srcptr Y, int add, slong prec)
{
    int i, j; arb_t t; arb_init(t);
    for (i = 0; i < 2; i++) for (j = 0; j < 2; j++)
    {
        arb_mul(t, X + 2 * i, Y + j, prec); arb_addmul(t, X + 2 * i + 1, Y + 2 + j, prec);
        if (add) arb_add(R + 2 * i + j, R + 2 * i + j, t, prec); else arb_swap(R + 2 * i + j, t);
    }
    arb_clear(t);
}

static void ajbs(arb_ptr A, arb_ptr D, slong a, slong b, slong lim, const cfj_ctx * c, slong prec)
{
    if (b - a <= lim)
    {
        jblk G; int i; jblk_init(&G); jbs(&G, a, b, c);
        for (i = 0; i < 4; i++) { arb_set_round_fmpz(A + i, G.a + i, prec); arb_set_round_fmpz(D + i, G.d + i, prec); }
        jblk_clear(&G);
    }
    else
    {
        arb_ptr A1 = _arb_vec_init(4), D1 = _arb_vec_init(4), A2 = _arb_vec_init(4), D2 = _arb_vec_init(4);
        slong m = a + (b - a) / 2;
        ajbs(A1, D1, a, m, lim, c, prec); ajbs(A2, D2, m, b, lim, c, prec);
        am2mul(A, A2, A1, 0, prec);
        am2mul(D, A2, D1, 0, prec); am2mul(D, D2, A1, 1, prec);
        _arb_vec_clear(A1, 4); _arb_vec_clear(D1, 4); _arb_vec_clear(A2, 4); _arb_vec_clear(D2, 4);
    }
}

/* X (convergent value) and dX/da; returns 1 if accurate to W bits */
static int cf_jet(arb_t X, arb_t dX, slong an, slong ad, const fmpz_t p, const fmpz_t q, slong ns, slong W)
{
    cfj_ctx c; slong prec = W + 64, lb, i;
    arb_ptr A = _arb_vec_init(4), D = _arb_vec_init(4);
    arb_t b0, xa, xb, da, db, t;
    int ok;
    jblk G;
    c.an = an; c.ad = ad; fmpz_init_set(c.p, p); fmpz_init_set(c.q, q);
    arb_init(b0); arb_init(xa); arb_init(xb); arb_init(da); arb_init(db); arb_init(t);
    jblk_init(&G); jleaf(&G, ns, &c);
    lb = FLINT_MAX(fmpz_bits(G.a + 0), fmpz_bits(G.a + 1)) + 2;
    jblk_clear(&G);
    ajbs(A, D, 1, ns + 1, FLINT_MAX(1, 2 * prec / lb), &c, prec);
    /* T = [[A0 A1 D0 D1],[A2 A3 D2 D3]] as in somos.c */
    arb_set_fmpz(b0, p); arb_mul_ui(b0, b0, 2 * ad, prec);
    arb_div(xa, A + 1, A + 0, prec); arb_add(xa, xa, b0, prec);
    arb_div(xb, A + 3, A + 2, prec); arb_add(xb, xb, b0, prec);
    arb_mul(da, D + 1, A + 0, prec); arb_submul(da, A + 1, D + 0, prec);
    arb_div(da, da, A + 0, prec); arb_div(da, da, A + 0, prec);
    arb_mul(db, D + 3, A + 2, prec); arb_submul(db, A + 3, D + 2, prec);
    arb_div(db, db, A + 2, prec); arb_div(db, db, A + 2, prec);
    arb_sub(t, da, db, prec);
    { mag_t m; mag_init(m); arb_get_mag(m, t); mag_mul_2exp_si(m, m, 1); arb_add_error_mag(da, m); mag_clear(m); }
    arb_set(dX, da);
    arb_union(X, xa, xb, prec);
    ok = arb_rel_accuracy_bits(X) >= W && arb_rel_accuracy_bits(dX) >= W - 8;
    (void) i;
    _arb_vec_clear(A, 4); _arb_vec_clear(D, 4);
    arb_clear(b0); arb_clear(xa); arb_clear(xb); arb_clear(da); arb_clear(db); arb_clear(t);
    fmpz_clear(c.p); fmpz_clear(c.q);
    return ok;
}

/* lower series, b = 1/2: t_n = y^n/(1/2)_(n+1), u_n = t_n H_n, H_n = sum_{i<=n} 1/(i+1/2) */
typedef struct { fmpz_t p, q; } pq_ctx;
static void lh_leaf(fmpz_mat_t T, fmpz_t qq, slong n, const void * v)
{
    const pq_ctx * c = v;
    fmpz_mul_ui(qq, c->q, (ulong) (2 * n + 3) * (2 * n + 3));
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), c->p, 2 * (2 * n + 3));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), c->p, 2 * (2 * n + 3));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), c->p, 4);
    fmpz_set(fmpz_mat_entry(T, 2, 0), qq);
    fmpz_set(fmpz_mat_entry(T, 3, 1), qq);
}
/* lower series, b = 0: t_n = y^n/n!, (t H_n, t (H_n^2 + H2_n)) */
static void lz_leaf(fmpz_mat_t T, fmpz_t qq, slong n, const void * v)
{
    const pq_ctx * c = v;
    ulong n1 = n + 1;
    fmpz_mul_ui(qq, c->q, n1); fmpz_mul_ui(qq, qq, n1); fmpz_mul_ui(qq, qq, n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), c->p, n1 * n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), c->p, n1 * n1); fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), c->p, n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 2), c->p, n1 * n1); fmpz_mul_ui(fmpz_mat_entry(T, 2, 1), c->p, 2 * n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), c->p, 2);
    fmpz_set(fmpz_mat_entry(T, 3, 1), qq);
    fmpz_set(fmpz_mat_entry(T, 4, 2), qq);
}

/* G = Gamma(b, y), dG = d/db Gamma(b, y) for b = 1/2 (half) or b = 0, y = p/q > 0; relative accuracy ~W */
void dgamma_upper(arb_t G, arb_t dG, int half, const fmpz_t p, const fmpz_t q, slong W)
{
    double yd = fmpz_get_d(p) / fmpz_get_d(q);
    slong Wl = W + (slong) (LOG2E * yd) + 64, nlow;
    double ncf = pow((W + 20) / 2.4, 2) / yd + 1000, l = 0;
    arb_t y, t, L, s;
    arb_init(y); arb_init(t); arb_init(L); arb_init(s);
    /* lower series length: y^n/n! below 2^-Wl e^y */
    for (nlow = 1; ; nlow++)
    {
        l += log2(yd) - log2((double) nlow);
        if (nlow > yd && l + 2 * log2((double) nlow) < LOG2E * yd - Wl - 20) break;
    }
    arb_set_fmpz(y, p); arb_div_fmpz(y, y, q, Wl);
    if (1.5 * ncf < (double) nlow)
    {
        slong ns = (slong) ncf;
        arb_t X, dX;
        arb_init(X); arb_init(dX);
        while (!cf_jet(X, dX, half ? 1 : 0, half ? 2 : 1, p, q, ns, W + 20)) ns = ns * 3 / 2;
        /* Gamma = e^-y y^b 2 q ad / X, d/db log Gamma = log y - dX/X */
        arb_neg(t, y); arb_exp(t, t, W + 64);
        arb_mul_fmpz(t, t, q, W + 64); arb_mul_ui(t, t, half ? 4 : 2, W + 64);
        if (half) { arb_sqrt(s, y, W + 64); arb_mul(t, t, s, W + 64); }
        arb_div(G, t, X, W + 64);
        arb_log(L, y, W + 64);
        arb_div(s, dX, X, W + 64); arb_sub(s, L, s, W + 64);
        arb_mul(dG, G, s, W + 64);
        arb_clear(X); arb_clear(dX);
    }
    else
    {
        pq_ctx c; bs_t B; arb_ptr x0 = _arb_vec_init(3), sm = _arb_vec_init(2);
        arb_t e, g;
        arb_init(e); arb_init(g);
        fmpz_init_set(c.p, p); fmpz_init_set(c.q, q);
        arb_neg(e, y); arb_exp(e, e, Wl);
        arb_log(L, y, Wl);
        if (half)
        {
            B.d = 2; B.s = 2; B.leaf = lh_leaf; B.ctx = &c;
            arb_set_ui(x0, 2); arb_set_ui(x0 + 1, 4);
            bs_eval(NULL, sm, x0, 0, nlow, &B, Wl);
            arb_sqrt(s, y, Wl); arb_mul(s, s, e, Wl);
            arb_mul(g, sm, s, Wl);                                  /* gamma(1/2, y) */
            arb_const_sqrt_pi(t, Wl);
            arb_sub(G, t, g, Wl);
            /* sqrt(pi) psi(1/2) - log y gamma + sqrt(y) e^-y Su */
            arb_const_euler(dG, Wl); arb_const_log2(L, Wl); arb_mul_2exp_si(L, L, 1); arb_add(dG, dG, L, Wl);
            arb_neg(dG, dG); arb_mul(dG, dG, t, Wl);
            arb_log(L, y, Wl);
            arb_submul(dG, L, g, Wl);
            arb_addmul(dG, s, sm + 1, Wl);
        }
        else
        {
            arb_t S1, S2, c2;
            arb_init(S1); arb_init(S2); arb_init(c2);
            B.d = 3; B.s = 2; B.leaf = lz_leaf; B.ctx = &c;
            arb_one(x0);
            bs_eval(NULL, sm, x0, 0, nlow, &B, Wl);
            arb_mul(S1, sm, e, Wl); arb_mul(S2, sm + 1, e, Wl);
            arb_const_euler(t, Wl);
            arb_add(G, t, L, Wl); arb_sub(G, S1, G, Wl);             /* E1 = -gamma - L + S1 */
            arb_sqr(c2, t, Wl); arb_mul_2exp_si(c2, c2, -1);
            arb_const_pi(t, Wl); arb_sqr(t, t, Wl); arb_div_ui(t, t, 12, Wl); arb_add(c2, c2, t, Wl);
            arb_sqr(t, L, Wl); arb_mul_2exp_si(t, t, -1); arb_sub(dG, c2, t, Wl);
            arb_addmul(dG, L, S1, Wl);
            arb_mul_2exp_si(t, S2, -1); arb_sub(dG, dG, t, Wl);
            arb_clear(S1); arb_clear(S2); arb_clear(c2);
        }
        _arb_vec_clear(x0, 3); _arb_vec_clear(sm, 2); arb_clear(e); arb_clear(g);
        fmpz_clear(c.p); fmpz_clear(c.q);
    }
    arb_clear(y); arb_clear(t); arb_clear(L); arb_clear(s);
}

/* ======================= moment systems from theta-relations =======================
   theta f_f = sum (num/den) u^p f_k over the terms; components (f, o, s) hold c^(l + o) Z_{t0 + l + s}[f]
   (o = 0, or o = -1 for lags). Rows with o = 0 come from integration by parts,
   c Z_{t+1}[f] = E u0^(1-t) f(u0) - (1 - t) Z_t[f] - Z_t[theta f],  Z_t[u^p g] = Z_{t-p}[g];
   rows with o = -1 shift the index. */

static int tsys_td(const tsys_t * T) { return T->tden ? T->tden : 2; }

static int tsys_find(const tsys_t * T, int f, int o, int s)
{
    int i;
    for (i = 0; i < T->ncomp; i++)
        if (T->comps[i].f == f && T->comps[i].o == o && T->comps[i].s == s) return i;
    return -1;
}

static void tsys_amat(fmpz * A, slong l, const fmpz_t C, const fmpz_t D, const void * ctx)
{
    const tsys_t * T = ctx;
    int d = T->ncomp, i, j, t, td = tsys_td(T);
    fmpz_t v; fmpz_init(v);
    for (i = 0; i < d; i++)
    {
        const tcomp_t * cp = T->comps + i;
        if (cp->o == 0)
        {
            fmpz_mul_si(v, D, T->den * (T->twot0 + td * (l + cp->s - 1)));
            fmpz_add(A + i * d + i, A + i * d + i, v);
            for (t = 0; t < T->nterms; t++)
            {
                const tterm_t * tm = T->terms + t;
                if (tm->f != cp->f) continue;
                j = tsys_find(T, tm->k, 0, cp->s - tm->p);
                if (j >= 0) { fmpz_mul_si(v, D, -td * tm->num); fmpz_add(A + i * d + j, A + i * d + j, v); }
                else
                {
                    j = tsys_find(T, tm->k, -1, cp->s - tm->p);
                    if (j < 0) flint_abort();
                    fmpz_mul_si(v, C, -td * tm->num); fmpz_add(A + i * d + j, A + i * d + j, v);
                }
            }
        }
        else
        {
            j = tsys_find(T, cp->f, 0, cp->s + 1);
            if (j >= 0) { fmpz_mul_si(v, D, td * T->den); fmpz_add(A + i * d + j, A + i * d + j, v); }
            else
            {
                j = tsys_find(T, cp->f, -1, cp->s + 1);
                if (j < 0) flint_abort();
                fmpz_mul_si(v, C, td * T->den); fmpz_add(A + i * d + j, A + i * d + j, v);
            }
        }
    }
    fmpz_clear(v);
}

/* the outputs needed for the starting values: per component (f, s), kinds al, be (+ al', be' for log f) */
static void tsys_outputs(tsys_t * T)
{
    int i, kind, part, haslog = 0, td = tsys_td(T);
    /* ab in (-1, 0] with ab = 1 - t0 mod 1, h = td ab */
    slong r = (((td - T->twot0) % td) + td) % td, h = r ? r - td : 0;
    for (i = 0; i < T->nf; i++) if (T->islog[i]) haslog = 1;
    for (part = 0; part < 2; part++)
    {
        T->K[part].co = T->co; T->K[part].part = part; T->K[part].logs = haslog; T->K[part].h = h; T->K[part].td = td; T->K[part].nout = 0;
    }
    for (i = 0; i < T->ncomp; i++)
    {
        /* Z_{t0 + s}[f] = sum_j f_j D_{j - t0 - s + 1}, index n = j + delta, delta = 1 - t0 - s - ab */
        int delta, num = td - T->twot0 - td * T->comps[i].s - (int) h;
        if (num % td != 0) flint_abort();
        delta = num / td;
        int nk = T->islog[T->comps[i].f] ? 4 : 2;
        for (kind = 0; kind < nk; kind++)
        {
            /* kind 0 = al, 1 = be, 2 = al', 3 = be' */
            kron_t * K = T->K + (kind % 2);
            slong o = K->nout++;
            if (o >= KMAXO) flint_abort();
            K->of[o] = T->comps[i].f; K->od[o] = delta; K->ok[o] = kind / 2;
            T->oidx[i][kind] = o;
        }
    }
}

/* number of terms of the starting-value series at c (kernel of exponential type R2). The al-part terms f_n al_n
   are at most n^4 (R2 c)^n/(n!)^2, the be-part terms f_n be_n at most n^4 (R2 u0)^n/n! (since D_a ~ E u0^a/a),
   times a constant. */
static slong tsys_terms(double c, int R2, slong W, int part)
{
    double l2z = log2(R2 * (part == 0 ? c : U0_D) + 1e-6), lt; slong j;
    for (j = 1; ; j++)
    {
        lt = j * l2z - (part == 0 ? 2 : 1) * lgamma(j + 1.0) / log(2.0) + 4 * log2(j + 1.0) + 8;
        if (j > 4 && (part == 1 || j > 2 * sqrt(R2 * c)) && lt < -W - 64) return j + 1;
    }
}

static void tsys_init(arb_ptr V, arb_t E, const fmpz_t C, slong e, slong wp, const void * vsys)
{
    const moment_sys_t * S = vsys;
    const tsys_t * T0 = S->actx;
    tsys_t T;
    arb_t c, y, Db, dDb, G, dG, Eu, logc, logu0, t;
    arb_ptr sm;
    fmpz_t yq;
    double cd = ldexp(fmpz_get_d(C), -(int) e);
    slong W = wp + (slong) (LOG2E * cd / U0_D + 12 * sqrt(T0->R2 * cd)) + 64, N, i;
    int half = (T0->twot0 % 2) != 0, td = tsys_td(T0);
    memcpy(&T, T0, sizeof(tsys_t));
    arb_init(c); arb_init(y); arb_init(Db); arb_init(dDb); arb_init(G); arb_init(dG); arb_init(Eu);
    arb_init(logc); arb_init(logu0); arb_init(t);
    fmpz_init(yq);
    sm = _arb_vec_init(T.K[0].nout + T.K[1].nout);
    arb_set_fmpz(c, C); arb_mul_2exp_si(c, c, -e);
    /* y = c/u0 = C ud/(un 2^e) */
    arb_mul_fmpz(y, c, U0_DEN, ARF_PREC_EXACT); arb_div_fmpz(y, y, U0_NUM, W);
    arb_neg(E, y); arb_exp(E, E, W);
    if (td != 2)
    {
        /* ab = h/td in (-1, 0): D_ab = c^ab Gamma(-ab, y), E u0^ab (no log functions) */
        fmpq_t a;
        slong h = T.K[0].h, j;
        for (j = 0; j < T.nf; j++) if (T.islog[j]) flint_abort();
        fmpq_init(a);
        if (h == 0) flint_abort();
        fmpq_set_si(a, -h, td);
        gamma_upper_fmpq_exact(G, a, y, NULL, W);
        fmpq_neg(a, a);
        arb_pow_fmpq(t, c, a, W); arb_mul(Db, G, t, W);
        arb_pow_fmpq(t, U0, a, W); arb_mul(Eu, E, t, W);
        arb_zero(dDb);
        fmpq_clear(a);
    }
    else
    {
    {
        fmpz_t p, q;
        fmpz_init(p); fmpz_init(q);
        fmpz_mul(p, C, U0_DEN); fmpz_one(q); fmpz_mul_2exp(q, q, e); fmpz_mul(q, q, U0_NUM);
        dgamma_upper(G, dG, half, p, q, W);
        fmpz_clear(p); fmpz_clear(q);
    }
    arb_log(logc, c, W);
    if (half)
    {
        /* D_{-1/2} = c^-1/2 Gamma(1/2, y), D' = log c D - c^-1/2 dGamma(1/2, y); E u0^{-1/2} */
        arb_rsqrt(t, c, W);
        arb_mul(Db, G, t, W);
        arb_mul(dDb, logc, Db, W); arb_submul(dDb, t, dG, W);
        arb_rsqrt(t, U0, W); arb_mul(Eu, E, t, W);
    }
    else
    {
        arb_set(Db, G);
        arb_mul(dDb, logc, Db, W); arb_sub(dDb, dDb, dG, W);
        arb_set(Eu, E);
    }
    }
    for (i = 0; i < 2; i++)
    {
        N = tsys_terms(cd, T.R2, W, i);
        fmpz_init_set(T.K[i].C, C); fmpz_init(T.K[i].D); fmpz_one(T.K[i].D); fmpz_mul_2exp(T.K[i].D, T.K[i].D, e);
        kron_sums(sm + (i == 0 ? 0 : T.K[0].nout), T.K + i, N, W);
    }
    arb_log(logu0, U0, W);
    for (i = 0; i < T.ncomp; i++)
    {
        arb_ptr v = V + i;
        const slong * oi = T.oidx[i];
        arb_srcptr A0 = sm + oi[0], B0 = sm + T.K[0].nout + oi[1];
        if (!T.islog[T.comps[i].f])
        {
            arb_mul(v, Db, A0, W); arb_addmul(v, Eu, B0, W);
        }
        else
        {
            arb_srcptr A1 = sm + oi[2], B1 = sm + T.K[0].nout + oi[3];
            arb_mul(v, dDb, A0, W); arb_addmul(v, Db, A1, W);
            arb_mul(t, logu0, B0, W); arb_add(t, t, B1, W);
            arb_addmul(v, Eu, t, W);
        }
        if (T.comps[i].o == -1) arb_div(v, v, c, W);
    }
    for (i = 0; i < 2; i++) { fmpz_clear(T.K[i].C); fmpz_clear(T.K[i].D); }
    _arb_vec_clear(sm, T.K[0].nout + T.K[1].nout);
    arb_clear(c); arb_clear(y); arb_clear(Db); arb_clear(dDb); arb_clear(G); arb_clear(dG); arb_clear(Eu);
    arb_clear(logc); arb_clear(logu0); arb_clear(t);
    fmpz_clear(yq);
}

/* f(u0) for all functions (mode 1) */
static void tsys_values(tsys_t * T, slong prec)
{
    kron_t K;
    slong N, i;
    double l = 0;
    memset(&K, 0, sizeof(K));
    K.co = T->co; K.part = 2; K.logs = 0; K.h = 0; K.td = 2; K.nout = T->nf;
    fmpz_init(K.C); fmpz_init(K.D); fmpz_one(K.D);
    for (i = 0; i < T->nf; i++) { K.of[i] = i; K.od[i] = 0; K.ok[i] = 0; }
    for (N = 1; ; N++) { l += log2(T->R2 * U0_D + 0.01) - log2((double) N) + 2; if (N > 10 && l < -prec - 64) break; }
    T->fu0 = _arb_vec_init(T->nf);
    kron_sums(T->fu0, &K, N + 1, prec + 64);
    fmpz_clear(K.C); fmpz_clear(K.D);
}

void tsys_build(moment_sys_t * S, tsys_t * T, slong prec)
{
    int i, ng = 0;
    arb_t lu, t;
    arb_init(lu); arb_init(t);
    tsys_outputs(T);
    tsys_values(T, prec);
    arb_log(lu, U0, prec + 64);
    memset(S, 0, sizeof(*S));
    S->d = T->ncomp; S->t0 = T->twot0 / (double) tsys_td(T);
    /* tsys_amat writes td D den A = 2 D aden A */
    S->amatc = tsys_amat; S->actx = T; S->aden = T->den * tsys_td(T) / 2; S->init = tsys_init; S->amat = NULL;
    for (i = 0; i < T->ncomp; i++) if (T->comps[i].o == 0) ng++;
    S->ng = ng;
    S->kappa = _arb_vec_init(ng);
    ng = 0;
    for (i = 0; i < T->ncomp; i++)
    {
        const tcomp_t * cp = T->comps + i;
        S->lag[i] = cp->o;
        if (cp->o == 0)
        {
            /* kappa = f(u0) u0^-s (times log u0 for log functions) */
            arb_set(S->kappa + ng, T->fu0 + cp->f);
            if (T->islog[cp->f]) arb_mul(S->kappa + ng, S->kappa + ng, lu, prec + 64);
            arb_pow_ui(t, U0, -cp->s, prec + 64);
            arb_mul(S->kappa + ng, S->kappa + ng, t, prec + 64);
            S->fsel[i] = ng++;
        }
        else S->fsel[i] = -1;
    }
    arb_init(S->f0scale);
    /* u0^(1 - t0) */
    {
        fmpq_t ex; fmpq_init(ex);
        fmpq_set_si(ex, tsys_td(T) - T->twot0, tsys_td(T));
        arb_pow_fmpq(S->f0scale, U0, ex, prec + 64);
        fmpq_clear(ex);
    }
    arb_clear(lu); arb_clear(t);
}

void tsys_clear(moment_sys_t * S, tsys_t * T)
{
    moment_sys_clear(S);
    _arb_vec_clear(T->fu0, T->nf);
}

/* ======================= common helpers ======================= */

slong kd_prec(double size_log2, slong prec)  /* working precision for a term of size 2^size_log2 */
{
    return prec + (slong) size_log2 + 64;
}

/* number of terms of sum_m (c/K)^m (e^-x e_m(x)-like weights) to absolute 2^-prec */

slong kseries_terms(double cK, double x, slong prec)
{
    double lx = log2(x), lt; slong m;
    for (m = 2; ; m++)
    {
        double poi = (m - 1 < x) ? (m - 1) * lx - lgamma((double) m) / log(2.0) + 1 : LOG2E * x;
        lt = m * log2(cK) + FLINT_MIN(LOG2E * x, poi) + log2(log((double) m) + 2) + 2;
        if (lt - LOG2E * x < -prec - 40) return m + 1;
    }
}

/* number of terms of a factorial-type series with ratio ~ z/m to 2^-prec */
slong fact_terms(double z, slong prec)
{
    double l = 0; slong m;
    for (m = 1; ; m++) { l += log2(z + 1e-9) - log2((double) m) + 1; if (m > 4 && l < -prec - 64) return m + 1; }
}

void pi2c(arb_t c, double mm, slong prec)  /* c = pi^2 mm^2 with mm = m or m + 1/2 (exact in double) */
{
    arb_t t; arb_init(t);
    arb_set_d(t, mm);
    arb_const_pi(c, prec); arb_mul(c, c, t, prec); arb_sqr(c, c, prec);
    arb_clear(t);
}
