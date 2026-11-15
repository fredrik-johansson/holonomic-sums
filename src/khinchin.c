/*
    Khinchin's constant K = 2.6854520010... by three theta splittings (Section "Khinchin's constant" of the paper):

      khinchin_Z      log K = -Z'(0),  Z(s) = sum_k p_k k^-s, p_k = log2(1 + 1/(k(k+2)))                 (K1)
      khinchin_log    log K log 2 = zeta_F(0),  F(k) = -log(1 - 1/k) log(1 + 1/k)                      (K2)
      khinchin_dilog  log K log 2 = log^2 2 + Li2(-1/2) + (1/2) sum_{k>=2} (-1)^k Li2(4/k^2)            (K3)

    All three use the same machinery, so that their costs can be compared:
      - k-side series by binary splitting (engine bs_eval);
      - dual terms: moment systems built generically from theta-relations between kernel functions
        (tsys_t below), evaluated by the engine's bit-burst (dual_state); starting values by one binary
        splitting of the kernel coefficients times the incomplete-gamma recurrence (Kronecker product);
      - main terms by binary splitting.
    (K1) needs the derivative in s: on the k-side the derivative of Q(a, x) in a, on the dual side moments with
    a weight log u ("log functions"), and d/db Gamma(b, y) at b = 1/2 and b = 0.
*/
#include <math.h>
#include <string.h>
#include <stdlib.h>
#include <flint/fmpq_mat.h>
#include <flint/fmpq_vec.h>
#include "constants.h"

#define LOG2E 1.4426950408889634

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
static void kbs_eval(arb_ptr sums, arb_srcptr x0, slong a, slong b, const bs_t * B, slong prec)
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

#define KMAXO 96
#define KMAXR 8

typedef struct
{
    slong r;
    void (*leaf)(fmpz_mat_t M, fmpz_t q, slong n);      /* r x r, pre-zeroed */
    void (*init)(fmpq * g0);                            /* G_0 */
    void (*weight)(fmpq * w, int f, slong n);           /* length r, pre-zeroed */
}
coef_t;

/* One run of the Kronecker sums. The al-part and the be-part of Delta are independent recurrences and are
   summed separately: part 0 = (al) or (al, al'), part 1 = (be, T) or (be, be', T), part 2 = (T) alone. */
typedef struct
{
    const coef_t * co;
    int part, logs;         /* logs: include al', be' */
    slong h;                /* 2 ab */
    fmpz_t C, D;            /* c0 = C/D */
    slong nout;
    int of[KMAXO], od[KMAXO], ok[KMAXO];
}
kron_t;

static slong kron_dD(const kron_t * K) { return K->part == 2 ? 1 : (K->part == 0 ? 1 : 2) + (K->logs ? 1 : 0); }

/* one step of Delta: Delta_{n+1} = N(n) Delta_n (rational) */
static void delta_step(fmpq_mat_t N, const kron_t * K, slong n)
{
    fmpq_t c, u, i1, t, t2;
    fmpq_init(c); fmpq_init(u); fmpq_init(i1); fmpq_init(t); fmpq_init(t2);
    fmpq_mat_zero(N);
    fmpq_set_fmpz_frac(c, K->C, K->D);
    fmpq_set_fmpz_frac(u, U0_NUM, U0_DEN);
    fmpq_set_si(i1, 2, 2 * n + K->h + 2);                       /* 1/(a + 1) */
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
        fmpz_mul_ui(B->a + 1, c->q, 2 * c->ad * c->ad);
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
    fmpz_mul_ui(qq, c->q, n1 * n1 * n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), c->p, n1 * n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), c->p, n1 * n1); fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), c->p, n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 2), c->p, n1 * n1); fmpz_mul_ui(fmpz_mat_entry(T, 2, 1), c->p, 2 * n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), c->p, 2);
    fmpz_set(fmpz_mat_entry(T, 3, 1), qq);
    fmpz_set(fmpz_mat_entry(T, 4, 2), qq);
}

/* G = Gamma(b, y), dG = d/db Gamma(b, y) for b = 1/2 (half) or b = 0, y = p/q > 0; relative accuracy ~W */
static void dgamma_upper(arb_t G, arb_t dG, int half, const fmpz_t p, const fmpz_t q, slong W)
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
typedef struct { int f, k, p, num; } tterm_t;
typedef struct { int f, o, s; } tcomp_t;
typedef struct
{
    int nf, den, nterms, ncomp, twot0, R2;
    const tterm_t * terms;
    const tcomp_t * comps;
    const int * islog;
    const coef_t * co;
    arb_ptr fu0;                  /* f(u0), computed in setup */
    slong oidx[SYS_MAXD][4];      /* Kronecker output index per component and kind (al, be, al', be') */
    kron_t K[2];                  /* the al-run and the be-run (C, D filled per call) */
}
tsys_t;

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
    int d = T->ncomp, i, j, t;
    fmpz_t v; fmpz_init(v);
    for (i = 0; i < d; i++)
    {
        const tcomp_t * cp = T->comps + i;
        if (cp->o == 0)
        {
            fmpz_mul_si(v, D, T->den * (T->twot0 + 2 * l + 2 * cp->s - 2));
            fmpz_add(A + i * d + i, A + i * d + i, v);
            for (t = 0; t < T->nterms; t++)
            {
                const tterm_t * tm = T->terms + t;
                if (tm->f != cp->f) continue;
                j = tsys_find(T, tm->k, 0, cp->s - tm->p);
                if (j >= 0) { fmpz_mul_si(v, D, -2 * tm->num); fmpz_add(A + i * d + j, A + i * d + j, v); }
                else
                {
                    j = tsys_find(T, tm->k, -1, cp->s - tm->p);
                    if (j < 0) flint_abort();
                    fmpz_mul_si(v, C, -2 * tm->num); fmpz_add(A + i * d + j, A + i * d + j, v);
                }
            }
        }
        else
        {
            j = tsys_find(T, cp->f, 0, cp->s + 1);
            if (j >= 0) { fmpz_mul_si(v, D, 2 * T->den); fmpz_add(A + i * d + j, A + i * d + j, v); }
            else
            {
                j = tsys_find(T, cp->f, -1, cp->s + 1);
                if (j < 0) flint_abort();
                fmpz_mul_si(v, C, 2 * T->den); fmpz_add(A + i * d + j, A + i * d + j, v);
            }
        }
    }
    fmpz_clear(v);
}

/* the outputs needed for the starting values: per component (f, s), kinds al, be (+ al', be' for log f) */
static void tsys_outputs(tsys_t * T)
{
    int i, kind, part, haslog = 0;
    slong h = (T->twot0 % 2) ? -1 : 0;
    for (i = 0; i < T->nf; i++) if (T->islog[i]) haslog = 1;
    for (part = 0; part < 2; part++)
    {
        T->K[part].co = T->co; T->K[part].part = part; T->K[part].logs = haslog; T->K[part].h = h; T->K[part].nout = 0;
    }
    for (i = 0; i < T->ncomp; i++)
    {
        /* Z_{t0 + s}[f] = sum_j f_j D_{j - t0 - s + 1}, index n = j + delta, delta = 1 - t0 - s - h/2 */
        int delta = (2 - T->twot0 - 2 * T->comps[i].s - (int) h) / 2;
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
    int half = (T0->twot0 % 2) != 0;
    memcpy(&T, T0, sizeof(tsys_t));
    arb_init(c); arb_init(y); arb_init(Db); arb_init(dDb); arb_init(G); arb_init(dG); arb_init(Eu);
    arb_init(logc); arb_init(logu0); arb_init(t);
    fmpz_init(yq);
    sm = _arb_vec_init(T.K[0].nout + T.K[1].nout);
    arb_set_fmpz(c, C); arb_mul_2exp_si(c, c, -e);
    /* y = c/u0 = C ud/(un 2^e) */
    arb_mul_fmpz(y, c, U0_DEN, ARF_PREC_EXACT); arb_div_fmpz(y, y, U0_NUM, W);
    arb_neg(E, y); arb_exp(E, E, W);
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
    K.co = T->co; K.part = 2; K.logs = 0; K.h = 0; K.nout = T->nf;
    fmpz_init(K.C); fmpz_init(K.D); fmpz_one(K.D);
    for (i = 0; i < T->nf; i++) { K.of[i] = i; K.od[i] = 0; K.ok[i] = 0; }
    for (N = 1; ; N++) { l += log2(T->R2 * U0_D + 0.01) - log2((double) N) + 2; if (N > 10 && l < -prec - 64) break; }
    T->fu0 = _arb_vec_init(T->nf);
    kron_sums(T->fu0, &K, N + 1, prec + 64);
    fmpz_clear(K.C); fmpz_clear(K.D);
}

static void tsys_build(moment_sys_t * S, tsys_t * T, slong prec)
{
    int i, ng = 0;
    arb_t lu, t;
    arb_init(lu); arb_init(t);
    tsys_outputs(T);
    tsys_values(T, prec);
    arb_log(lu, U0, prec + 64);
    memset(S, 0, sizeof(*S));
    S->d = T->ncomp; S->t0 = T->twot0 / 2.0;
    S->amatc = tsys_amat; S->actx = T; S->aden = T->den; S->init = tsys_init; S->amat = NULL;
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
    arb_set_si(t, 2 - T->twot0); arb_mul_2exp_si(t, t, -1);
    arb_pow(S->f0scale, U0, t, prec + 64);
    arb_clear(lu); arb_clear(t);
}

static void tsys_clear(moment_sys_t * S, tsys_t * T)
{
    moment_sys_clear(S);
    _arb_vec_clear(T->fu0, T->nf);
}

/* ======================= common helpers ======================= */

static slong kd_prec(double size_log2, slong prec)  /* working precision for a term of size 2^size_log2 */
{
    return prec + (slong) size_log2 + 64;
}

/* number of terms of sum_m (c/K)^m (e^-x e_m(x)-like weights) to absolute 2^-prec */

static slong kseries_terms(double cK, double x, slong prec)
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
static slong fact_terms(double z, slong prec)
{
    double l = 0; slong m;
    for (m = 1; ; m++) { l += log2(z + 1e-9) - log2((double) m) + 1; if (m > 4 && l < -prec - 64) return m + 1; }
}

static void pi2c(arb_t c, double mm, slong prec)  /* c = pi^2 mm^2 with mm = m or m + 1/2 (exact in double) */
{
    arb_t t; arb_init(t);
    arb_set_d(t, mm);
    arb_const_pi(c, prec); arb_mul(c, c, t, prec); arb_sqr(c, c, prec);
    arb_clear(t);
}

/* ======================= (K3): the dilogarithm series =======================
   log K log 2 = log^2 2 + Li2(-1/2) + pi^2/12 + (1/2)(M + sum_{k>=3} (-1)^k I_k + sum_{m>=0} J_m),
   I_k = e^-x sum_n (4/K)^n e_n(x)/n^2, J_m = sqrt(pi) Z_{3/2}[Eip(4u)](pi^2 (m + 1/2)^2). */

/* coefficients: G_n = 4^n/n!; functions 0 = 1, 1 = e^{4u}, 2 = Eip(4u) */
static void c3_leaf(fmpz_mat_t M, fmpz_t q, slong n) { fmpz_set_ui(fmpz_mat_entry(M, 0, 0), 4); fmpz_set_ui(q, n + 1); }
static void c3_init(fmpq * g) { fmpq_one(g); }
static void c3_weight(fmpq * w, int f, slong n)
{
    if (f == 0) { if (n == 0) fmpq_one(w); }
    else if (f == 1) fmpq_one(w);
    else if (n >= 1) fmpq_set_si(w, 1, n);
}
static const coef_t CO3 = { 1, c3_leaf, c3_init, c3_weight };
static const tterm_t TT3[] = { {1, 1, 1, 4}, {2, 1, 0, 1}, {2, 0, 0, -1} };
static const tcomp_t TC3[] = { {2, 0, 0}, {1, 0, 0}, {1, -1, -1}, {0, 0, 0} };
static const int IL3[] = { 0, 0, 0 };
static tsys_t T3 = { 3, 1, 3, 4, 3, 4, TT3, TC3, IL3, &CO3 };
static moment_sys_t S3;
static arb_t K3_main;
static int K3_done = 0;

/* k-side: P_{n+1} = (4/K)(P_n + Q_n), Q_{n+1} = 4 u0 Q_n/(n+1), sum P_n/n^2 */
typedef struct { ulong K; } kctx;
static void k3_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * v)
{
    ulong K = ((const kctx *) v)->K, n2 = (ulong) n * n;
    fmpz_set_ui(q, K); fmpz_mul_ui(q, q, n2 * (n + 1)); fmpz_mul(q, q, U0_DEN);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_DEN, 4 * n2 * (n + 1));
    fmpz_set(fmpz_mat_entry(T, 0, 1), fmpz_mat_entry(T, 0, 0));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), U0_NUM, 4 * K * n2);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), U0_DEN, K * (n + 1));
}

/* main: S_a = sum_i (y^i/i!) W_i with W_i = sum_{n<=i} c^n/n^2: U' = (y/(i+1))U + (y c/(i+1)^3) V, V' = (y c/(i+1)) V */
typedef struct { fmpz_t yn, yd; ulong c; } uv_ctx;
static void uv_leaf(fmpz_mat_t T, fmpz_t q, slong i, const void * v)
{
    const uv_ctx * x = v; ulong i1 = i + 1;
    fmpz_mul_ui(q, x->yd, i1 * i1 * i1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), x->yn, i1 * i1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 1), x->yn, x->c);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), x->yn, x->c * i1 * i1);
    fmpz_set(fmpz_mat_entry(T, 2, 0), q);
}
/* t_n = (4u0)^n/n!, sum t_n/n^2 */
static void h4_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * v)
{
    fmpz_mul_ui(q, U0_DEN, (ulong) (n + 1) * n * n);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, 4 * (ulong) n * n);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), U0_DEN, n + 1);
}

static void K3_setup(slong prec)
{
    slong wp = prec + 64, N;
    arb_t Sa, Sb, Sc, t, y; arb_ptr x0 = _arb_vec_init(2), s = _arb_vec_init(1);
    bs_t B; uv_ctx U;
    if (K3_done) return;
    K3_done = 1;
    tsys_build(&S3, &T3, prec);
    arb_init(Sa); arb_init(Sb); arb_init(Sc); arb_init(t); arb_init(y);
    fmpz_init(U.yn); fmpz_init(U.yd);
    B.d = 2; B.s = 1; B.leaf = uv_leaf; B.ctx = &U;
    /* y = u0, c = 4 */
    fmpz_set(U.yn, U0_NUM); fmpz_set(U.yd, U0_DEN); U.c = 4;
    N = fact_terms(4 * U0_D * 4, wp) + 10;
    arb_mul_ui(x0, U0, 4, wp); arb_set(x0 + 1, x0);
    bs_eval(NULL, s, x0, 1, N, &B, wp);
    arb_neg(t, U0); arb_exp(t, t, wp); arb_mul(Sa, s, t, wp);
    /* y = 4 u0, c = 1 */
    fmpz_mul_ui(U.yn, U0_NUM, 4); U.c = 1;
    arb_mul_ui(x0, U0, 4, wp); arb_set(x0 + 1, x0);
    bs_eval(NULL, s, x0, 1, N, &B, wp);
    arb_mul_si(t, U0, -4, wp); arb_exp(t, t, wp); arb_mul(Sb, s, t, wp);
    /* sum (4u0)^n/(n^2 n!) */
    B.d = 1; B.s = 1; B.leaf = h4_leaf; B.ctx = NULL;
    arb_mul_ui(x0, U0, 4, wp);
    bs_eval(NULL, Sc, x0, 1, N, &B, wp);
    /* main = log^2 2 + Li2(-1/2) + pi^2/12 + M/2, M = Sa - Sb - Sc/2 */
    arb_init(K3_main);
    arb_mul_2exp_si(Sc, Sc, -1);
    arb_sub(K3_main, Sa, Sb, wp); arb_sub(K3_main, K3_main, Sc, wp); arb_mul_2exp_si(K3_main, K3_main, -1);
    arb_const_log2(t, wp); arb_sqr(t, t, wp); arb_add(K3_main, K3_main, t, wp);
    arb_set_si(y, -1); arb_mul_2exp_si(y, y, -1); arb_polylog_si(t, 2, y, wp); arb_add(K3_main, K3_main, t, wp);
    arb_const_pi(t, wp); arb_sqr(t, t, wp); arb_div_ui(t, t, 12, wp); arb_add(K3_main, K3_main, t, wp);
    _arb_vec_clear(x0, 2); _arb_vec_clear(s, 1);
    arb_clear(Sa); arb_clear(Sb); arb_clear(Sc); arb_clear(t); arb_clear(y);
    fmpz_clear(U.yn); fmpz_clear(U.yd);
}

static void K3_clear(void) { if (!K3_done) return; tsys_clear(&S3, &T3); arb_clear(K3_main); K3_done = 0; }

static void K3_k(arb_t res, slong idx, slong prec, void * ctx)
{
    ulong k = idx + 3, K = k * k;
    double x = K * U0_D;
    slong wp = kd_prec(-LOG2E * (K - 4.0) * U0_D, prec), N;
    kctx kc; bs_t B; arb_ptr x0 = _arb_vec_init(2); arb_t s, e;
    arb_zero(res);
    if (wp < 64) { _arb_vec_clear(x0, 2); return; }
    arb_init(s); arb_init(e);
    N = kseries_terms(4.0 / K, x, prec);
    kc.K = K; B.d = 2; B.s = 1; B.leaf = k3_leaf; B.ctx = &kc;
    arb_set_ui(x0, 4); arb_div_ui(x0, x0, K, wp); arb_mul_ui(x0 + 1, U0, 4, wp);
    bs_eval(NULL, s, x0, 1, N, &B, wp);
    arb_mul_ui(e, U0, K, ARF_PREC_EXACT); arb_neg(e, e); arb_exp(e, e, wp);
    arb_mul(res, s, e, wp);
    if (k % 2) arb_neg(res, res);
    arb_mul_2exp_si(res, res, -1);
    _arb_vec_clear(x0, 2); arb_clear(s); arb_clear(e);
}

static void K3_dual(arb_t res, slong idx, slong prec, void * ctx)
{
    double mm = idx + 0.5, cd = 9.8696044010893586 * mm * mm;
    slong wp = prec - (slong) (LOG2E * cd / U0_D) + 64;
    arb_t c, sp; arb_ptr V;
    arb_zero(res);
    if (wp < 64) return;
    V = _arb_vec_init(S3.d);
    arb_init(c); arb_init(sp);
    pi2c(c, mm, 2 * prec + 64);
    dual_state(V, &S3, c, wp);
    arb_const_sqrt_pi(sp, wp + 64);
    arb_mul(res, V + 0, sp, wp);
    arb_mul_2exp_si(res, res, -1);
    arb_clear(c); arb_clear(sp); _arb_vec_clear(V, S3.d);
}

static void K3_main_term(arb_t res) { arb_set(res, K3_main); }
static void Kfinish_loglog2(arb_t res, const arb_t lin, slong prec)
{
    arb_t t; arb_init(t);
    arb_const_log2(t, prec + 64); arb_div(res, lin, t, prec + 64); arb_exp(res, res, prec);
    arb_clear(t);
}
static slong K3_kcount(slong prec)
{
    slong k;
    for (k = 3; ; k++) if (LOG2E * ((double) k * k - 4) * U0_D > prec + 64) return k;
}
static slong K3_dcount(slong prec)
{
    slong m;
    for (m = 0; ; m++) if (LOG2E * 9.8696044010893586 * (m + 0.5) * (m + 0.5) / U0_D > prec + 64) return m + 1;
}

static void K_ref(arb_t res, slong prec, int threads) { arb_const_khinchin(res, prec + 32); }

const constant_t CONST_KHINCHIN_DILOG = { "khinchin_dilog",
    "Khinchin's constant from the dilogarithm series (K3)",
    K3_setup, K3_clear, K3_dual, K3_k, 3, Kfinish_loglog2, K3_main_term, K_ref, NULL, 2, K3_kcount, K3_dcount, NULL };

/* ======================= (K2): the logarithmic series =======================
   log K log 2 = sum_{k>=2} f(1/k), f(x) = -log(1-x) log(1+x) = sum_{N>=1} (A_N/N) x^(2N),
   kernel H(u) = sum_n h_n u^n, h_n = A_{n+1}/(n+1)!, theta^2(theta+1)(2theta+1)H - u(theta+1)(4theta^2+6theta+3)H
   + u^2(theta+1)(2theta+3)H = -u/2. */

static void c2_leaf(fmpz_mat_t M, fmpz_t q, slong n)
{
    if (n == 0)
    {
        fmpz_set_ui(fmpz_mat_entry(M, 0, 0), 5); fmpz_set_ui(fmpz_mat_entry(M, 1, 0), 12); fmpz_set_ui(q, 12);
        return;
    }
    fmpz_set_ui(q, (ulong) (n + 1) * (n + 1) * (n + 2) * (2 * n + 3));
    fmpz_set_ui(fmpz_mat_entry(M, 0, 0), (ulong) (n + 1) * (4 * n * n + 6 * n + 3));
    fmpz_set_si(fmpz_mat_entry(M, 0, 1), -(slong) n * (2 * n + 1));
    fmpz_set(fmpz_mat_entry(M, 1, 0), q);
}
static void c2_init(fmpq * g) { fmpq_one(g); fmpq_zero(g + 1); }
static void c2_weight_fix(fmpq * w, int f, slong n)
{
    if (f == 4) { if (n == 0) fmpq_one(w); return; }
    { fmpz_t p; fmpz_init(p); fmpz_set_ui(p, n); fmpz_pow_ui(p, p, f); fmpz_set(fmpq_numref(w), p); fmpz_one(fmpq_denref(w)); fmpz_clear(p); }
}
static const coef_t CO2 = { 2, c2_leaf, c2_init, c2_weight_fix };
/* G_i = theta^i H (i < 4), 4 = constant 1; den = 4 */
static const tterm_t TT2[] = {
    {0, 1, 0, 4}, {1, 2, 0, 4}, {2, 3, 0, 4},
    {3, 3, 0, -6}, {3, 2, 0, -2},
    {3, 3, 1, 8}, {3, 2, 1, 20}, {3, 1, 1, 18}, {3, 0, 1, 6},
    {3, 2, 2, -4}, {3, 1, 2, -10}, {3, 0, 2, -6},
    {3, 4, 1, -1} };
static const tcomp_t TC2[] = {
    {0, 0, 0}, {1, 0, 0}, {2, 0, 0}, {3, 0, 0},
    {0, -1, -1}, {1, -1, -1}, {2, -1, -1}, {3, -1, -1},
    {0, -1, -2}, {1, -1, -2}, {2, -1, -2},
    {4, 0, -1} };
static const int IL2[] = { 0, 0, 0, 0, 0 };
static tsys_t T2 = { 5, 4, 13, 12, 1, 1, TT2, TC2, IL2, &CO2 };
static moment_sys_t S2;
static arb_t K2_main;
static int K2_done = 0;

/* k-side: (P, Q, AP, AQ), P = e_N/K^N, Q = u0^N/N!, A = A_N, sum AP/N */
static void k2_leaf(fmpz_mat_t T, fmpz_t q, slong N, const void * v)
{
    ulong K = ((const kctx *) v)->K, D1 = 2 * (ulong) N * (2 * N + 1);
    fmpz_t a, b; fmpz_init(a); fmpz_init(b);
    fmpz_mul_ui(a, U0_DEN, (ulong) (N + 1) * D1 * N);            /* (N+1) ud D1 N */
    fmpz_mul_ui(b, U0_NUM, K * D1 * N);                           /* un K D1 N */
    fmpz_mul_ui(q, a, K);
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), a);
    fmpz_set(fmpz_mat_entry(T, 1, 1), b);
    fmpz_set(fmpz_mat_entry(T, 2, 2), a); fmpz_set(fmpz_mat_entry(T, 2, 3), a);
    fmpz_mul_si(fmpz_mat_entry(T, 2, 0), U0_DEN, -(slong) ((N + 1) * N));      /* A_{N+1} - A_N = -1/D1 */
    fmpz_set(fmpz_mat_entry(T, 2, 1), fmpz_mat_entry(T, 2, 0));
    fmpz_set(fmpz_mat_entry(T, 3, 3), b);
    fmpz_mul_si(fmpz_mat_entry(T, 3, 1), U0_NUM, -(slong) (K * N));
    fmpz_mul_ui(fmpz_mat_entry(T, 4, 2), U0_DEN, K * (N + 1) * D1);
    fmpz_clear(a); fmpz_clear(b);
}

/* main, L_1 = e^-u0 sum_{i>=1} t_i W_i: state (t, tA, tW) */
static void m2a_leaf(fmpz_mat_t T, fmpz_t q, slong i, const void * v)
{
    ulong i1 = i + 1, D1 = 2 * (ulong) i * (2 * i + 1);
    fmpz_mul_ui(q, U0_DEN, i1 * i1 * D1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, i1 * D1);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), U0_NUM, i1 * D1); fmpz_mul_si(fmpz_mat_entry(T, 1, 0), U0_NUM, -(slong) i1);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 2), U0_NUM, i1 * D1); fmpz_mul_ui(fmpz_mat_entry(T, 2, 1), U0_NUM, D1);
    fmpz_neg(fmpz_mat_entry(T, 2, 0), U0_NUM);
    fmpz_set(fmpz_mat_entry(T, 3, 2), q);
}
/* main, (r, Ar): r_n = u0^n/(n+1)!, Ar = A_{n+1} r_n; sums 2Ar/(2n+1), Ar/(n+1) */
static void m2b_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * v)
{
    ulong n1 = n + 1, D1 = 2 * n1 * (2 * n + 3), o = 2 * n + 1;
    fmpz_mul_ui(q, U0_DEN, (n + 2) * D1 * o * n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, D1 * o * n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), U0_NUM, D1 * o * n1);
    fmpz_mul_si(fmpz_mat_entry(T, 1, 0), U0_NUM, -(slong) (o * n1));
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 1), U0_DEN, 2 * (n + 2) * D1 * n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), U0_DEN, (n + 2) * D1 * o);
}

static void K2_setup(slong prec)
{
    slong wp = prec + 64, N;
    arb_t t, s1, sp; arb_ptr x0 = _arb_vec_init(3), s = _arb_vec_init(2);
    bs_t B;
    if (K2_done) return;
    K2_done = 1;
    tsys_build(&S2, &T2, prec);
    arb_init(t); arb_init(s1); arb_init(sp);
    N = fact_terms(U0_D, wp) + 10;
    B.d = 3; B.s = 1; B.leaf = m2a_leaf; B.ctx = NULL;
    arb_set(x0, U0); arb_set(x0 + 1, U0); arb_set(x0 + 2, U0);
    bs_eval(NULL, s, x0, 1, N, &B, wp);
    arb_neg(t, U0); arb_exp(t, t, wp); arb_mul(s1, s, t, wp);          /* L_1 */
    B.d = 2; B.s = 2; B.leaf = m2b_leaf;
    arb_one(x0); arb_one(x0 + 1);
    bs_eval(NULL, s, x0, 0, N, &B, wp);
    arb_init(K2_main);
    arb_const_sqrt_pi(sp, wp); arb_mul(sp, sp, SQRT_U0, wp); arb_mul_2exp_si(sp, sp, -1);
    arb_mul(K2_main, sp, s, wp);
    arb_mul(t, U0, s + 1, wp); arb_mul_2exp_si(t, t, -1); arb_sub(K2_main, K2_main, t, wp);
    arb_sub(K2_main, K2_main, s1, wp);
    _arb_vec_clear(x0, 3); _arb_vec_clear(s, 2); arb_clear(t); arb_clear(s1); arb_clear(sp);
}
static void K2_clear(void) { if (!K2_done) return; tsys_clear(&S2, &T2); arb_clear(K2_main); K2_done = 0; }

static void K2_k(arb_t res, slong idx, slong prec, void * ctx)
{
    ulong k = idx + 2, K = k * k;
    double x = K * U0_D;
    slong wp = kd_prec(-LOG2E * (K - 1.0) * U0_D, prec), N;
    kctx kc; bs_t B; arb_ptr x0 = _arb_vec_init(4); arb_t s, e;
    arb_zero(res);
    if (wp < 64) { _arb_vec_clear(x0, 4); return; }
    arb_init(s); arb_init(e);
    N = kseries_terms(1.0 / K, x, prec);
    kc.K = K; B.d = 4; B.s = 1; B.leaf = k2_leaf; B.ctx = &kc;
    arb_one(x0); arb_div_ui(x0, x0, K, wp); arb_set(x0 + 1, U0); arb_set(x0 + 2, x0); arb_set(x0 + 3, U0);
    bs_eval(NULL, s, x0, 1, N, &B, wp);
    arb_mul_ui(e, U0, K, ARF_PREC_EXACT); arb_neg(e, e); arb_exp(e, e, wp);
    arb_mul(res, s, e, wp);
    _arb_vec_clear(x0, 4); arb_clear(s); arb_clear(e);
}

static void K2_dual(arb_t res, slong idx, slong prec, void * ctx)
{
    slong m = idx + 1, wp = dual_term_prec(m, prec);
    arb_t c, sp; arb_ptr V;
    arb_zero(res);
    if (wp < 64) return;
    V = _arb_vec_init(S2.d);
    arb_init(c); arb_init(sp);
    pi2c(c, (double) m, 2 * prec + 64);
    dual_state(V, &S2, c, wp);
    arb_const_sqrt_pi(sp, wp + 64);
    arb_mul(res, V + 0, sp, wp);
    arb_clear(c); arb_clear(sp); _arb_vec_clear(V, S2.d);
}
static void K2_main_term(arb_t res) { arb_set(res, K2_main); }
static slong K2_kcount(slong prec)
{
    slong k;
    for (k = 2; ; k++) if (LOG2E * ((double) k * k - 1) * U0_D > prec + 64) return k;
}
static slong K12_dcount(slong prec)
{
    slong m;
    for (m = 1; ; m++) if (LOG2E * 9.8696044010893586 * m * m / U0_D > prec + 64) return m;
}

const constant_t CONST_KHINCHIN_LOG = { "khinchin_log",
    "Khinchin's constant from the logarithmic series (K2)",
    K2_setup, K2_clear, K2_dual, K2_k, 2, Kfinish_loglog2, K2_main_term, K_ref, NULL, 3, K2_kcount, K12_dcount, NULL };

/* ======================= (K1): the derivative of Z at 0 =======================
   log K = log(9/8) - L'(0)/log 2, L(s) = sum_{k>=3} f(1/k) k^-s, f(x) = 2 log(1+x) - log(1+2x),
   L'(0) = sum_{k>=3} I_k'(0) + sqrt(pi) sum_{m>=1} J_m'(0) + M'(0) (see the paper for the formulas). */

/* even dual system (t0 = 3/2): 0 = 1, 1 = e^{4u}, 2 = e^u, 3 = Eip(4u), 4 = Eip(u), 5 = e^{4u} Ein(4u),
   6 = e^u Ein(u), 7 = log e^{4u}, 8 = log e^u, 9 = log 1 */
static void c1e_leaf(fmpz_mat_t M, fmpz_t q, slong n)
{
    ulong n1 = n + 1;
    fmpz_set_ui(q, n1 * n1);
    fmpz_set_ui(fmpz_mat_entry(M, 0, 0), 4 * n1);
    fmpz_set_ui(fmpz_mat_entry(M, 1, 1), 4 * n1); fmpz_set_ui(fmpz_mat_entry(M, 1, 0), 4);
    fmpz_set_ui(fmpz_mat_entry(M, 2, 2), n1);
    fmpz_set_ui(fmpz_mat_entry(M, 3, 3), n1); fmpz_set_ui(fmpz_mat_entry(M, 3, 2), 1);
}
static void c1e_init(fmpq * g) { fmpq_one(g); fmpq_zero(g + 1); fmpq_one(g + 2); fmpq_zero(g + 3); }
static void c1e_weight(fmpq * w, int f, slong n)
{
    switch (f)
    {
        case 0: case 9: if (n == 0) fmpq_one(w); break;
        case 1: case 7: fmpq_one(w); break;
        case 2: case 8: fmpq_one(w + 2); break;
        case 3: if (n >= 1) fmpq_set_si(w, 1, n); break;
        case 4: if (n >= 1) fmpq_set_si(w + 2, 1, n); break;
        case 5: fmpq_one(w + 1); break;
        case 6: fmpq_one(w + 3); break;
    }
}
static const coef_t CO1E = { 4, c1e_leaf, c1e_init, c1e_weight };
static const tterm_t TT1E[] = {
    {1, 1, 1, 4}, {2, 2, 1, 1},
    {3, 1, 0, 1}, {3, 0, 0, -1}, {4, 2, 0, 1}, {4, 0, 0, -1},
    {5, 5, 1, 4}, {5, 1, 0, 1}, {5, 0, 0, -1}, {6, 6, 1, 1}, {6, 2, 0, 1}, {6, 0, 0, -1},
    {7, 1, 0, 1}, {7, 7, 1, 4}, {8, 2, 0, 1}, {8, 8, 1, 1},
    {9, 0, 0, 1} };
static const tcomp_t TC1E[] = {
    {0, 0, 0}, {1, 0, 0}, {1, -1, -1}, {2, 0, 0}, {2, -1, -1}, {3, 0, 0}, {4, 0, 0},
    {5, 0, 0}, {5, -1, -1}, {6, 0, 0}, {6, -1, -1}, {7, 0, 0}, {7, -1, -1}, {8, 0, 0}, {8, -1, -1}, {9, 0, 0} };
static const int IL1E[] = { 0, 0, 0, 0, 0, 0, 0, 1, 1, 1 };
static tsys_t T1E = { 10, 1, 17, 16, 3, 4, TT1E, TC1E, IL1E, &CO1E };

/* odd dual system (t0 = 1), scaled by sqrt(pi): 0 = 1, 1 = w(4u), 2 = w(u), 3 = s(4u), 4 = s(u), 5 = r(4u),
   6 = r(u), 7 = log w(4u), 8 = log w(u), 9 = log 1, with w(y) = sum y^m/(1/2)_(m+1), s(y) = sum_{m>=1}
   y^m/((2m-1)(1/2)_m), r(y) = sum O_m y^m/(1/2)_(m+1); den = 2 */
static void c1o_leaf(fmpz_mat_t M, fmpz_t q, slong m)
{
    ulong a = 2 * m + 1, b = 2 * m + 3;
    fmpz_set_ui(q, a * b);
    fmpz_set_ui(fmpz_mat_entry(M, 0, 0), 8 * a);
    fmpz_set_ui(fmpz_mat_entry(M, 1, 1), 8 * a); fmpz_set_ui(fmpz_mat_entry(M, 1, 0), 8);
    fmpz_set_ui(fmpz_mat_entry(M, 2, 2), 2 * a);
    fmpz_set_ui(fmpz_mat_entry(M, 3, 3), 2 * a); fmpz_set_ui(fmpz_mat_entry(M, 3, 2), 2);
}
static void c1o_init(fmpq * g) { fmpq_set_si(g, 2, 1); fmpq_zero(g + 1); fmpq_set_si(g + 2, 2, 1); fmpq_zero(g + 3); }
static void c1o_weight(fmpq * w, int f, slong n)
{
    switch (f)
    {
        case 0: case 9: if (n == 0) fmpq_set_si(w, 1, 2); break;
        case 1: case 7: fmpq_one(w); break;
        case 2: case 8: fmpq_one(w + 2); break;
        case 3: if (n >= 1) fmpq_set_si(w, 2 * n + 1, 2 * (2 * n - 1)); break;
        case 4: if (n >= 1) fmpq_set_si(w + 2, 2 * n + 1, 2 * (2 * n - 1)); break;
        case 5: fmpq_one(w + 1); break;
        case 6: fmpq_one(w + 3); break;
    }
}
static const coef_t CO1O = { 4, c1o_leaf, c1o_init, c1o_weight };
static const tterm_t TT1O[] = {
    {1, 1, 1, 8}, {1, 1, 0, -1}, {1, 0, 0, 2}, {2, 2, 1, 2}, {2, 2, 0, -1}, {2, 0, 0, 2},
    {3, 3, 0, 1}, {3, 1, 1, 4}, {4, 4, 0, 1}, {4, 2, 1, 1},
    {5, 5, 1, 8}, {5, 5, 0, -1}, {5, 3, 0, 2}, {6, 6, 1, 2}, {6, 6, 0, -1}, {6, 4, 0, 2},
    {7, 1, 0, 2}, {7, 7, 1, 8}, {7, 7, 0, -1}, {7, 9, 0, 2},
    {8, 2, 0, 2}, {8, 8, 1, 2}, {8, 8, 0, -1}, {8, 9, 0, 2},
    {9, 0, 0, 2} };
static const tcomp_t TC1O[] = {
    {0, 0, 0}, {1, 0, 0}, {1, -1, -1}, {2, 0, 0}, {2, -1, -1}, {3, 0, 0}, {4, 0, 0},
    {5, 0, 0}, {5, -1, -1}, {6, 0, 0}, {6, -1, -1}, {7, 0, 0}, {7, -1, -1}, {8, 0, 0}, {8, -1, -1}, {9, 0, 0} };
static const int IL1O[] = { 0, 0, 0, 0, 0, 0, 0, 1, 1, 1 };
static tsys_t T1O = { 10, 2, 25, 16, 2, 4, TT1O, TC1O, IL1O, &CO1O };

static moment_sys_t S1E, S1O;
static arb_t K1_main, K1_psih, K1_logu0, K1_euler;
static int K1_done = 0;

/* k-side even, per c: (P, Q, U, V), P = (c/K)^m e_m, Q = (c u0)^m/m!, U = (c/K)^m eh_m, V = (c u0)^m H_m/m!;
   sums P/m, U/m */
typedef struct { ulong K, c; } kcctx;
static void k1e_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    const kcctx * x = v; ulong m1 = m + 1;
    fmpz_t a, b; fmpz_init(a); fmpz_init(b);
    fmpz_mul_ui(a, U0_DEN, x->c * m1 * m1 * m);
    fmpz_mul_ui(b, U0_NUM, x->c * x->K * m1 * m);
    fmpz_mul_ui(q, U0_DEN, x->K * m1 * m1 * m);
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), a);
    fmpz_set(fmpz_mat_entry(T, 1, 1), b);
    fmpz_set(fmpz_mat_entry(T, 2, 2), a); fmpz_set(fmpz_mat_entry(T, 2, 3), a);
    fmpz_set(fmpz_mat_entry(T, 3, 3), b); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), U0_NUM, x->c * x->K * m);
    fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), U0_DEN, x->K * m1 * m1);
    fmpz_set(fmpz_mat_entry(T, 5, 2), fmpz_mat_entry(T, 4, 0));
    fmpz_clear(a); fmpz_clear(b);
}
/* k-side odd, per c: (P, rho, U, V); sums P/(2m+1), U/(2m+1) */
static void k1o_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    const kcctx * x = v; ulong b = 2 * m + 3, a = 2 * m + 1;
    fmpz_t A, B; fmpz_init(A); fmpz_init(B);
    fmpz_mul_ui(A, U0_DEN, x->c * b * b * a);
    fmpz_mul_ui(B, U0_NUM, 2 * x->c * x->K * b * a);
    fmpz_mul_ui(q, U0_DEN, x->K * b * b * a);
    fmpz_set(fmpz_mat_entry(T, 0, 0), A); fmpz_set(fmpz_mat_entry(T, 0, 1), A);
    fmpz_set(fmpz_mat_entry(T, 1, 1), B);
    fmpz_set(fmpz_mat_entry(T, 2, 2), A); fmpz_set(fmpz_mat_entry(T, 2, 3), A);
    fmpz_set(fmpz_mat_entry(T, 3, 3), B); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), U0_NUM, 2 * x->c * x->K * a);
    fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), U0_DEN, x->K * b * b);
    fmpz_set(fmpz_mat_entry(T, 5, 2), fmpz_mat_entry(T, 4, 0));
    fmpz_clear(A); fmpz_clear(B);
}

static void K1_k(arb_t res, slong idx, slong prec, void * ctx)
{
    ulong k = idx + 3, K = k * k, ci;
    double x = K * U0_D;
    slong wp = kd_prec(-LOG2E * (K - 4.0) * U0_D, prec), wa = prec + 64, N;
    kcctx kc; bs_t B;
    arb_ptr x0 = _arb_vec_init(4), s = _arb_vec_init(2);
    arb_t xa, ex, sx, E1, Gh, dGh, Qh, Bx, Se, So, logx, t, u, SP, SU, PO, UO, ev, od, sp;
    fmpz_t p, q;
    arb_zero(res);
    if (wp < 64) { _arb_vec_clear(x0, 4); _arb_vec_clear(s, 2); return; }
    arb_init(xa); arb_init(ex); arb_init(sx); arb_init(E1); arb_init(Gh); arb_init(dGh); arb_init(Qh); arb_init(Bx);
    arb_init(Se); arb_init(So); arb_init(logx); arb_init(t); arb_init(u);
    arb_init(SP); arb_init(SU); arb_init(PO); arb_init(UO); arb_init(ev); arb_init(od); arb_init(sp);
    fmpz_init(p); fmpz_init(q);
    arb_mul_ui(xa, U0, K, ARF_PREC_EXACT);
    arb_neg(ex, xa); arb_exp(ex, ex, wa);
    arb_sqrt(sx, xa, wa);
    arb_const_sqrt_pi(sp, wa);
    /* special functions at x */
    fmpz_mul_ui(p, U0_NUM, K); fmpz_set(q, U0_DEN);
    dgamma_upper(Gh, dGh, 1, p, q, wp + 20);
    gamma_upper_exact(E1, 0, xa, wp + 20);
    arb_div(Qh, Gh, sp, wa);
    arb_log(logx, xa, wa);
    /* B = dGamma(1/2,x)/sqrt(pi) - Q (psi(1/2) + log x) */
    arb_div(Bx, dGh, sp, wa);
    arb_add(t, K1_psih, logx, wa); arb_submul(Bx, Qh, t, wa);
    /* S_even = log(1 - 1/K) - log(1 - 4/K)/2, S_odd = k (2 atanh(1/k) - atanh(2/k)) */
    arb_set_ui(t, K - 1); arb_div_ui(t, t, K, wa); arb_log(Se, t, wa);
    arb_set_ui(t, K - 4); arb_div_ui(t, t, K, wa); arb_log(t, t, wa); arb_mul_2exp_si(t, t, -1); arb_sub(Se, Se, t, wa);
    arb_set_ui(t, 1); arb_div_ui(t, t, k, wa); arb_atanh(So, t, wa); arb_mul_2exp_si(So, So, 1);
    arb_set_ui(t, 2); arb_div_ui(t, t, k, wa); arb_atanh(t, t, wa); arb_sub(So, So, t, wa); arb_mul_ui(So, So, k, wa);
    /* even sums: a_{2m} = (1/2) 4^m/m - 1/m */
    kc.K = K; B.d = 4; B.s = 2; B.leaf = k1e_leaf; B.ctx = &kc;
    for (ci = 0; ci < 2; ci++)
    {
        ulong c = ci == 0 ? 4 : 1;
        kc.c = c;
        N = kseries_terms((double) c / K, x, prec);
        arb_set_ui(x0, c); arb_div_ui(x0, x0, K, wp); arb_mul_ui(x0 + 1, U0, c, wp); arb_zero(x0 + 2); arb_set(x0 + 3, x0 + 1);
        bs_eval(NULL, s, x0, 1, N, &B, wp);
        if (c == 4) { arb_mul_2exp_si(SP, s, -1); arb_mul_2exp_si(SU, s + 1, -1); }
        else { arb_sub(SP, SP, s, wp); arb_sub(SU, SU, s + 1, wp); }
    }
    /* even = e^-x [(log u0 + gamma)/2 SP - SU/2] + E1 S_even/2 */
    arb_add(t, K1_logu0, K1_euler, wa); arb_mul_2exp_si(t, t, -1);
    arb_mul(ev, t, SP, wp); arb_mul_2exp_si(u, SU, -1); arb_sub(ev, ev, u, wp); arb_mul(ev, ev, ex, wp);
    arb_mul(t, E1, Se, wp); arb_mul_2exp_si(t, t, -1); arb_add(ev, ev, t, wp);
    /* odd sums: a_{2m+1} = -2 4^m/(2m+1) + 2/(2m+1); R_m carries 1/Gamma(3/2) = 2/sqrt(pi) */
    B.leaf = k1o_leaf;
    for (ci = 0; ci < 2; ci++)
    {
        ulong c = ci == 0 ? 4 : 1;
        kc.c = c;
        N = kseries_terms((double) c / K, x, prec);
        arb_set_ui(x0, c); arb_div_ui(x0, x0, K, wp);
        arb_mul_ui(x0 + 1, U0, 2 * c, wp); arb_div_ui(x0 + 1, x0 + 1, 3, wp);
        arb_set(x0 + 2, x0);
        arb_mul_ui(x0 + 3, U0, 8 * c, wp); arb_div_ui(x0 + 3, x0 + 3, 9, wp);
        bs_eval(NULL, s, x0, 1, N, &B, wp);
        if (c == 4) { arb_mul_si(PO, s, -2, wp); arb_mul_si(UO, s + 1, -2, wp); }
        else { arb_addmul_ui(PO, s, 2, wp); arb_addmul_ui(UO, s + 1, 2, wp); }
    }
    arb_mul_2exp_si(PO, PO, 1); arb_div(PO, PO, sp, wp);      /* A_R */
    arb_mul_2exp_si(UO, UO, 1); arb_div(UO, UO, sp, wp);      /* A_RO */
    /* odd = (1/k)[ (log u0/2)(Q S_odd + e^-x sqrt(x) A_R) + B S_odd/2 - e^-x sqrt(x)(psi(1/2) A_R + 2 A_RO)/2 ] */
    arb_mul(t, ex, sx, wp);
    arb_mul(od, t, PO, wp); arb_addmul(od, Qh, So, wp); arb_mul(od, od, K1_logu0, wp); arb_mul_2exp_si(od, od, -1);
    arb_mul(u, Bx, So, wp); arb_mul_2exp_si(u, u, -1); arb_add(od, od, u, wp);
    arb_mul(u, K1_psih, PO, wp); arb_addmul_ui(u, UO, 2, wp); arb_mul(u, u, t, wp); arb_mul_2exp_si(u, u, -1);
    arb_sub(od, od, u, wp);
    arb_div_ui(od, od, k, wp);
    arb_add(res, ev, od, wp);
    _arb_vec_clear(x0, 4); _arb_vec_clear(s, 2);
    arb_clear(xa); arb_clear(ex); arb_clear(sx); arb_clear(E1); arb_clear(Gh); arb_clear(dGh); arb_clear(Qh); arb_clear(Bx);
    arb_clear(Se); arb_clear(So); arb_clear(logx); arb_clear(t); arb_clear(u);
    arb_clear(SP); arb_clear(SU); arb_clear(PO); arb_clear(UO); arb_clear(ev); arb_clear(od); arb_clear(sp);
    fmpz_clear(p); fmpz_clear(q);
}

/* dual term: J' = (1/2) Zlog[G0] + Z[dG0] + (1/sqrt(pi)) ((1/2) Zlog[G1^] + Z[dG1^]) at c = pi^2 m^2 */
static void K1_dual(arb_t res, slong idx, slong prec, void * ctx)
{
    slong m = idx + 1, wp = dual_term_prec(m, prec);
    arb_t c, sp, ev, od, t;
    arb_ptr Ve, Vo;
    arb_zero(res);
    if (wp < 64) return;
    Ve = _arb_vec_init(S1E.d); Vo = _arb_vec_init(S1O.d);
    arb_init(c); arb_init(sp); arb_init(ev); arb_init(od); arb_init(t);
    pi2c(c, (double) m, 2 * prec + 64);
    dual_state(Ve, &S1E, c, wp);
    dual_state(Vo, &S1O, c, wp);
    /* even components: 0 C, 1 Y4, 3 Y1, 5 E4, 6 E1, 7 Phi4, 9 Phi1, 11 LY4, 13 LY1, 15 L1 */
    /* (1/2) Zlog[G0] = (1/2)((1/2) LY4 - LY1 + (1/2) L1) */
    arb_add(ev, Ve + 11, Ve + 15, wp); arb_mul_2exp_si(ev, ev, -1); arb_sub(ev, ev, Ve + 13, wp);
    arb_mul_2exp_si(ev, ev, -1);
    /* Z[dG0] = -(1/4)[(Phi4 - E4) - 2(Phi1 - E1) - gamma (Y4 - 2 Y1 + C)] */
    arb_sub(t, Ve + 7, Ve + 5, wp);
    arb_submul_ui(t, Ve + 9, 2, wp); arb_addmul_ui(t, Ve + 6, 2, wp);
    {
        arb_t g; arb_init(g);
        arb_set(g, Ve + 1); arb_submul_ui(g, Ve + 3, 2, wp); arb_add(g, g, Ve + 0, wp);
        arb_submul(t, K1_euler, g, wp);
        arb_clear(g);
    }
    arb_mul_2exp_si(t, t, -2); arb_sub(ev, ev, t, wp);
    /* odd components: 1 w4, 3 w1, 7 r4, 9 r1, 11 Lw4, 13 Lw1 */
    /* (1/2) Zlog[G1^] = -(1/2)(Lw4 - Lw1); Z[dG1^] = (1/2) psi(1/2)(w4 - w1) + (r4 - r1) */
    arb_sub(od, Vo + 13, Vo + 11, wp); arb_mul_2exp_si(od, od, -1);
    arb_sub(t, Vo + 1, Vo + 3, wp); arb_mul(t, t, K1_psih, wp); arb_mul_2exp_si(t, t, -1); arb_add(od, od, t, wp);
    arb_add(od, od, Vo + 7, wp); arb_sub(od, od, Vo + 9, wp);
    arb_const_sqrt_pi(sp, wp + 64);
    arb_div(od, od, sp, wp);
    arb_add(res, ev, od, wp);
    arb_mul(res, res, sp, wp);
    _arb_vec_clear(Ve, S1E.d); _arb_vec_clear(Vo, S1O.d);
    arb_clear(c); arb_clear(sp); arb_clear(ev); arb_clear(od); arb_clear(t);
}

/* main term pieces */
typedef struct { ulong c; slong k2; } mctx;
/* even n = 2m, per c: (b, bH), b = (c u0)^m/m!; sums b/(2m-1), b/(2m-1)^2, (bH - b/m)/(2m-1), b/m, bH/m */
static void m1e_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    ulong c = ((const mctx *) v)->c, m1 = m + 1, o = 2 * m - 1;
    fmpz_t Q; fmpz_init(Q);
    fmpz_mul_ui(Q, U0_DEN, m1 * m1 * m * o * o);
    fmpz_set(q, Q);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, c * m1 * m * o * o);
    fmpz_set(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 0, 0));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), U0_NUM, c * m * o * o);
    fmpz_divexact_ui(fmpz_mat_entry(T, 2, 0), Q, o);
    fmpz_divexact_ui(fmpz_mat_entry(T, 3, 0), Q, o * o);
    fmpz_divexact_ui(fmpz_mat_entry(T, 4, 1), Q, o);
    fmpz_divexact_ui(fmpz_mat_entry(T, 4, 0), Q, m * o); fmpz_neg(fmpz_mat_entry(T, 4, 0), fmpz_mat_entry(T, 4, 0));
    fmpz_divexact_ui(fmpz_mat_entry(T, 5, 0), Q, m);
    fmpz_divexact_ui(fmpz_mat_entry(T, 6, 1), Q, m);
    fmpz_clear(Q);
}
/* odd n = 2m+1, per c: (be, beO), be = (c u0)^m/(1/2)_m, O = O_m;
   sums be/(m(2m+1)), be/(m^2(2m+1)), beO/(m(2m+1)), 2be/(2m+1)^2, 2(beO + be/(2m+1))/(2m+1)^2 */
static void m1o_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    ulong c = ((const mctx *) v)->c, a = 2 * m + 1, m2 = (ulong) m * m;
    fmpz_t Q; fmpz_init(Q);
    fmpz_mul_ui(Q, U0_DEN, a * a * a * m2);
    fmpz_set(q, Q);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, 2 * c * a * a * m2);
    fmpz_set(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 0, 0));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), U0_NUM, 2 * c * a * m2);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), U0_DEN, a * a * m);
    fmpz_mul_ui(fmpz_mat_entry(T, 3, 0), U0_DEN, a * a);
    fmpz_mul_ui(fmpz_mat_entry(T, 4, 1), U0_DEN, a * a * m);
    fmpz_mul_ui(fmpz_mat_entry(T, 5, 0), U0_DEN, 2 * a * m2);
    fmpz_mul_ui(fmpz_mat_entry(T, 6, 1), U0_DEN, 2 * a * m2);
    fmpz_mul_ui(fmpz_mat_entry(T, 6, 0), U0_DEN, 2 * m2);
    fmpz_clear(Q);
}
/* L_k, even n = 2j: (wS, wSH, w4, w4H, w1, w1H), w = u0^j/j!; sums wS, wSH */
static void l1e_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    ulong k2 = ((const mctx *) v)->k2, j1 = j + 1;
    fmpz_mul_ui(q, U0_DEN, j1 * j1 * j1);
#define E(r, c, val) fmpz_mul_si(fmpz_mat_entry(T, r, c), U0_NUM, (slong) (val))
    E(0, 0, k2 * j1 * j1); E(0, 2, 2 * j1); E(0, 4, -(slong) j1);
    E(1, 1, k2 * j1 * j1); E(1, 0, k2 * j1); E(1, 3, 2 * j1); E(1, 5, -(slong) j1); E(1, 2, 2); E(1, 4, -1);
    E(2, 2, 4 * j1 * j1); E(3, 3, 4 * j1 * j1); E(3, 2, 4 * j1);
    E(4, 4, j1 * j1); E(5, 5, j1 * j1); E(5, 4, j1);
#undef E
    fmpz_set(fmpz_mat_entry(T, 6, 0), q);
    fmpz_set(fmpz_mat_entry(T, 7, 1), q);
}
/* L_k, odd n = 2j+1: (wS, wSO, w4, w4O, w1, w1O), w = u0^j/(1/2)_(j+1), O = O_{j+1}; sums wS, wSO */
static void l1o_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    ulong k2 = ((const mctx *) v)->k2, b = 2 * j + 3;
    fmpz_mul_ui(q, U0_DEN, b * b * b);
#define E(r, c, val) fmpz_mul_si(fmpz_mat_entry(T, r, c), U0_NUM, (slong) (val))
    E(0, 0, 2 * k2 * b * b); E(0, 2, -16 * (slong) b); E(0, 4, 4 * b);
    E(1, 1, 2 * k2 * b * b); E(1, 0, 2 * k2 * b); E(1, 3, -16 * (slong) b); E(1, 5, 4 * b); E(1, 2, -16); E(1, 4, 4);
    E(2, 2, 8 * b * b); E(3, 3, 8 * b * b); E(3, 2, 8 * b);
    E(4, 4, 2 * b * b); E(5, 5, 2 * b * b); E(5, 4, 2 * b);
#undef E
    fmpz_set(fmpz_mat_entry(T, 6, 0), q);
    fmpz_set(fmpz_mat_entry(T, 7, 1), q);
}

static void K1_setup(slong prec)
{
    slong wp = prec + 64, N, i;
    arb_t t, u, h, sp, su, SE, SO, Lk, Dk, ex, z;
    arb_ptr x0 = _arb_vec_init(6), s = _arb_vec_init(5);
    bs_t B; mctx mc;
    if (K1_done) return;
    K1_done = 1;
    arb_init(K1_psih); arb_init(K1_logu0); arb_init(K1_euler); arb_init(K1_main);
    arb_const_euler(K1_euler, wp);
    arb_const_log2(K1_psih, wp); arb_mul_2exp_si(K1_psih, K1_psih, 1); arb_add(K1_psih, K1_psih, K1_euler, wp); arb_neg(K1_psih, K1_psih);
    arb_log(K1_logu0, U0, wp);
    tsys_build(&S1E, &T1E, prec);
    tsys_build(&S1O, &T1O, prec);
    arb_init(t); arb_init(u); arb_init(h); arb_init(sp); arb_init(su); arb_init(SE); arb_init(SO);
    arb_init(Lk); arb_init(Dk); arb_init(ex); arb_init(z);
    arb_const_sqrt_pi(sp, wp);
    arb_mul(su, sp, SQRT_U0, wp);                 /* sqrt(pi u0) */
    N = fact_terms(4 * U0_D, wp) + 10;
    /* (1/2)(log u0 + gamma) */
    arb_add(h, K1_logu0, K1_euler, wp); arb_mul_2exp_si(h, h, -1);
    /* even: sum_c w_c { sqrt(pi/u0) [h E1 - E2 - E3/2] - (1/2)[h E4 - E5/2] }, w_4 = 1/2, w_1 = -1 */
    B.d = 2; B.s = 5; B.leaf = m1e_leaf; B.ctx = &mc;
    for (i = 0; i < 2; i++)
    {
        mc.c = i == 0 ? 4 : 1;
        arb_mul_ui(x0, U0, mc.c, wp); arb_set(x0 + 1, x0);
        bs_eval(NULL, s, x0, 1, N, &B, wp);
        arb_mul(t, h, s + 0, wp); arb_sub(t, t, s + 1, wp); arb_mul_2exp_si(u, s + 2, -1); arb_sub(t, t, u, wp);
        arb_div(t, t, SQRT_U0, wp); arb_mul(t, t, sp, wp);
        arb_mul(u, h, s + 3, wp); arb_mul_2exp_si(z, s + 4, -1); arb_sub(u, u, z, wp); arb_mul_2exp_si(u, u, -1);
        arb_sub(t, t, u, wp);
        if (i == 0) arb_mul_2exp_si(SE, t, -1); else arb_sub(SE, SE, t, wp);
    }
    /* odd: sum_c v_c { -[g O1 - O2/2 - O3] + sqrt(u0/pi)[g O4 - O5] }, g = (log u0 - psi(1/2))/2, v = +1, -1 */
    arb_sub(h, K1_logu0, K1_psih, wp); arb_mul_2exp_si(h, h, -1);
    B.leaf = m1o_leaf;
    for (i = 0; i < 2; i++)
    {
        mc.c = i == 0 ? 4 : 1;
        arb_mul_ui(x0, U0, 2 * mc.c, wp); arb_set(x0 + 1, x0);
        bs_eval(NULL, s, x0, 1, N, &B, wp);
        arb_mul(t, h, s + 0, wp); arb_mul_2exp_si(u, s + 1, -1); arb_sub(t, t, u, wp); arb_sub(t, t, s + 2, wp);
        arb_neg(t, t);
        arb_mul(u, h, s + 3, wp); arb_sub(u, u, s + 4, wp); arb_mul(u, u, SQRT_U0, wp); arb_div(u, u, sp, wp);
        arb_add(t, t, u, wp);
        if (i == 0) arb_set(SO, t); else arb_sub(SO, SO, t, wp);
    }
    arb_add(K1_main, SE, SO, wp);
    /* L_k'(0) = (log u0/2) L_k(0) - e^-x D_k/2, k = 1, 2 */
    for (i = 1; i <= 2; i++)
    {
        mc.k2 = i * i;
        B.d = 6; B.s = 2; B.leaf = l1e_leaf;
        _arb_vec_zero(x0, 6); arb_one(x0 + 2); arb_one(x0 + 4);
        bs_eval(NULL, s, x0, 0, N, &B, wp);
        arb_set(Lk, s); arb_set(Dk, s + 1); arb_submul(Dk, K1_euler, s, wp);
        B.leaf = l1o_leaf;
        _arb_vec_zero(x0, 6); arb_set_ui(x0 + 2, 2); arb_set_ui(x0 + 3, 2); arb_set_ui(x0 + 4, 2); arb_set_ui(x0 + 5, 2);
        bs_eval(NULL, s, x0, 0, N, &B, wp);
        arb_mul(z, SQRT_U0, s, wp); arb_div(z, z, sp, wp); arb_add(Lk, Lk, z, wp);
        arb_mul(t, K1_psih, s, wp); arb_addmul_ui(t, s + 1, 2, wp); arb_mul(t, t, SQRT_U0, wp); arb_div(t, t, sp, wp);
        arb_add(Dk, Dk, t, wp);
        arb_mul_ui(ex, U0, i * i, wp); arb_neg(ex, ex); arb_exp(ex, ex, wp);
        arb_mul(Lk, Lk, ex, wp); arb_mul(Dk, Dk, ex, wp);
        arb_mul(t, K1_logu0, Lk, wp); arb_sub(t, t, Dk, wp); arb_mul_2exp_si(t, t, -1);
        arb_sub(K1_main, K1_main, t, wp);
    }
    _arb_vec_clear(x0, 6); _arb_vec_clear(s, 5);
    arb_clear(t); arb_clear(u); arb_clear(h); arb_clear(sp); arb_clear(su); arb_clear(SE); arb_clear(SO);
    arb_clear(Lk); arb_clear(Dk); arb_clear(ex); arb_clear(z);
}
static void K1_clear(void)
{
    if (!K1_done) return;
    tsys_clear(&S1E, &T1E); tsys_clear(&S1O, &T1O);
    arb_clear(K1_main); arb_clear(K1_psih); arb_clear(K1_logu0); arb_clear(K1_euler);
    K1_done = 0;
}
static void K1_main_term(arb_t res) { arb_set(res, K1_main); }
static void K1_finish(arb_t res, const arb_t lin, slong prec)
{
    arb_t t; arb_init(t);
    arb_const_log2(t, prec + 64); arb_div(res, lin, t, prec + 64);
    arb_set_ui(t, 9); arb_div_ui(t, t, 8, prec + 64); arb_log(t, t, prec + 64);
    arb_sub(res, t, res, prec + 64); arb_exp(res, res, prec);
    arb_clear(t);
}
static slong K1_kcount(slong prec)
{
    slong k;
    for (k = 3; ; k++) if (LOG2E * ((double) k * k - 4) * U0_D > prec + 64) return k;
}

const constant_t CONST_KHINCHIN_Z = { "khinchin_Z",
    "Khinchin's constant from -Z'(0), the derivative of the Khinchin zeta function (K1)",
    K1_setup, K1_clear, K1_dual, K1_k, 3, K1_finish, K1_main_term, K_ref, NULL, 2, K1_kcount, K12_dcount, NULL };
