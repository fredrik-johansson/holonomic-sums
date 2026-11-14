/*
    Somos's quadratic recurrence constant sigma = prod_{k>=1} k^(1/2^k) = 1.6616879496... (OEIS A112302),

        log sigma = sum_{k>=1} 2^-k log k = -d/ds Li_s(1/2) at s = 0,

    by the geometric-factor splitting (Theorem "geometric" of the paper) with F = 1, z = 1/2 = e^(2 pi i alpha),
    alpha = i y_a, y_a = log(2)/(2 pi), differentiated in s at s = 0. With x = k^2 u0, C_k = (2^-k + 2^k)/2,
    S_k = (2^-k - 2^k)/2 and c_n = pi^2 (n - i y_a)^2, y_n = c_n/u0:

        -log sigma = sum_{k>=1} [C_k E1(x)/2 + S_k B_k] + (sqrt(pi)/2) Re T_0 + sqrt(pi) sum_{n>=1} Re T_n
                     - (log u0 + gamma)/4,

    where B_k = -log k Q(1/2, x) + (1/2) dQ/da(1/2, x) and T_n = J0'(c_n) - i pi (n - i y_a) J1'(c_n), with
    J0' = Gamma(1/2, y)/(2 sqrt c), J1' = (e^-y (log u0 - psi(1/2)) - E1(y))/(2 sqrt(pi) c) (the s-derivatives of
    Crandall's dual functions); c_0 = -log(2)^2/4 lies on the branch cut and only the real part, which is the same
    from either side, is needed.

    k-side. With the lower series sums St = sum_n x^n/(1/2)_(n+1), Su = sum_n x^n H_n/(1/2)_(n+1)
    (H_n = sum_{i<=n} 1/(i+1/2)) and Sp = sum_{n>=1} x^n H'_n/n! (H'_n harmonic numbers),
        E1(x) = -gamma - 2 log k - log u0 + e^-x Sp,
        B_k   = -log k + sqrt(x) e^-x (Su - (log u0 + gamma + 2 log 2) St)/(2 sqrt(pi)),
    so that each k-term costs two rational series (binary splitting) and log k, which is assembled from the
    logarithms of the primes below the cutoff (computed once, in parallel). The pieces of size 2^k cancel to
    2^k e^-x, which costs k guard bits.

    Dual side. With V_a(y) = e^y y^-a Gamma(a, y), which satisfies y V' = (y - a) V - 1,
        T_n = e^-y/(2 sqrt u0) [V_{1/2}(y) - i sqrt(u0/pi) (log u0 + gamma + 2 log 2 - V_0(y))/(pi n - i log(2)/2)],
    and V_a at the complex point y_n is computed by the bit-burst algorithm from a real starting point, where
    V_a is an incomplete gamma function at an exact dyadic argument. T_0 is real-analytic: it needs erfi and Ei at
    log(2)/sqrt(u0) and log(2)^2/(4 u0), one evaluation each (FLINT).

    Reference (--method direct): log sigma = sum_{p prime} log p sum_{e>=1} 1/(2^(p^e) - 1).
*/
#include <math.h>
#include <stdlib.h>
#include <flint/acb.h>
#include <flint/ulong_extras.h>
#include "constants.h"

#define LOG2E 1.4426950408889634

static slong S_kmax, S_lprec;
static arb_t S_log2, S_euler, S_sqrtpi, S_logu0, S_L0, S_main;
static arb_ptr S_logp;
static slong * S_pidx;       /* S_pidx[p] = index of the prime p, for p <= S_kmax */

/* ======================= logarithms of primes ======================= */

/* log p = atanh(1/(2p^2 - 1)) + (log((p-1)/2) + log((p+1)/2))/2 + log 2, p >= 3 */
typedef struct { const ulong * pr; arb_ptr A; slong prec; } lp_ctx;

static void lp_block(slong i, void * vctx)
{
    lp_ctx * c = vctx;
    fmpz_t p, q;
    if (c->pr[i] == 2) return;
    fmpz_init(p); fmpz_init(q);
    fmpz_one(p); fmpz_set_ui(q, c->pr[i]); fmpz_mul_ui(q, q, c->pr[i]); fmpz_mul_2exp(q, q, 1); fmpz_sub_ui(q, q, 1);
    arb_atan_frac_bsplit(c->A + i, p, q, 1, c->prec);
    fmpz_clear(p); fmpz_clear(q);
}

static void add_log_of(arb_t s, ulong m, arb_srcptr logp, const slong * idx, slong prec)
{
    n_factor_t f;
    slong j;
    if (m <= 1) return;
    n_factor_init(&f);
    n_factor(&f, m, 1);
    for (j = 0; j < f.num; j++)
        arb_addmul_ui(s, logp + idx[f.p[j]], f.exp[j], prec);
}

/* logp[i] = log(primes[i]) for all primes up to N; idx (size N + 1) receives the prime indices */
static slong log_primes(arb_ptr * logp, ulong ** primes, slong ** idx, ulong N, slong prec, int threads)
{
    slong n = 0, i;
    ulong p;
    n_primes_t it;
    lp_ctx c;
    arb_t l2;
    *idx = flint_malloc(sizeof(slong) * (N + 2));
    *primes = flint_malloc(sizeof(ulong) * (N / 2 + 8));
    n_primes_init(it);
    while ((p = n_primes_next(it)) <= N) { (*idx)[p] = n; (*primes)[n++] = p; }
    n_primes_clear(it);
    *logp = _arb_vec_init(FLINT_MAX(n, 1));
    c.pr = *primes; c.A = *logp; c.prec = prec + 32;
    parallel_for(n, lp_block, &c, threads);
    arb_init(l2);
    arb_const_log2(l2, prec + 32);
    for (i = 0; i < n; i++)
    {
        p = (*primes)[i];
        if (p == 2) { arb_set(*logp + i, l2); continue; }
        /* the atanh value is in logp[i]; the factors of (p +- 1)/2 are smaller primes */
        {
            arb_t s;
            arb_init(s);
            add_log_of(s, (p - 1) / 2, *logp, *idx, prec + 32);
            add_log_of(s, (p + 1) / 2, *logp, *idx, prec + 32);
            arb_mul_2exp_si(s, s, -1);
            arb_add(s, s, *logp + i, prec + 32);
            arb_add(*logp + i, s, l2, prec);
            arb_clear(s);
        }
    }
    arb_clear(l2);
    return n;
}

/* ======================= counts ======================= */

static slong somos_k_count(slong prec)
{
    slong k;
    for (k = 1; ; k++)
        if (k > 8 && (double) k * k * U0_D * LOG2E - k > prec + 64) return k;
}

static slong somos_dual_count(slong prec)
{
    slong n;
    double t2 = 0.0600566;          /* log(2)^2/8 rounded up: |c_0| = log(2)^2/4 */
    for (n = 1; ; n++)
        if ((9.8696044010893586 * n * n - 2 * t2) / U0_D * LOG2E > prec + 64) return n;
}

/* ======================= k-side ======================= */

typedef struct { ulong P; } klow_ctx;

/* (t_n, u_n) -> (t_{n+1}, u_{n+1}): t_n = x^n/(1/2)_(n+1), u_n = t_n H_n; x = P/ud; sums t_n, u_n */
static void half_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * vctx)
{
    ulong P = ((const klow_ctx *) vctx)->P;
    fmpz_set_ui(q, 2 * n + 3); fmpz_mul_ui(q, q, 2 * n + 3); fmpz_mul(q, q, U0_DEN);
    fmpz_set_ui(fmpz_mat_entry(T, 0, 0), 2 * P); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), 2 * n + 3);
    fmpz_set_ui(fmpz_mat_entry(T, 1, 0), 4 * P);
    fmpz_set(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 0, 0));
    fmpz_set(fmpz_mat_entry(T, 2, 0), q);
    fmpz_set(fmpz_mat_entry(T, 3, 1), q);
}

/* (t_n, u_n) -> next: t_n = x^n/n!, u_n = t_n H'_n; sum u_n */
static void ein_leaf2(fmpz_mat_t T, fmpz_t q, slong n, const void * vctx)
{
    ulong P = ((const klow_ctx *) vctx)->P;
    fmpz_set_ui(q, n + 1); fmpz_mul_ui(q, q, n + 1); fmpz_mul(q, q, U0_DEN);
    fmpz_set_ui(fmpz_mat_entry(T, 0, 0), P); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), n + 1);
    fmpz_set_ui(fmpz_mat_entry(T, 1, 0), P);
    fmpz_set(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 0, 0));
    fmpz_set(fmpz_mat_entry(T, 2, 1), q);
}

/* number of terms of a lower series with log2 |t_n| = l0 + sum (log2 x - log2(n + sh)) until below
   log2(e^x) - W */
static slong lower_len(double x, double sh, double l0, slong n0, slong W)
{
    double l = l0;
    slong n = n0;
    for (;;)
    {
        n++;
        l += log2(x) - log2(n + sh);
        if (n > x && l + log2((double) n) < x * LOG2E - W - 20) return n + 1;
    }
}


/* Legendre's continued fraction for Gamma(a, x), x = P/qd, a = an/ad, scaled as in engine.c (gamma_cfa):
   Gamma(a, x) = e^-x x^a 2 qd ad / X. With jet != 0 also dX = dX/da (forward mode: the leaf is the block
   matrix [[M, M'], [0, M]], M' = d M/da); the value is enclosed by consecutive convergents, the derivative is
   given the difference of the two derivative convergents as (heuristic) error. Returns 1 on success. */
typedef struct { slong an, ad; ulong P; int jet; } cfj_ctx;

static void cfj_leaf(fmpz_mat_t T, fmpz_t qq, slong n, const void * vctx)
{
    const cfj_ctx * c = vctx;
    int b;
    for (b = 0; b < (c->jet ? 2 : 1); b++)
    {
        slong o = 2 * b;
        if (n % 2 == 0) { fmpz_set_ui(fmpz_mat_entry(T, o, o), c->P); fmpz_mul_ui(fmpz_mat_entry(T, o, o), fmpz_mat_entry(T, o, o), 2 * c->ad); }
        else fmpz_set_ui(fmpz_mat_entry(T, o, o), 2 * c->ad);
        if (n % 2 == 1)
        {
            fmpz_mul_ui(fmpz_mat_entry(T, o, o + 1), U0_DEN, 2 * c->ad);
            fmpz_mul_si(fmpz_mat_entry(T, o, o + 1), fmpz_mat_entry(T, o, o + 1), (n + 1) * c->ad - 2 * c->an);
        }
        else
        {
            fmpz_mul_ui(fmpz_mat_entry(T, o, o + 1), U0_DEN, 2 * c->ad * c->ad);
            fmpz_mul_ui(fmpz_mat_entry(T, o, o + 1), fmpz_mat_entry(T, o, o + 1), n);
        }
        fmpz_one(fmpz_mat_entry(T, o + 1, o));
    }
    if (c->jet && n % 2 == 1)
        fmpz_mul_si(fmpz_mat_entry(T, 0, 3), U0_DEN, -4 * c->ad * c->ad);
    fmpz_one(qq);
}


/* the jet product [[A, D], [0, A]] of the continued fraction with 2x2 blocks: 3 block products per merge */
typedef struct { fmpz a[4], d[4]; } jblk;
typedef struct { arb_struct a[4], d[4]; } ajblk;

static void jblk_init(jblk * B) { int i; for (i = 0; i < 4; i++) { fmpz_init(B->a + i); fmpz_init(B->d + i); } }
static void jblk_clear(jblk * B) { int i; for (i = 0; i < 4; i++) { fmpz_clear(B->a + i); fmpz_clear(B->d + i); } }

static void m2mul(fmpz * R, const fmpz * X, const fmpz * Y)       /* R = X Y, 2x2, R not aliased */
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
    fmpz_mat_t T; fmpz_t q; int i;
    fmpz_mat_init(T, 4, 4); fmpz_init(q);
    cfj_leaf(T, q, n, c);
    for (i = 0; i < 4; i++)
    {
        fmpz_set(B->a + i, fmpz_mat_entry(T, i / 2, i % 2));
        fmpz_set(B->d + i, fmpz_mat_entry(T, i / 2, 2 + i % 2));
    }
    fmpz_mat_clear(T); fmpz_clear(q);
}

static void jbs(jblk * R, slong a, slong b, const cfj_ctx * c)
{
    jblk L, U;
    slong m;
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
    int i, j;
    arb_t t; arb_init(t);
    for (i = 0; i < 2; i++)
        for (j = 0; j < 2; j++)
        {
            arb_mul(t, X + 2 * i, Y + j, prec);
            arb_addmul(t, X + 2 * i + 1, Y + 2 + j, prec);
            if (add) arb_add(R + 2 * i + j, R + 2 * i + j, t, prec); else arb_swap(R + 2 * i + j, t);
        }
    arb_clear(t);
}

static void ajbs(arb_ptr A, arb_ptr D, slong a, slong b, slong lim, const cfj_ctx * c, slong prec)
{
    if (b - a <= lim)
    {
        jblk G; int i;
        jblk_init(&G);
        jbs(&G, a, b, c);
        for (i = 0; i < 4; i++) { arb_set_round_fmpz(A + i, G.a + i, prec); arb_set_round_fmpz(D + i, G.d + i, prec); }
        jblk_clear(&G);
    }
    else
    {
        arb_ptr A1 = _arb_vec_init(4), D1 = _arb_vec_init(4), A2 = _arb_vec_init(4), D2 = _arb_vec_init(4);
        slong m = a + (b - a) / 2;
        ajbs(A1, D1, a, m, lim, c, prec);
        ajbs(A2, D2, m, b, lim, c, prec);
        am2mul(A, A2, A1, 0, prec);
        am2mul(D, A2, D1, 0, prec); am2mul(D, D2, A1, 1, prec);
        _arb_vec_clear(A1, 4); _arb_vec_clear(D1, 4); _arb_vec_clear(A2, 4); _arb_vec_clear(D2, 4);
    }
}

static int cf_jet(arb_t X, arb_t dX, slong an, slong ad, ulong P, slong ns, slong W)
{
    cfj_ctx c;
    bs_t B;
    arb_mat_t T;
    arb_t Q, b0, xa, xb, da, db, t;
    slong prec = W + 64, d;
    int ok;
    c.an = an; c.ad = ad; c.P = P; c.jet = (dX != NULL);
    d = c.jet ? 4 : 2;
    B.d = d; B.s = 0; B.leaf = cfj_leaf; B.ctx = &c;
    arb_mat_init(T, d, d); arb_init(Q); arb_init(b0); arb_init(xa); arb_init(xb); arb_init(da); arb_init(db); arb_init(t);
    if (c.jet)
    {
        arb_ptr A = _arb_vec_init(4), D = _arb_vec_init(4);
        slong lb, i;
        jblk G; jblk_init(&G); jleaf(&G, ns, &c);
        lb = FLINT_MAX(fmpz_bits(G.a + 0), fmpz_bits(G.a + 1)) + 2;
        jblk_clear(&G);
        ajbs(A, D, 1, ns + 1, FLINT_MAX(1, 2 * prec / lb), &c, prec);
        for (i = 0; i < 4; i++) { arb_set(arb_mat_entry(T, i / 2, i % 2), A + i); arb_set(arb_mat_entry(T, i / 2, 2 + i % 2), D + i); }
        _arb_vec_clear(A, 4); _arb_vec_clear(D, 4);
    }
    else
        bs_product(T, Q, 1, ns + 1, &B, prec);
    arb_set_ui(b0, P); arb_mul_ui(b0, b0, 2 * ad, prec);
#define TT(i, j) arb_mat_entry(T, i, j)
    arb_div(xa, TT(0, 1), TT(0, 0), prec); arb_add(xa, xa, b0, prec);
    arb_div(xb, TT(1, 1), TT(1, 0), prec); arb_add(xb, xb, b0, prec);
    if (c.jet)
    {
        arb_mul(da, TT(0, 3), TT(0, 0), prec); arb_submul(da, TT(0, 1), TT(0, 2), prec);
        arb_div(da, da, TT(0, 0), prec); arb_div(da, da, TT(0, 0), prec);
        arb_mul(db, TT(1, 3), TT(1, 0), prec); arb_submul(db, TT(1, 1), TT(1, 2), prec);
        arb_div(db, db, TT(1, 0), prec); arb_div(db, db, TT(1, 0), prec);
        arb_sub(t, da, db, prec);
        {
            mag_t m; mag_init(m); arb_get_mag(m, t); mag_mul_2exp_si(m, m, 1);
            arb_add_error_mag(da, m); mag_clear(m);
        }
        arb_set(dX, da);
    }
#undef TT
    arb_union(X, xa, xb, prec);
    ok = arb_rel_accuracy_bits(X) >= W && (!c.jet || arb_rel_accuracy_bits(dX) >= W - 8);
    arb_mat_clear(T); arb_clear(Q); arb_clear(b0); arb_clear(xa); arb_clear(xb); arb_clear(da); arb_clear(db); arb_clear(t);
    return ok;
}

static void S_k(arb_t res, slong idx, slong prec, void * unused)
{
    slong k = idx + 1, W, N;
    double x = (double) k * k * U0_D;
    ulong P = (ulong) k * k;
    klow_ctx c;
    bs_t B;
    arb_ptr x0, sm;
    arb_t xa, em, logk, t, u, Ck, Sk, E1, Bk;
    (void) unused;
    if (k - x * LOG2E < -(prec + 64)) { arb_zero(res); return; }
    W = prec + k + 64 + 2 * FLINT_BIT_COUNT(k);
    x0 = _arb_vec_init(2); sm = _arb_vec_init(2);
    arb_init(xa); arb_init(em); arb_init(logk); arb_init(t); arb_init(u);
    arb_init(Ck); arb_init(Sk); arb_init(E1); arb_init(Bk);
    c.P = P;
    arb_set_ui(xa, P); arb_mul_2exp_si(xa, xa, -2 * U0_EXP);        /* exact */
    arb_neg(em, xa); arb_exp(em, em, W);
    /* continued fractions when they are shorter than the lower series (large x) */
    {
        slong Wr = FLINT_MAX(64, prec + 64 + k - (slong) (x * LOG2E) + 2 * FLINT_BIT_COUNT(k) + 20);
        double ncf = pow(Wr / 2.4, 2) / x + 1000;
        if (1.5 * ncf < (double) lower_len(x, 0.5, 1.0, 0, W))
        {
            slong ns = (slong) ncf;
            arb_t X0, X, dX;
            arb_init(X0); arb_init(X); arb_init(dX);
            while (!cf_jet(X0, NULL, 0, 1, P, ns, Wr)) ns = ns * 3 / 2;
            ns = (slong) ncf;
            while (!cf_jet(X, dX, 1, 2, P, ns, Wr)) ns = ns * 3 / 2;
            /* E1 = e^-x 2 ud/X0; Q(1/2, x) = e^-x sqrt(x) 4 ud/(sqrt(pi) X); B = Q (L0 - dX/X)/2 */
            arb_mul_fmpz(E1, em, U0_DEN, Wr); arb_mul_2exp_si(E1, E1, 1); arb_div(E1, E1, X0, Wr);
            arb_mul_fmpz(Bk, em, U0_DEN, Wr); arb_mul_ui(Bk, Bk, k, Wr); arb_mul_2exp_si(Bk, Bk, 2 - U0_EXP);
            arb_div(Bk, Bk, X, Wr); arb_div(Bk, Bk, S_sqrtpi, Wr);
            arb_div(t, dX, X, Wr); arb_sub(t, S_L0, t, Wr);
            arb_mul(Bk, Bk, t, Wr); arb_mul_2exp_si(Bk, Bk, -1);
            arb_clear(X0); arb_clear(X); arb_clear(dX);
            goto combine;
        }
    }
    arb_zero(logk);
    add_log_of(logk, k, S_logp, S_pidx, W);

    /* E1(x) = -gamma - 2 log k - log u0 + e^-x sum_{n>=1} x^n H'_n/n! */
    N = lower_len(x, 0.0, log2(x), 1, W);
    B.d = 2; B.s = 1; B.leaf = ein_leaf2; B.ctx = &c;
    arb_set(x0, xa); arb_set(x0 + 1, xa);
    bs_eval(NULL, sm, x0, 1, N, &B, W);
    arb_mul(E1, sm, em, W);
    arb_sub(E1, E1, S_euler, W);
    arb_submul_ui(E1, logk, 2, W);
    arb_sub(E1, E1, S_logu0, W);

    /* B_k = -log k + sqrt(x) e^-x (Su - L0 St)/(2 sqrt(pi)) */
    N = lower_len(x, 0.5, 1.0, 0, W);
    B.d = 2; B.s = 2; B.leaf = half_leaf; B.ctx = &c;
    arb_set_ui(x0, 2); arb_set_ui(x0 + 1, 4);
    bs_eval(NULL, sm, x0, 0, N, &B, W);
    arb_mul(t, S_L0, sm, W);
    arb_sub(t, sm + 1, t, W);
    arb_mul(t, t, em, W);
    arb_mul_ui(t, t, k, W); arb_mul_2exp_si(t, t, -U0_EXP - 1);      /* sqrt(x)/2 = k 2^-a/2 */
    arb_div(t, t, S_sqrtpi, W);
    arb_sub(Bk, t, logk, W);

combine:
    /* C_k E1/2 + S_k B_k */
    arb_one(u); arb_mul_2exp_si(u, u, -k);
    arb_one(t); arb_mul_2exp_si(t, t, k);
    arb_add(Ck, u, t, W); arb_mul_2exp_si(Ck, Ck, -1);
    arb_sub(Sk, u, t, W); arb_mul_2exp_si(Sk, Sk, -1);
    arb_mul(E1, E1, Ck, W); arb_mul_2exp_si(E1, E1, -1);
    arb_mul(Bk, Bk, Sk, W);
    arb_add(res, E1, Bk, prec + 64);

    _arb_vec_clear(x0, 2); _arb_vec_clear(sm, 2);
    arb_clear(xa); arb_clear(em); arb_clear(logk); arb_clear(t); arb_clear(u);
    arb_clear(Ck); arb_clear(Sk); arb_clear(E1); arb_clear(Bk);
}

/* ======================= complex bit-burst for V_a ======================= */

/* Taylor step for y V' = (y - a) V - 1 from z0 = Y/2^e to z1 = Y1/2^E (Gaussian integers), a = an/ad.
   With T_l = V_l h^l, h = H/2^E, and R_l = h T_{l-1}:
   T_{l+1} = H conj(Y) [(Y ad - (an + l ad) 2^e) T_l + ad 2^e R_l] / (ad 2^E |Y|^2 (l+1)),  R_{l+1} = h T_l.
   State (T_l, R_l) in real coordinates; the sum collects T_l. */
typedef struct { fmpz_t a0r, a0i, a1r, a1i, br, bi, Hr, Hi, y2, q0; } vstep_ctx;

static void cmul_fmpz(fmpz_t rr, fmpz_t ri, const fmpz_t ar, const fmpz_t ai, const fmpz_t br, const fmpz_t bi)
{
    fmpz_t t, u;
    fmpz_init(t); fmpz_init(u);
    fmpz_mul(t, ar, br); fmpz_submul(t, ai, bi);
    fmpz_mul(u, ar, bi); fmpz_addmul(u, ai, br);
    fmpz_swap(rr, t); fmpz_swap(ri, u);
    fmpz_clear(t); fmpz_clear(u);
}


/* Binary splitting for the 2x2 complex recurrence of vstep, with Gaussian integers and Karatsuba-style complex
   products (3 real multiplications), instead of the 4x4 real embedding. A block is
   [M (2x2), S (1x2), Q]: X_b = M X_a / Q, sum_{a<=l<b} T_l = S X_a / Q. */
typedef struct { fmpz re[6], im[6]; fmpz_t Q; } gblk;      /* m00 m01 m10 m11 s0 s1 */
typedef struct { acb_struct m[6]; arb_t Q; } ablk;

static void gblk_init(gblk * B) { int i; for (i = 0; i < 6; i++) { fmpz_init(B->re + i); fmpz_init(B->im + i); } fmpz_init(B->Q); }
static void gblk_clear(gblk * B) { int i; for (i = 0; i < 6; i++) { fmpz_clear(B->re + i); fmpz_clear(B->im + i); } fmpz_clear(B->Q); }

/* r = a b (complex), 3 multiplications; r may not alias */
static void gmul(fmpz_t rr, fmpz_t ri, const fmpz_t ar, const fmpz_t ai, const fmpz_t br, const fmpz_t bi)
{
    fmpz_t k1, k2, k3, t;
    fmpz_init(k1); fmpz_init(k2); fmpz_init(k3); fmpz_init(t);
    fmpz_add(t, ar, ai); fmpz_mul(k1, t, br);
    fmpz_sub(t, bi, br); fmpz_mul(k2, t, ar);
    fmpz_add(t, br, bi); fmpz_mul(k3, t, ai);
    fmpz_sub(rr, k1, k3); fmpz_add(ri, k1, k2);
    fmpz_clear(k1); fmpz_clear(k2); fmpz_clear(k3); fmpz_clear(t);
}

static void gaddmul(fmpz_t rr, fmpz_t ri, const fmpz_t ar, const fmpz_t ai, const fmpz_t br, const fmpz_t bi)
{
    fmpz_t u, v; fmpz_init(u); fmpz_init(v);
    gmul(u, v, ar, ai, br, bi); fmpz_add(rr, rr, u); fmpz_add(ri, ri, v);
    fmpz_clear(u); fmpz_clear(v);
}

/* R = B2 * B1 */
static void gblk_mul(gblk * R, const gblk * B2, const gblk * B1)
{
    int i, j, k;
    for (i = 0; i < 2; i++)
        for (j = 0; j < 2; j++)
        {
            fmpz_zero(R->re + 2 * i + j); fmpz_zero(R->im + 2 * i + j);
            for (k = 0; k < 2; k++)
                gaddmul(R->re + 2 * i + j, R->im + 2 * i + j, B2->re + 2 * i + k, B2->im + 2 * i + k, B1->re + 2 * k + j, B1->im + 2 * k + j);
        }
    for (j = 0; j < 2; j++)
    {
        fmpz_mul(R->re + 4 + j, B2->Q, B1->re + 4 + j); fmpz_mul(R->im + 4 + j, B2->Q, B1->im + 4 + j);
        for (k = 0; k < 2; k++)
            gaddmul(R->re + 4 + j, R->im + 4 + j, B2->re + 4 + k, B2->im + 4 + k, B1->re + 2 * k + j, B1->im + 2 * k + j);
    }
    fmpz_mul(R->Q, B2->Q, B1->Q);
}

static void vleaf(gblk * B, slong l, const vstep_ctx * c)
{
    fmpz_t s;
    fmpz_init(s);
    fmpz_set(B->re + 0, c->a0r); fmpz_addmul_ui(B->re + 0, c->a1r, l);
    fmpz_set(B->im + 0, c->a0i); fmpz_addmul_ui(B->im + 0, c->a1i, l);
    fmpz_set(B->re + 1, c->br); fmpz_set(B->im + 1, c->bi);
    fmpz_mul_ui(s, c->y2, l + 1);
    fmpz_mul(B->re + 2, c->Hr, s); fmpz_mul(B->im + 2, c->Hi, s);
    fmpz_zero(B->re + 3); fmpz_zero(B->im + 3);
    fmpz_mul_ui(B->Q, c->q0, l + 1);
    fmpz_set(B->re + 4, B->Q); fmpz_zero(B->im + 4);
    fmpz_zero(B->re + 5); fmpz_zero(B->im + 5);
    fmpz_clear(s);
}

static void gbs(gblk * R, slong a, slong b, const vstep_ctx * c)
{
    gblk L;
    slong m;
    if (b - a == 1) { vleaf(R, a, c); return; }
    m = a + (b - a) / 2;
    gblk_init(&L);
    gbs(&L, a, m, c);
    {
        gblk U; gblk_init(&U);
        gbs(&U, m, b, c);
        gblk_mul(R, &U, &L);
        gblk_clear(&U);
    }
    gblk_clear(&L);
}

static void ablk_init(ablk * B) { int i; for (i = 0; i < 6; i++) acb_init(B->m + i); arb_init(B->Q); }
static void ablk_clear(ablk * B) { int i; for (i = 0; i < 6; i++) acb_clear(B->m + i); arb_clear(B->Q); }

static void ablk_mul(ablk * R, const ablk * B2, const ablk * B1, slong prec)
{
    int i, j;
    acb_t t;
    acb_init(t);
    for (i = 0; i < 2; i++)
        for (j = 0; j < 2; j++)
        {
            acb_mul(R->m + 2 * i + j, B2->m + 2 * i, B1->m + j, prec);
            acb_mul(t, B2->m + 2 * i + 1, B1->m + 2 + j, prec);
            acb_add(R->m + 2 * i + j, R->m + 2 * i + j, t, prec);
        }
    for (j = 0; j < 2; j++)
    {
        acb_mul_arb(R->m + 4 + j, B1->m + 4 + j, B2->Q, prec);
        acb_mul(t, B2->m + 4, B1->m + j, prec); acb_add(R->m + 4 + j, R->m + 4 + j, t, prec);
        acb_mul(t, B2->m + 5, B1->m + 2 + j, prec); acb_add(R->m + 4 + j, R->m + 4 + j, t, prec);
    }
    arb_mul(R->Q, B2->Q, B1->Q, prec);
    acb_clear(t);
}

static void abs_top(ablk * R, slong a, slong b, slong lim, const vstep_ctx * c, slong prec)
{
    if (b - a <= lim)
    {
        gblk G; int i;
        gblk_init(&G);
        gbs(&G, a, b, c);
        for (i = 0; i < 6; i++)
        {
            arb_set_round_fmpz(acb_realref(R->m + i), G.re + i, prec);
            arb_set_round_fmpz(acb_imagref(R->m + i), G.im + i, prec);
        }
        arb_set_round_fmpz(R->Q, G.Q, prec);
        gblk_clear(&G);
    }
    else
    {
        ablk L, U;
        slong m = a + (b - a) / 2;
        ablk_init(&L); ablk_init(&U);
        abs_top(&L, a, m, lim, c, prec);
        abs_top(&U, m, b, lim, c, prec);
        ablk_mul(R, &U, &L, prec);
        ablk_clear(&L); ablk_clear(&U);
    }
}

/* sum_{a <= l < b} T_l from X_a = (T_a, R_a) */
static void vsum(acb_t res, const acb_t Ta, const acb_t Ra, slong a, slong b, const vstep_ctx * c, slong prec)
{
    ablk R;
    slong lb, lim;
    acb_t t;
    gblk G;
    gblk_init(&G); vleaf(&G, b - 1, c);
    lb = FLINT_MAX(fmpz_bits(G.re + 0), fmpz_bits(G.Q)) + 4;
    gblk_clear(&G);
    lim = FLINT_MAX(1, 2 * prec / lb);
    ablk_init(&R); acb_init(t);
    abs_top(&R, a, b, lim, c, prec);
    acb_mul(res, R.m + 4, Ta, prec);
    acb_mul(t, R.m + 5, Ra, prec); acb_add(res, res, t, prec);
    acb_div_arb(res, res, R.Q, prec);
    ablk_clear(&R); acb_clear(t);
}

static double lg2add(double a, double b)       /* log2(2^a + 2^b) */
{
    if (a < b) { double t = a; a = b; b = t; }
    if (b < a - 60) return a;
    return a + log2(1 + exp2(b - a));
}

static double fmpz_log2_abs(const fmpz_t x)
{
    slong ex;
    double m;
    if (fmpz_is_zero(x)) return -1e300;
    m = fmpz_get_d_2exp(&ex, x);
    return log2(fabs(m)) + ex;
}

static void vstep(acb_t V, int an, int ad, const fmpz_t Yr, const fmpz_t Yi, slong e,
                  const fmpz_t Y1r, const fmpz_t Y1i, slong E, slong W)
{
    vstep_ctx c;
    fmpz_t Hr, Hi, cYr, cYi, t, u;
    double lh, z0r, z0i, z0d, lr, lp, peak, ln;
    slong L, l, wp;
    acb_t z0, h, V1, T1;
    fmpz_init(Hr); fmpz_init(Hi); fmpz_init(cYr); fmpz_init(cYi); fmpz_init(t); fmpz_init(u);
    fmpz_init(c.a0r); fmpz_init(c.a0i); fmpz_init(c.a1r); fmpz_init(c.a1i); fmpz_init(c.br); fmpz_init(c.bi); fmpz_init(c.q0);
    fmpz_init(c.Hr); fmpz_init(c.Hi); fmpz_init(c.y2);
    fmpz_mul_2exp(Hr, Yr, E - e); fmpz_sub(Hr, Y1r, Hr);
    fmpz_mul_2exp(Hi, Yi, E - e); fmpz_sub(Hi, Y1i, Hi);
    if (fmpz_is_zero(Hr) && fmpz_is_zero(Hi)) goto cleanup0;
    /* term estimate */
    lh = 0.5 * lg2add(2 * fmpz_log2_abs(Hr), 2 * fmpz_log2_abs(Hi)) - E;
    { slong ex; double m;
      m = fmpz_get_d_2exp(&ex, Yr); z0r = ldexp(m, ex - e);
      m = fmpz_get_d_2exp(&ex, Yi); z0i = ldexp(m, ex - e); }
    z0d = sqrt(z0r * z0r + z0i * z0i);
    lp = 0; lr = lh + 1; peak = FLINT_MAX(0, lr);
    for (l = 1; ; l++)
    {
        double a = (double) an / ad;
        ln = lh - log2(z0d) - log2(l + 1.0)
            + lg2add(log2(sqrt(pow(z0r - a - l, 2) + z0i * z0i) + 1e-300) + lr, lh + lp);
        lp = lr; lr = ln;
        peak = FLINT_MAX(peak, lr);
        if (l >= 2 && lr < -(W + 64) && lp < -(W + 64)) break;
    }
    L = l + 2;
    wp = W + (slong) peak + 64;
    /* coefficients: HcY = H conj(Y); alpha_l = HcY (Y ad - an 2^e) - l HcY ad 2^e; beta = HcY ad 2^e;
       q_l = ad 2^E |Y|^2 (l+1); R row: H ad |Y|^2 (l+1) */
    fmpz_set(cYr, Yr); fmpz_neg(cYi, Yi);
    cmul_fmpz(t, u, Hr, Hi, cYr, cYi);
    {
        fmpz_t Ar, Ai, s2;
        fmpz_init(Ar); fmpz_init(Ai); fmpz_init(s2);
        fmpz_one(s2); fmpz_mul_2exp(s2, s2, e);
        fmpz_mul_ui(Ar, Yr, ad); fmpz_submul_ui(Ar, s2, an);
        fmpz_mul_ui(Ai, Yi, ad);
        cmul_fmpz(c.a0r, c.a0i, t, u, Ar, Ai);
        fmpz_mul_ui(c.br, t, ad); fmpz_mul_2exp(c.br, c.br, e);
        fmpz_mul_ui(c.bi, u, ad); fmpz_mul_2exp(c.bi, c.bi, e);
        fmpz_neg(c.a1r, c.br); fmpz_neg(c.a1i, c.bi);
        fmpz_clear(Ar); fmpz_clear(Ai); fmpz_clear(s2);
    }
    fmpz_set(c.Hr, Hr); fmpz_set(c.Hi, Hi);
    fmpz_mul(c.y2, Yr, Yr); fmpz_addmul(c.y2, Yi, Yi); fmpz_mul_ui(c.y2, c.y2, ad);
    fmpz_mul_2exp(c.q0, c.y2, E);
    /* T_0 = V, T_1 = h ((z0 - a) V - 1)/z0 */
    acb_init(z0); acb_init(h); acb_init(V1); acb_init(T1);
    arb_set_fmpz(acb_realref(z0), Yr); arb_set_fmpz(acb_imagref(z0), Yi); acb_mul_2exp_si(z0, z0, -e);
    arb_set_fmpz(acb_realref(h), Hr); arb_set_fmpz(acb_imagref(h), Hi); acb_mul_2exp_si(h, h, -E);
    {
        arb_t a; arb_init(a); arb_set_si(a, an); arb_div_si(a, a, ad, wp);
        acb_sub_arb(V1, z0, a, wp); acb_mul(V1, V1, V, wp); acb_sub_ui(V1, V1, 1, wp);
        acb_div(V1, V1, z0, wp); acb_mul(T1, V1, h, wp);
        arb_clear(a);
    }
    acb_mul(V1, V, h, wp);                                   /* R_1 = h T_0 */
    { double t0 = cpu_seconds();
    acb_t sm;
    acb_init(sm);
    vsum(sm, T1, V1, 1, L, &c, wp);
    acb_add(V, V, sm, wp);
    acb_clear(sm);
    if (getenv("HOLSUM_PROF")) flint_fprintf(stderr, "vstep e=%wd E=%wd L=%wd wp=%wd %.3f s\n", e, E, L, wp, cpu_seconds() - t0); }
    acb_clear(z0); acb_clear(h); acb_clear(V1); acb_clear(T1);
cleanup0:
    fmpz_clear(Hr); fmpz_clear(Hi); fmpz_clear(cYr); fmpz_clear(cYi); fmpz_clear(t); fmpz_clear(u);
    fmpz_clear(c.a0r); fmpz_clear(c.a0i); fmpz_clear(c.a1r); fmpz_clear(c.a1i); fmpz_clear(c.br); fmpz_clear(c.bi); fmpz_clear(c.q0);
    fmpz_clear(c.Hr); fmpz_clear(c.Hi); fmpz_clear(c.y2);
}

/* V = V_a(y), a = 0 (half = 0) or 1/2 (half = 1), relative accuracy about W; Re y > 0 large enough that the
   real starting point y_s ~ Re y works with gamma_upper_exact; path y_s -> y along the vertical direction */
static void V_eval(acb_t V, int half, const acb_t y, slong W)
{
    fmpz_t Yr, Yi, Y1r, Y1i;
    slong e = 8, E, Efin = W + 64, guard;
    arb_t ys, G, t;
    double imd = fabs(arf_get_d(arb_midref(acb_imagref(y)), ARF_RND_NEAR));
    fmpz_init(Yr); fmpz_init(Yi); fmpz_init(Y1r); fmpz_init(Y1i);
    arb_init(ys); arb_init(G); arb_init(t);
    guard = (slong) (2 * imd * LOG2E) + 64;
    /* starting value at y_s = Re y to 8 bits */
    arf_get_fmpz_fixed_si(Yr, arb_midref(acb_realref(y)), -e);
    fmpz_zero(Yi);
    arb_set_fmpz(ys, Yr); arb_mul_2exp_si(ys, ys, -e);
    { double t0 = cpu_seconds();
    gamma_upper_exact(G, half, ys, W + guard + 64);
    if (getenv("HOLSUM_PROF")) flint_fprintf(stderr, "gamma %d %.3f s\n", half, cpu_seconds() - t0); }
    arb_exp(t, ys, W + guard + 64);
    arb_mul(G, G, t, W + guard + 64);
    if (half) { arb_rsqrt(t, ys, W + guard + 64); arb_mul(G, G, t, W + guard + 64); }
    acb_set_arb(V, G);
    /* first step: to y rounded to 8 bits, then refinements with 4x more bits */
    E = e;
    for (;;)
    {
        int last;
        last = (E >= Efin);
        arf_get_fmpz_fixed_si(Y1r, arb_midref(acb_realref(y)), -E);
        arf_get_fmpz_fixed_si(Y1i, arb_midref(acb_imagref(y)), -E);
        vstep(V, half ? 1 : 0, half ? 2 : 1, Yr, Yi, e, Y1r, Y1i, E, W);
        fmpz_swap(Yr, Y1r); fmpz_swap(Yi, Y1i); e = E;
        if (last) break;
        E = FLINT_MIN(4 * E, Efin);
        if (E < 32) E = 32;
    }
    /* distance to the ball y and its radius: |V'| <= 2|V| + 1 for |y| >= 1 */
    {
        mag_t r, m;
        mag_init(r); mag_init(m);
        mag_set_ui_2exp_si(r, 1, -e + 1);
        mag_add(r, r, arb_radref(acb_realref(y))); mag_add(r, r, arb_radref(acb_imagref(y)));
        acb_get_mag(m, V); mag_mul_2exp_si(m, m, 1); mag_add_ui(m, m, 1);
        mag_mul(r, r, m);
        acb_add_error_mag(V, r);
        mag_clear(r); mag_clear(m);
    }
    fmpz_clear(Yr); fmpz_clear(Yi); fmpz_clear(Y1r); fmpz_clear(Y1i);
    arb_clear(ys); arb_clear(G); arb_clear(t);
}

/* ======================= dual side ======================= */

static void S_dual(arb_t res, slong idx, slong prec, void * unused)
{
    slong n = idx + 1, W, wp;
    double ry = (9.8696044010893586 * n * n - 0.1201132) / U0_D;
    acb_t y, w, V12, V0, t;
    arb_t pi, tau;
    (void) unused;
    W = prec + 64 - (slong) (ry * LOG2E) + 16;
    if (W < 64) { arb_zero(res); return; }
    wp = W + 64 + FLINT_BIT_COUNT(n) * 4;
    acb_init(y); acb_init(w); acb_init(V12); acb_init(V0); acb_init(t);
    arb_init(pi); arb_init(tau);
    arb_const_pi(pi, wp + 64);
    arb_set_round(tau, S_log2, wp + 64);
    /* w = pi n - i tau/2, y = w^2/u0 */
    arb_mul_ui(acb_realref(w), pi, n, wp + 64);
    arb_mul_2exp_si(acb_imagref(w), tau, -1); arb_neg(acb_imagref(w), acb_imagref(w));
    acb_sqr(y, w, wp + 64);
    acb_mul_2exp_si(y, y, 2 * U0_EXP);
    V_eval(V12, 1, y, W);
    V_eval(V0, 0, y, W);
    /* T = e^-y/(2 sqrt u0) [V12 - i sqrt(u0) (L0 - V0)/(sqrt(pi) w)] */
    acb_sub_arb(V0, V0, S_L0, wp); acb_neg(V0, V0);
    acb_div(V0, V0, w, wp);
    arb_sqrt(pi, pi, wp); acb_div_arb(V0, V0, pi, wp);
    acb_mul_2exp_si(V0, V0, -U0_EXP);                               /* sqrt(u0) = 2^-a */
    acb_mul_onei(V0, V0);
    acb_sub(t, V12, V0, wp);
    acb_neg(y, y); acb_exp(y, y, wp);
    acb_mul(t, t, y, wp);
    acb_mul_2exp_si(t, t, U0_EXP - 1);
    /* contribution sqrt(pi) Re T (the terms n and -n) */
    arb_mul(res, acb_realref(t), pi, prec + 64);
    acb_clear(y); acb_clear(w); acb_clear(V12); acb_clear(V0); acb_clear(t);
    arb_clear(pi); arb_clear(tau);
}

/* ======================= setup, main term ======================= */

static ulong * S_primes;
static slong S_np;

static void somos_setup(slong prec)
{
    slong wp;
    arb_t t, u, ay, ra, J0, J1, c;
    S_kmax = somos_k_count(prec);
    S_lprec = prec + S_kmax + 128;
    wp = S_lprec;
    arb_init(S_log2); arb_init(S_euler); arb_init(S_sqrtpi); arb_init(S_logu0); arb_init(S_L0); arb_init(S_main);
    arb_const_log2(S_log2, wp);
    arb_const_euler(S_euler, wp);
    arb_const_sqrt_pi(S_sqrtpi, wp);
    arb_mul_si(S_logu0, S_log2, -2 * U0_EXP, wp);
    arb_add(S_L0, S_logu0, S_euler, wp); arb_addmul_ui(S_L0, S_log2, 2, wp);
    S_np = log_primes(&S_logp, &S_primes, &S_pidx, S_kmax + 1, wp, ENGINE_THREADS);

    /* n = 0: (sqrt(pi)/2) (Re J0' - (tau/2) Re J1'), with |y| = tau^2/(4 u0), c = -tau^2/4,
       Re J0' = -sqrt(pi) erfi(sqrt|y|)/(2 sqrt(u0) sqrt|y|), Re J1' = (e^|y| L0 + Ei(|y|))/(2 sqrt(pi) c) */
    arb_zero(S_main);
    if (!ENGINE_NEED_MAIN) return;
    wp = prec + 128;
    arb_init(t); arb_init(u); arb_init(ay); arb_init(ra); arb_init(J0); arb_init(J1); arb_init(c);
    arb_mul_2exp_si(ra, S_log2, U0_EXP - 1);                         /* sqrt|y| = tau/(2 sqrt u0) */
    arb_sqr(ay, ra, wp);
    arb_hypgeom_erfi(J0, ra, wp);
    arb_div(J0, J0, ra, wp); arb_mul(J0, J0, S_sqrtpi, wp);
    arb_mul_2exp_si(J0, J0, U0_EXP - 1); arb_neg(J0, J0);
    arb_exp(t, ay, wp); arb_mul(t, t, S_L0, wp);
    arb_hypgeom_ei(u, ay, wp); arb_add(J1, t, u, wp);
    arb_sqr(c, S_log2, wp); arb_mul_2exp_si(c, c, -2); arb_neg(c, c);
    arb_div(J1, J1, c, wp); arb_div(J1, J1, S_sqrtpi, wp); arb_mul_2exp_si(J1, J1, -1);
    arb_mul(J1, J1, S_log2, wp); arb_mul_2exp_si(J1, J1, -1);
    arb_sub(t, J0, J1, wp);
    arb_mul(t, t, S_sqrtpi, wp); arb_mul_2exp_si(t, t, -1);
    /* main = dual_0 - (log u0 + gamma)/4 */
    arb_add(u, S_logu0, S_euler, wp); arb_mul_2exp_si(u, u, -2);
    arb_sub(S_main, t, u, wp);
    arb_clear(t); arb_clear(u); arb_clear(ay); arb_clear(ra); arb_clear(J0); arb_clear(J1); arb_clear(c);
}

static void somos_clear(void)
{
    arb_clear(S_log2); arb_clear(S_euler); arb_clear(S_sqrtpi); arb_clear(S_logu0); arb_clear(S_L0); arb_clear(S_main);
    _arb_vec_clear(S_logp, FLINT_MAX(S_np, 1));
    flint_free(S_primes); flint_free(S_pidx);
}

static void S_main_term(arb_t res) { arb_set(res, S_main); }

/* sigma = exp(-lin) */
static void S_finish(arb_t res, const arb_t lin, slong prec)
{
    arb_neg(res, lin);
    arb_exp(res, res, prec + 64);
}

/* ======================= reference: prime sum ======================= */

typedef struct { const ulong * pr; arb_srcptr logp; slong n, prec, nblocks; arb_ptr part; } ps_ctx;

static void ps_block(slong b, void * vctx)
{
    ps_ctx * c = vctx;
    slong i, N = c->prec + 80;
    arb_t s, t;
    arb_init(s); arb_init(t);
    for (i = b; i < c->n; i += c->nblocks)
    {
        ulong p = c->pr[i], m;
        arb_zero(s);
        for (m = p; m <= (ulong) N; m *= p)
        {
            arb_one(t); arb_mul_2exp_si(t, t, m); arb_sub_ui(t, t, 1, c->prec + 64);
            arb_inv(t, t, c->prec + 64 - m > 64 ? c->prec + 64 - m : 64);
            arb_add(s, s, t, c->prec + 64);
            if (m > (ulong) N / p) break;
        }
        arb_addmul(c->part + b, s, c->logp + i, c->prec + 64);
    }
    arb_clear(s); arb_clear(t);
}

static void S_ref_direct(arb_t res, slong prec, int threads)
{
    arb_ptr logp; ulong * pr; slong * idx, n, b;
    ps_ctx c;
    ulong N = prec + 80;
    n = log_primes(&logp, &pr, &idx, N, prec + 64, threads);
    c.pr = pr; c.logp = logp; c.n = n; c.prec = prec; c.nblocks = 64 * FLINT_MAX(threads, 1);
    c.part = _arb_vec_init(c.nblocks);
    parallel_for(c.nblocks, ps_block, &c, threads);
    arb_zero(res);
    for (b = 0; b < c.nblocks; b++) arb_add(res, res, c.part + b, prec + 64);
    /* tail sum_{m > N} log m 2^-m < 2^-(N - 2 log2 N) */
    {
        mag_t tl; mag_init(tl);
        mag_set_ui_2exp_si(tl, 1, -(slong) N + 2 * FLINT_BIT_COUNT(N));
        arb_add_error_mag(res, tl);
        mag_clear(tl);
    }
    arb_exp(res, res, prec + 64);
    _arb_vec_clear(c.part, c.nblocks);
    _arb_vec_clear(logp, n); flint_free(pr); flint_free(idx);
}

const constant_t CONST_SOMOS = {
    "somos", "Somos's quadratic recurrence constant prod_{k>=1} k^(1/2^k) (OEIS A112302)",
    somos_setup, somos_clear, S_dual, S_k, 1, S_finish, S_main_term, NULL, NULL, 0,
    somos_k_count, somos_dual_count, S_ref_direct };
