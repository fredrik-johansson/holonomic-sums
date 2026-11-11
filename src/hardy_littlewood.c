/*
    The Hardy-Littlewood function at an integer x (environment variable HOLSUM_HL_X, default 1):

      H(x) = sum_{k>=1} sin(x/k)/k = sum_k f(1/k),   f(t) = t sin(x t)   (entire; the summand has an
      essential singularity at k = 0 but is analytic at infinity).

    Kernel h(u) = x 0F2(; 3/2, 1; -x^2 u/4), theta^2 (theta + 1/2) h = -(x^2/4) u h; dual moments
    Z_{1/2}[h] in a system of order 4 with three forcing constants; Gamma(1/2, y) starting values.
*/
#include <math.h>
#include <stdlib.h>
#include "constants.h"

static slong XX = 1;          /* x, integer */

/* ---------------- k-side: state (B, C) = alpha_m (e_m(x'), x'^m/m!), alpha_m = a_{2m} K^-m; sum B; m >= 1 ---------------- */
typedef struct { ulong K; } kctx;
static void k_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    ulong K = ((const kctx *) v)->K;
    fmpz_t a; fmpz_init(a);
    /* q = 2m(2m+1)(m+1) K U0_DEN; B' = rho (B + C), C' = rho x'/(m+1) C, rho = -x^2/(2m(2m+1)K) */
    fmpz_set_ui(q, 2 * (ulong) m * (2 * m + 1)); fmpz_mul_ui(q, q, m + 1); fmpz_mul_ui(q, q, K); fmpz_mul(q, q, U0_DEN);
    fmpz_set_si(a, -XX * XX); fmpz_mul_ui(a, a, m + 1); fmpz_mul(a, a, U0_DEN);          /* -x^2 (m+1) U0_DEN */
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), a);
    fmpz_set_si(a, -XX * XX); fmpz_mul_ui(a, a, K); fmpz_mul(a, a, U0_NUM);              /* -x^2 K U0_NUM */
    fmpz_set(fmpz_mat_entry(T, 1, 1), a);
    fmpz_set(fmpz_mat_entry(T, 2, 0), q);
    fmpz_clear(a);
}

static slong k_terms(ulong K, slong prec, double * lmax)
{
    double x = K * U0_D, lx = log2(x), lal = log2((double) XX) - log2((double) K), lr = lx, lE = 0, lt;
    slong m;
    *lmax = -1e300;
    for (m = 1; ; m++)
    {
        /* B_m = alpha_m e_m(x'), e_m = sum_{i<m} x'^i/i!; lr = log2(x'^m/m!) */
        lt = lal + lE - 1.4426950408889634 * x;
        if (lt > *lmax) *lmax = lt;
        if (m > x + 10 && lt < -prec - 64) return m + 2;
        lE = (lr > lE) ? lr + log2(1 + pow(2.0, lE - lr)) : lE + log2(1 + pow(2.0, lr - lE));
        lal += 2 * log2((double) XX) - log2(2.0 * m * (2 * m + 1) * K);
        lr += lx - log2((double) m + 1);
    }
}

static void k_term(arb_t res, ulong k, slong prec)
{
    ulong K = k * k;
    kctx kc; bs_t B; arb_ptr x0 = _arb_vec_init(2), s = _arb_vec_init(1);
    arb_t x, ex;
    double lmax;
    slong N = k_terms(K, prec, &lmax), wp = prec + 64 + (slong) lmax;
    if (wp < 64) { arb_zero(res); _arb_vec_clear(x0, 2); _arb_vec_clear(s, 1); return; }
    arb_init(x); arb_init(ex);
    kc.K = K;
    B.d = 2; B.s = 1; B.leaf = k_leaf; B.ctx = &kc;
    /* m = 1: alpha_1 = x/K, e_1 = 1, x'^1/1! = x' : B_1 = x/K, C_1 = x x'/K = x U0 */
    arb_set_si(x0 + 0, XX); arb_div_ui(x0 + 0, x0 + 0, K, wp + 32);
    arb_mul_si(x0 + 1, U0, XX, wp + 32);
    bs_eval(NULL, s, x0, 1, N, &B, wp + 32);
    arb_mul_ui(x, U0, K, ARF_PREC_EXACT);
    arb_neg(ex, x); arb_exp(ex, ex, wp + 32);
    arb_mul(res, s + 0, ex, wp + 32);
    _arb_vec_clear(x0, 2); _arb_vec_clear(s, 1); arb_clear(x); arb_clear(ex);
}

/* ---------------- dual system: state (c^j P, c^j Q, c^j R, (x^2/4) c^{j-1} P_{t-1}), t = 1/2 + j ---------------- */
static void amatH(fmpz * A, slong l, const fmpz_t C, const fmpz_t D)
{
    fmpz_mul_si(A + 0, D, 2 * l - 1); fmpz_mul_si(A + 1, D, -2);
    fmpz_mul_si(A + 5, D, 2 * l - 1); fmpz_mul_si(A + 6, D, -2);
    fmpz_mul_si(A + 10, D, 2 * l); fmpz_mul_si(A + 11, C, 2);
    fmpz_mul_si(A + 12, D, XX * XX); fmpz_tdiv_q_2exp(A + 12, A + 12, 1);       /* D x^2 / 2 (D = 2^e) */
}

/* starting values: h_j alpha_j =: A_j, h_j beta_j =: B_j, h_j U0^{j+3/2} =: U_j, with
   D_{j+1/2} = alpha_j G + beta_j E, G = D_{-1/2} = c^{-1/2} Gamma(1/2, c/U0),
   alpha_j = -2c alpha_{j-1}/(2j+1), beta_j = 2 (U0^{j+1/2} - c beta_{j-1})/(2j+1)  (alpha_{-1} = 1, beta_{-1} = 0).
   sums: A (1, j, j^2, 1/(2j+3)), B (same), U (1/(2j+3)) */
typedef struct { fmpz_t C, D; } ictx;
static void i_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    const ictx * c = v;
    ulong o = 2 * j + 3, j1 = j + 1;
    fmpz_t t; fmpz_init(t);
    fmpz_set_ui(q, 2 * o * o); fmpz_mul_ui(q, q, j1 * j1); fmpz_mul(q, q, c->D); fmpz_mul(q, q, U0_DEN);
    fmpz_mul_ui(t, c->C, 2 * XX * XX); fmpz_mul(t, t, U0_DEN);                      /* 2 x^2 C U0_DEN */
    fmpz_set(fmpz_mat_entry(T, 0, 0), t); fmpz_set(fmpz_mat_entry(T, 1, 1), t);
    fmpz_mul_ui(t, c->D, 2 * XX * XX); fmpz_mul(t, t, U0_DEN); fmpz_neg(t, t);       /* -2 x^2 D U0_DEN */
    fmpz_set(fmpz_mat_entry(T, 1, 2), t);
    fmpz_mul_ui(t, c->D, XX * XX * o); fmpz_mul(t, t, U0_NUM); fmpz_neg(t, t);       /* -x^2 U0_NUM (2j+3) D */
    fmpz_set(fmpz_mat_entry(T, 2, 2), t);
    fmpz_divexact_ui(t, q, o);
    fmpz_set(fmpz_mat_entry(T, 3, 0), q); fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), q, j);
    fmpz_mul_ui(fmpz_mat_entry(T, 5, 0), q, (ulong) j * j); fmpz_set(fmpz_mat_entry(T, 6, 0), t);
    fmpz_set(fmpz_mat_entry(T, 7, 1), q); fmpz_mul_ui(fmpz_mat_entry(T, 8, 1), q, j);
    fmpz_mul_ui(fmpz_mat_entry(T, 9, 1), q, (ulong) j * j); fmpz_set(fmpz_mat_entry(T, 10, 1), t);
    fmpz_set(fmpz_mat_entry(T, 11, 2), t);
    fmpz_clear(t);
}

static void initH(arb_ptr V, arb_t E, const fmpz_t C, slong e, slong wp, const void * sys)
{
    ictx ic; bs_t B; arb_t c, G, y, t; arb_ptr x0 = _arb_vec_init(3), s = _arb_vec_init(9);
    slong W, N, j;
    double cd, la = 0, lb = 0;
    arb_init(c); arb_init(G); arb_init(y); arb_init(t);
    arb_set_fmpz(c, C); arb_mul_2exp_si(c, c, -e);
    cd = arf_get_d(arb_midref(c), ARF_RND_NEAR);
    W = wp + (slong) (1.4427 * cd / U0_D + 6 * sqrt(cd) + 6 * pow(XX * XX * cd, 1.0 / 3)) + 64;
    arb_mul_fmpz(y, c, U0_DEN, ARF_PREC_EXACT); arb_div_fmpz(y, y, U0_NUM, W);
    arb_neg(E, y); arb_exp(E, E, wp + 64);
    gamma_upper_exact(G, 1, y, wp + 64);
    arb_rsqrt(t, c, wp + 64); arb_mul(G, G, t, wp + 64);              /* G = c^-1/2 Gamma(1/2, c/U0) */
    /* terms: alpha part ~ (x^2 c)^j/(j!^3 4^j) (times 2^j slack); beta part ~ (x^2 U0)^j/(j!^2 ...) */
    for (j = 1; ; j++)
    {
        la += log2((double) XX * XX * (cd + 1) + 1) - 3 * log2((double) j) + 2;
        lb += log2((double) XX * XX * U0_D + 1e-300) - 2 * log2((double) j) + 2;
        if (j > 10 && la < -W - 64 && lb < -W - 64) break;
    }
    N = j + 10;
    fmpz_init_set(ic.C, C); fmpz_init(ic.D); fmpz_one(ic.D); fmpz_mul_2exp(ic.D, ic.D, e);
    B.d = 3; B.s = 9; B.leaf = i_leaf; B.ctx = &ic;
    arb_mul_si(x0 + 0, c, -2 * XX, W);                     /* A_0 = x alpha_0 = -2 c x */
    arb_mul_si(x0 + 1, SQRT_U0, 2 * XX, W);                    /* B_0 = x beta_0 = 2 x U0^{1/2} */
    arb_mul(x0 + 2, U0, SQRT_U0, W); arb_mul_si(x0 + 2, x0 + 2, XX, W);   /* U_0 = x U0^{3/2} */
    bs_eval(NULL, s, x0, 0, N, &B, W);
    arb_mul(V + 0, G, s + 0, W); arb_addmul(V + 0, E, s + 4, W);
    arb_mul(V + 1, G, s + 1, W); arb_addmul(V + 1, E, s + 5, W);
    arb_mul(V + 2, G, s + 2, W); arb_addmul(V + 2, E, s + 6, W);
    /* P_{-1/2} = -2c G s3 + 2E (s8 - c s7); V3 = (x^2/4) P_{-1/2}/c */
    arb_mul(V + 3, G, s + 3, W); arb_mul(V + 3, V + 3, c, W); arb_mul_si(V + 3, V + 3, -2, W);
    arb_mul(t, c, s + 7, W); arb_sub(t, s + 8, t, W); arb_mul_2exp_si(t, t, 1); arb_addmul(V + 3, E, t, W);
    arb_div(V + 3, V + 3, c, W); arb_mul_si(V + 3, V + 3, XX * XX, W); arb_mul_2exp_si(V + 3, V + 3, -2);
    _arb_vec_clear(x0, 3); _arb_vec_clear(s, 9); arb_clear(c); arb_clear(G); arb_clear(y); arb_clear(t);
    fmpz_clear(ic.C); fmpz_clear(ic.D);
}

/* ---------------- setup: h-series at U0, main term ---------------- */
static moment_sys_t SH;
static arb_t MAIN;
/* Y_j = h_j U0^j, h_{j+1}/h_j = -x^2/(2(2j+3)(j+1)^2); sums Y, jY, j^2 Y, 2Y/(2j+1), Y/(j+1) */
static void y_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    ulong o = 2 * j + 3, e = 2 * j + 1, j1 = j + 1;
    fmpz_set_ui(q, 2 * o * j1 * j1); fmpz_mul_ui(q, q, e); fmpz_mul(q, q, U0_DEN);
    fmpz_set_si(fmpz_mat_entry(T, 0, 0), -XX * XX); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), e);
    fmpz_mul(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), U0_NUM);
    fmpz_set(fmpz_mat_entry(T, 1, 0), q);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), q, j);
    fmpz_mul_ui(fmpz_mat_entry(T, 3, 0), q, (ulong) j * j);
    fmpz_divexact_ui(fmpz_mat_entry(T, 4, 0), q, e); fmpz_mul_2exp(fmpz_mat_entry(T, 4, 0), fmpz_mat_entry(T, 4, 0), 1);
    fmpz_divexact_ui(fmpz_mat_entry(T, 5, 0), q, j1);
}

static void hl_setup(slong prec)
{
    const char * ex = getenv("HOLSUM_HL_X");
    if (ex != NULL) XX = atol(ex);
    slong wp = prec + 64, N;
    bs_t B; arb_ptr X0 = _arb_vec_init(1), R = _arb_vec_init(5);
    arb_t t, sp;
    double lg = 0;
    arb_init(t); arb_init(sp);
    for (N = 1; lg > -(double) (wp + 40); N++) lg += log2(XX * XX * U0_D + 1e-300) - 2 * log2((double) N) + 1;
    N += 10;
    B.d = 1; B.s = 5; B.leaf = y_leaf; B.ctx = NULL;
    arb_set_si(X0 + 0, XX);
    bs_eval(NULL, R, X0, 0, N, &B, wp);
    SH.kappa = _arb_vec_init(3);
    arb_set(SH.kappa + 0, R + 0); arb_set(SH.kappa + 1, R + 1); arb_set(SH.kappa + 2, R + 2);
    /* M = (sqrt(pi)/2) U0^{1/2} sum 2Y/(2j+1) - (1/2) U0 sum Y/(j+1) */
    arb_const_sqrt_pi(sp, wp);
    arb_init(MAIN);
    arb_mul(MAIN, R + 3, SQRT_U0, wp); arb_mul(MAIN, MAIN, sp, wp);
    arb_mul(t, R + 4, U0, wp); arb_sub(MAIN, MAIN, t, wp);
    arb_mul_2exp_si(MAIN, MAIN, -1);
    SH.d = 4; SH.ng = 3; SH.amat = amatH; SH.init = initH; SH.t0 = 0.5;
    SH.fsel[0] = 0; SH.fsel[1] = 1; SH.fsel[2] = 2; SH.fsel[3] = -1;
    SH.lag[0] = 0; SH.lag[1] = 0; SH.lag[2] = 0; SH.lag[3] = -1;
    arb_init(SH.f0scale); arb_set(SH.f0scale, SQRT_U0);
    _arb_vec_clear(X0, 1); _arb_vec_clear(R, 5); arb_clear(t); arb_clear(sp);
}


static void hl_clear(void) { moment_sys_clear(&SH); arb_clear(MAIN); }

static void H_dual(arb_t res, slong idx, slong prec, void * ctx)
{
    slong m = idx + 1, wp = dual_term_prec(m, prec);
    arb_t c, sp; arb_ptr V;
    arb_zero(res);
    if (wp < 64) return;
    V = _arb_vec_init(SYS_MAXD);
    arb_init(c); arb_init(sp);
    arb_const_pi(c, 2 * prec + 64); arb_mul_ui(c, c, m, 2 * prec + 64); arb_sqr(c, c, 2 * prec + 64);
    arb_const_sqrt_pi(sp, wp + 64);
    dual_state(V, &SH, c, wp);
    arb_mul(res, V + 0, sp, wp);
    arb_clear(c); arb_clear(sp); _arb_vec_clear(V, SYS_MAXD);
}

static void H_k(arb_t res, slong idx, slong prec, void * ctx) { k_term(res, idx + 1, prec); }
static void H_main(arb_t res) { arb_set(res, MAIN); }
static void H_finish(arb_t res, const arb_t lin, slong prec) { arb_set_round(res, lin, prec); }

static void hl_params(void)
{
    const char * ex = getenv("HOLSUM_HL_X");
    if (ex != NULL) XX = atol(ex);
}

/* ======================= reference: zeta-value expansion =======================
   H(x) = sum_{m>=0} (-1)^m zeta(2m+2) x^(2m+1)/(2m+1)!  (even zeta values, i.e. Bernoulli numbers) */
#define HBLK 64
typedef struct { slong M, wp, nblocks; arb_ptr part; } hzctx;

static void hz_block(slong b, void * vctx)
{
    hzctx * c = vctx;
    slong m0 = b * HBLK, num = FLINT_MIN(HBLK, c->M - m0), i, wp = c->wp;
    arb_ptr z; arb_t f, t;
    if (num <= 0) return;
    z = _arb_vec_init(num); arb_init(f); arb_init(t);
    arb_zeta_ui_vec_even(z, 2 * m0 + 2, num, wp);
    /* f = x^(2m0+1)/(2m0+1)! */
    arb_set_si(f, XX); arb_pow_ui(f, f, 2 * m0 + 1, wp);
    arb_fac_ui(t, 2 * m0 + 1, wp); arb_div(f, f, t, wp);
    arb_zero(c->part + b);
    for (i = 0; i < num; i++)
    {
        slong m = m0 + i;
        arb_mul(t, z + i, f, wp);
        if (m % 2) arb_sub(c->part + b, c->part + b, t, wp); else arb_add(c->part + b, c->part + b, t, wp);
        arb_mul_si(f, f, XX * XX, wp); arb_div_ui(f, f, (2 * m + 2) * (2 * m + 3), wp);
    }
    _arb_vec_clear(z, num); arb_clear(f); arb_clear(t);
}

static void H_ref_zeta(arb_t res, slong prec, int threads)
{
    hzctx c;
    slong b;
    double l = 0;
    hl_params();
    for (c.M = 1; ; c.M++) { l += 2 * log2((double) XX) - log2(2.0 * c.M * (2 * c.M + 1)); if (l < -prec - 128) break; }
    c.M += 2;
    c.wp = prec + 64;
    c.nblocks = (c.M + HBLK - 1) / HBLK;
    c.part = _arb_vec_init(c.nblocks);
    parallel_for(c.nblocks, hz_block, &c, threads);
    arb_zero(res);
    for (b = 0; b < c.nblocks; b++) arb_add(res, res, c.part + b, c.wp);
    arb_add_error_2exp_si(res, -prec - 100);
    _arb_vec_clear(c.part, c.nblocks);
}

/* ======================= reference: Euler-Maclaurin =======================
   F(x) = sin(x0/x)/x; Taylor coefficients at M from the differential equation; int_M^oo F = Si(x0/M) */
typedef struct { ulong M; slong wp, nblocks; arb_ptr part; } hemctx;
#define HEMBLK 256
static void hem_block(slong b, void * vctx)
{
    hemctx * c = vctx;
    ulong k, k1 = 1 + b * HEMBLK, k2 = FLINT_MIN(c->M, k1 + HEMBLK);
    arb_t t; arb_init(t);
    arb_zero(c->part + b);
    for (k = k1; k < k2; k++)
    {
        arb_set_si(t, XX); arb_div_ui(t, t, k, c->wp); arb_sin(t, t, c->wp); arb_div_ui(t, t, k, c->wp);
        arb_add(c->part + b, c->part + b, t, c->wp);
    }
    arb_clear(t);
}

static void H_ref_em(arb_t res, slong prec, int threads)
{
    ulong M;
    slong wp = prec + 64, len, b;
    hemctx c;
    arb_t S, t;
    hl_params();
    M = em_cutoff(prec);
    len = em_length((double) M, prec) + 2;
    arb_init(S); arb_init(t);
    c.M = M; c.wp = wp; c.nblocks = (M - 1 + HEMBLK - 1) / HEMBLK; c.part = _arb_vec_init(c.nblocks);
    parallel_for(c.nblocks, hem_block, &c, threads);
    for (b = 0; b < c.nblocks; b++) arb_add(S, S, c.part + b, wp);
    _arb_vec_clear(c.part, c.nblocks);
    {
        /* x^4 F'' + 4 x^3 F' + (2 x^2 + x0^2) F = 0; F(M) = sin(x0/M)/M, F'(M) = -sin(x0/M)/M^2 - x0 cos(x0/M)/M^3 */
        fmpz_poly_t p2, p1, p0;
        arb_t f0, f1, sn, cs;
        ode_jet_t J; jet_stream_t js;
        fmpz_poly_init(p2); fmpz_poly_init(p1); fmpz_poly_init(p0);
        arb_init(f0); arb_init(f1); arb_init(sn); arb_init(cs);
        fmpz_poly_set_coeff_ui(p2, 4, 1); fmpz_poly_set_coeff_ui(p1, 3, 4);
        fmpz_poly_set_coeff_ui(p0, 2, 2); fmpz_poly_set_coeff_ui(p0, 0, XX * XX);
        arb_set_si(t, XX); arb_div_ui(t, t, M, wp + 32); arb_sin_cos(sn, cs, t, wp + 32);
        arb_div_ui(f0, sn, M, wp + 32);
        arb_div_ui(f1, f0, M, wp + 32); arb_neg(f1, f1);
        arb_mul_si(cs, cs, XX, wp + 32); arb_div_ui(cs, cs, M, wp + 32); arb_div_ui(cs, cs, M, wp + 32); arb_div_ui(cs, cs, M, wp + 32);
        arb_sub(f1, f1, cs, wp + 32);
        ode_jet_init(&J, p2, p1, p0, M, f0, f1, wp + 32);
        js.restart = ode_jet_restart; js.next = ode_jet_next; js.st = &J;
        em_bernoulli_stream(t, f0, &js, len, wp);
        arb_sub(S, S, t, wp);
        arb_mul_2exp_si(t, f0, -1); arb_add(S, S, t, wp);
        ode_jet_clear(&J);
        fmpz_poly_clear(p2); fmpz_poly_clear(p1); fmpz_poly_clear(p0);
        arb_clear(f0); arb_clear(f1); arb_clear(sn); arb_clear(cs);
    }
    arb_set_si(t, XX); arb_div_ui(t, t, M, wp); arb_hypgeom_si(t, t, wp);
    arb_add(res, S, t, prec);
    arb_clear(S); arb_clear(t);
}

const constant_t CONST_HL = {
    "hardy_littlewood", "Hardy-Littlewood function H(x) = sum_{k>=1} sin(x/k)/k at x = HOLSUM_HL_X (default 1)",
    hl_setup, hl_clear, H_dual, H_k, 1, H_finish, H_main, H_ref_zeta, H_ref_em, 1 };
