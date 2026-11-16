/*
    The constant of Theodorus T = sum_{k>=1} 1/((k+1) sqrt k) = 1.8600250792211903071806959157...
    (Section "The constant of Theodorus" of the paper): T = 1/2 + zeta_F(1/2; 2) with F(k) = 1/(k+1),
    f(x) = x/(1+x), a_n = (-1)^(n-1) (n >= 1), s = 1/2, split point u0 = 4^-a:

        zeta_F(1/2; 2) = sum_{k>=2} I_k + sqrt(pi) sum_{m>=1} J_m + M.

    k-side (x = k^2 u0): the geometric sums over n close, and
        I_k = [k^(1/2) Q(3/4, x) - k^(-1/2) Q(1/4, x) + e^-x C0]/(k^2 - 1),
        C0 = u0^(3/4) Phi_{3/4}/Gamma(7/4) - u0^(1/4) Phi_{1/4}/Gamma(5/4),  Phi_b = sum_i u0^i/(b+1)_i,
    two incomplete gamma functions per k.

    Dual side (c = pi^2 m^2): J_m = Z_{5/4}[G0](c) + Z_{3/4}[G1](c) with the kernel parts
        G1 = sum_j u^j/Gamma(j + 3/4) = Gh1/Gamma(3/4),      theta Gh1 = (u + 1/4) Gh1 - 1/4,
        G0 = -sum_j u^(j+1)/Gamma(j + 5/4) = -Gh0/Gamma(5/4), theta Gh0 = (u + 3/4) Gh0 + u/4,
    (G1 = e^u u^(1/4) P(-1/4, u) Gamma-normalized, an incomplete gamma function times e^u), evaluated by two
    moment systems of tsys.c with quarter-integer t0 (starting values from Gamma(3/4, y) and Gamma(1/4, y)).

    Main term (k0 = 2, the k = 1 term enters through P):
        M = sum_n a_n [sqrt(pi) u0^((n-1/2)/2)/((n-1/2) Gamma((n+1/2)/2)) - u0^((n+1/2)/2)/(2 Gamma((n+1/2)/2 + 1))
                       - P((n+1/2)/2, u0)],
    split by the parity of n into hypergeometric series in u0 (binary splitting).

    Reference (--method em): Euler-Maclaurin summation; F(x) = x^(-1/2)/(x+1) satisfies
    2x(x+1) F'' + (7x+3) F' + 3F = 0, and int_M^oo F = 2 arctan(1/sqrt M).
*/
#include <math.h>
#include <stdlib.h>
#include "tsys.h"

static arb_t TH_g14, TH_g34, TH_g54, TH_C0, TH_main, TH_sqrtpi;
static moment_sys_t TH_SA, TH_SB;
static int TH_done = 0;

/* ======================= hypergeometric series in u0 =======================
   sum_j w(j) u0^j/(beta)_j, beta = bq/4; w = 1, j + 1, 2/(4j+1) or 2/(4j+3) */
typedef struct { int bq, wt; } hs_ctx;

static void hs_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * v)
{
    const hs_ctx * c = v;
    ulong b = 4 * (ulong) n + c->bq, wn = 1, wd = 1;
    if (c->wt == 1) wn = n + 1;
    else if (c->wt == 2) { wn = 2; wd = 4 * n + 1; }
    else if (c->wt == 3) { wn = 2; wd = 4 * n + 3; }
    fmpz_mul_ui(q, U0_DEN, b); fmpz_mul_ui(q, q, wd);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, 4 * wd);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), U0_DEN, b); fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), fmpz_mat_entry(T, 1, 0), wn);
}

static void hsum(arb_t res, int bq, int wt, slong wp)
{
    hs_ctx c; bs_t B; arb_t x0;
    slong N = fact_terms(U0_D, wp) + 10;
    arb_init(x0); arb_one(x0);
    c.bq = bq; c.wt = wt;
    B.d = 1; B.s = 1; B.leaf = hs_leaf; B.ctx = &c;
    bs_eval(NULL, res, x0, 0, N, &B, wp);
    arb_clear(x0);
}

/* res = u0^(num/4) */
static void u0pow4(arb_t res, slong num, slong wp)
{
    fmpq_t e; fmpq_init(e); fmpq_set_si(e, num, 4);
    arb_pow_fmpq(res, U0, e, wp);
    fmpq_clear(e);
}

/* ======================= dual moment systems ======================= */

/* G_n = 1/(3/4)_n (system A) or 1/(5/4)_n (system B) */
static void cA_leaf(fmpz_mat_t M, fmpz_t q, slong n) { fmpz_set_ui(fmpz_mat_entry(M, 0, 0), 4); fmpz_set_ui(q, 4 * n + 3); }
static void cB_leaf(fmpz_mat_t M, fmpz_t q, slong n) { fmpz_set_ui(fmpz_mat_entry(M, 0, 0), 4); fmpz_set_ui(q, 4 * n + 5); }
static void c_init(fmpq * g) { fmpq_one(g); }
/* functions 0 = 1, 1 = Gh1 = sum G_n u^n */
static void cA_weight(fmpq * w, int f, slong n)
{
    if (f == 0) { if (n == 0) fmpq_one(w); }
    else fmpq_one(w);
}
/* functions 0 = 1, 1 = Gh0 = sum_{n>=1} G_{n-1} u^n, G_{n-1} = (n + 1/4) G_n */
static void cB_weight(fmpq * w, int f, slong n)
{
    if (f == 0) { if (n == 0) fmpq_one(w); }
    else if (n >= 1) fmpq_set_si(w, 4 * n + 1, 4);
}
static const coef_t COA = { 1, cA_leaf, c_init, cA_weight };
static const coef_t COB = { 1, cB_leaf, c_init, cB_weight };
/* theta Gh1 = u Gh1 + (1/4) Gh1 - (1/4) 1;  theta Gh0 = u Gh0 + (3/4) Gh0 + (1/4) u 1 */
static const tterm_t TTA[] = { {1, 1, 1, 4}, {1, 1, 0, 1}, {1, 0, 0, -1} };
static const tterm_t TTB[] = { {1, 1, 1, 4}, {1, 1, 0, 3}, {1, 0, 1, 1} };
static const tcomp_t TCA[] = { {1, 0, 0}, {1, -1, -1}, {0, 0, 0} };
static const tcomp_t TCB[] = { {1, 0, 0}, {1, -1, -1}, {0, 0, 0}, {0, -1, -1} };
static const int ILT[] = { 0, 0 };
/* nf, den, nterms, ncomp, twot0 (= 4 t0), R2, terms, comps, islog, co, tden */
static tsys_t TA = { 2, 4, 3, 3, 3, 1, TTA, TCA, ILT, &COA, 4 };
static tsys_t TB = { 2, 4, 3, 4, 5, 1, TTB, TCB, ILT, &COB, 4 };

/* ======================= setup ======================= */

static void theodorus_setup(slong prec)
{
    slong wp = prec + 64;
    arb_t s, t, u, e;
    fmpq_t a;
    if (TH_done) return;
    TH_done = 1;
    arb_init(TH_g14); arb_init(TH_g34); arb_init(TH_g54); arb_init(TH_C0); arb_init(TH_main); arb_init(TH_sqrtpi);
    arb_init(s); arb_init(t); arb_init(u); arb_init(e);
    fmpq_init(a);
    fmpq_set_si(a, 1, 4); arb_gamma_fmpq(TH_g14, a, prec + 256);
    fmpq_set_si(a, 3, 4); arb_gamma_fmpq(TH_g34, a, prec + 256);
    arb_mul_2exp_si(TH_g54, TH_g14, -2);                              /* Gamma(5/4) = Gamma(1/4)/4 */
    arb_const_sqrt_pi(TH_sqrtpi, wp);
    tsys_build(&TH_SA, &TA, prec);
    tsys_build(&TH_SB, &TB, prec);

    /* C0 = u0^(3/4) Phi_{3/4}/Gamma(7/4) - u0^(1/4) Phi_{1/4}/Gamma(5/4); Gamma(7/4) = (3/4) Gamma(3/4) */
    hsum(s, 7, 0, wp); u0pow4(t, 3, wp); arb_mul(s, s, t, wp);
    arb_mul_ui(t, TH_g34, 3, wp); arb_mul_2exp_si(t, t, -2); arb_div(TH_C0, s, t, wp);
    hsum(s, 5, 0, wp); u0pow4(t, 1, wp); arb_mul(s, s, t, wp); arb_div(s, s, TH_g54, wp);
    arb_sub(TH_C0, TH_C0, s, wp);

    /* M1 = sqrt(pi) [u0^(1/4)/Gamma(3/4) sum u0^m/((2m+1/2)(3/4)_m) - u0^(3/4)/Gamma(5/4) sum u0^j/((2j+3/2)(5/4)_j)] */
    hsum(s, 3, 2, wp); u0pow4(t, 1, wp); arb_mul(s, s, t, wp); arb_div(s, s, TH_g34, wp);
    hsum(u, 5, 3, wp); u0pow4(t, 3, wp); arb_mul(u, u, t, wp); arb_div(u, u, TH_g54, wp);
    arb_sub(s, s, u, wp); arb_mul(TH_main, s, TH_sqrtpi, wp);
    /* M2 = u0^(3/4)/(2 Gamma(7/4)) sum u0^m/(7/4)_m - u0^(5/4)/(2 Gamma(9/4)) sum u0^j/(9/4)_j,
       Gamma(9/4) = (5/4) Gamma(5/4) */
    hsum(s, 7, 0, wp); u0pow4(t, 3, wp); arb_mul(s, s, t, wp);
    arb_mul_ui(t, TH_g34, 3, wp); arb_mul_2exp_si(t, t, -2); arb_div(s, s, t, wp);
    hsum(u, 9, 0, wp); u0pow4(t, 5, wp); arb_mul(u, u, t, wp);
    arb_mul_ui(t, TH_g54, 5, wp); arb_mul_2exp_si(t, t, -2); arb_div(u, u, t, wp);
    arb_sub(s, s, u, wp); arb_mul_2exp_si(s, s, -1);
    arb_sub(TH_main, TH_main, s, wp);
    /* M3 = e^-u0 [u0^(3/4)/Gamma(7/4) sum (j+1) u0^j/(7/4)_j - u0^(5/4)/Gamma(9/4) sum (j+1) u0^j/(9/4)_j] */
    hsum(s, 7, 1, wp); u0pow4(t, 3, wp); arb_mul(s, s, t, wp);
    arb_mul_ui(t, TH_g34, 3, wp); arb_mul_2exp_si(t, t, -2); arb_div(s, s, t, wp);
    hsum(u, 9, 1, wp); u0pow4(t, 5, wp); arb_mul(u, u, t, wp);
    arb_mul_ui(t, TH_g54, 5, wp); arb_mul_2exp_si(t, t, -2); arb_div(u, u, t, wp);
    arb_sub(s, s, u, wp);
    arb_neg(e, U0); arb_exp(e, e, wp); arb_mul(s, s, e, wp);
    arb_sub(TH_main, TH_main, s, wp);

    arb_clear(s); arb_clear(t); arb_clear(u); arb_clear(e);
    fmpq_clear(a);
}

static void theodorus_clear(void)
{
    if (!TH_done) return;
    tsys_clear(&TH_SA, &TA); tsys_clear(&TH_SB, &TB);
    arb_clear(TH_g14); arb_clear(TH_g34); arb_clear(TH_g54); arb_clear(TH_C0); arb_clear(TH_main); arb_clear(TH_sqrtpi);
    TH_done = 0;
}

/* ======================= terms ======================= */

static void TH_k(arb_t res, slong idx, slong prec, void * ctx)
{
    ulong k = idx + 2, K = k * k;
    double x = K * U0_D;
    slong wp = kd_prec(-LOG2E * x, prec) + 2 * FLINT_BIT_COUNT(k) + 32;
    arb_t y, G, t, sk;
    fmpq_t a;
    arb_zero(res);
    if (wp < 64) return;
    arb_init(y); arb_init(G); arb_init(t); arb_init(sk); fmpq_init(a);
    arb_mul_ui(y, U0, K, ARF_PREC_EXACT);                 /* x = k^2 u0, exact */
    arb_sqrt_ui(sk, k, wp);
    fmpq_set_si(a, 3, 4); gamma_upper_fmpq_exact(G, a, y, TH_g34, wp);
    arb_div(G, G, TH_g34, wp); arb_mul(res, G, sk, wp);
    fmpq_set_si(a, 1, 4); gamma_upper_fmpq_exact(G, a, y, TH_g14, wp);
    arb_div(G, G, TH_g14, wp); arb_div(G, G, sk, wp); arb_sub(res, res, G, wp);
    arb_neg(t, y); arb_exp(t, t, wp); arb_addmul(res, t, TH_C0, wp);
    arb_div_ui(res, res, K - 1, wp);
    arb_clear(y); arb_clear(G); arb_clear(t); arb_clear(sk); fmpq_clear(a);
}

static void TH_dual(arb_t res, slong idx, slong prec, void * ctx)
{
    slong m = idx + 1;
    double cd = 9.8696044010893586 * m * m;
    slong wp = prec - (slong) (LOG2E * cd / U0_D) + 64;
    arb_t c, t; arb_ptr VA, VB;
    arb_zero(res);
    if (wp < 64) return;
    VA = _arb_vec_init(TH_SA.d); VB = _arb_vec_init(TH_SB.d);
    arb_init(c); arb_init(t);
    pi2c(c, (double) m, 2 * prec + 64);
    dual_state(VA, &TH_SA, c, wp);
    dual_state(VB, &TH_SB, c, wp);
    /* J = Z_{3/4}[Gh1]/Gamma(3/4) - Z_{5/4}[Gh0]/Gamma(5/4) */
    arb_div(res, VA + 0, TH_g34, wp);
    arb_div(t, VB + 0, TH_g54, wp);
    arb_sub(res, res, t, wp);
    arb_mul(res, res, TH_sqrtpi, wp);
    arb_clear(c); arb_clear(t); _arb_vec_clear(VA, TH_SA.d); _arb_vec_clear(VB, TH_SB.d);
}

static void TH_main_term(arb_t res) { arb_set(res, TH_main); }

static void TH_finish(arb_t res, const arb_t lin, slong prec)
{
    arb_set_d(res, 0.5); arb_add(res, res, lin, prec + 64);
}

static slong TH_kcount(slong prec)
{
    slong k;
    for (k = 2; ; k++) if (LOG2E * (double) k * k * U0_D > prec + 64) return k + 2;
}

static slong TH_dcount(slong prec)
{
    slong m;
    for (m = 1; ; m++) if (LOG2E * 9.8696044010893586 * m * m / U0_D > prec + 64) return m + 2;
}

/* ======================= reference: Euler-Maclaurin ======================= */

#define THEMBLK 512
typedef struct { ulong M; slong wp, nblocks; arb_ptr part; } them_ctx;

static void them_block(slong b, void * vctx)
{
    them_ctx * c = vctx;
    ulong k, k0 = 1 + (ulong) b * THEMBLK, k1 = FLINT_MIN(c->M, k0 + THEMBLK);
    arb_t t;
    arb_init(t);
    for (k = k0; k < k1; k++)
    {
        arb_rsqrt_ui(t, k, c->wp); arb_div_ui(t, t, k + 1, c->wp);
        arb_add(c->part + b, c->part + b, t, c->wp);
    }
    arb_clear(t);
}

static void TH_ref_em(arb_t res, slong prec, int threads)
{
    ulong M = em_cutoff(prec);
    slong wp = prec + 64, len, b;
    them_ctx c;
    arb_t S, t, f0, f1;
    fmpz_poly_t p2, p1, p0;
    ode_jet_t J; jet_stream_t js;
    len = em_length((double) M, prec) + 2;
    arb_init(S); arb_init(t); arb_init(f0); arb_init(f1);
    c.M = M; c.wp = wp; c.nblocks = (M - 1 + THEMBLK - 1) / THEMBLK; c.part = _arb_vec_init(c.nblocks);
    parallel_for(c.nblocks, them_block, &c, threads);
    for (b = 0; b < c.nblocks; b++) arb_add(S, S, c.part + b, wp);
    _arb_vec_clear(c.part, c.nblocks);
    /* 2x(x+1) F'' + (7x+3) F' + 3F = 0, F(M) = M^(-1/2)/(M+1), F'(M) = -F(M)(3M+1)/(2M(M+1)) */
    fmpz_poly_init(p2); fmpz_poly_init(p1); fmpz_poly_init(p0);
    fmpz_poly_set_coeff_ui(p2, 2, 2); fmpz_poly_set_coeff_ui(p2, 1, 2);
    fmpz_poly_set_coeff_ui(p1, 1, 7); fmpz_poly_set_coeff_ui(p1, 0, 3);
    fmpz_poly_set_coeff_ui(p0, 0, 3);
    arb_rsqrt_ui(f0, M, wp + 32); arb_div_ui(f0, f0, M + 1, wp + 32);
    arb_mul_ui(f1, f0, 3 * M + 1, wp + 32); arb_div_ui(f1, f1, 2 * M, wp + 32); arb_div_ui(f1, f1, M + 1, wp + 32);
    arb_neg(f1, f1);
    ode_jet_init(&J, p2, p1, p0, M, f0, f1, wp + 32);
    js.restart = ode_jet_restart; js.next = ode_jet_next; js.st = &J;
    em_bernoulli_stream(t, f0, &js, len, wp);
    arb_sub(S, S, t, wp);
    arb_mul_2exp_si(t, f0, -1); arb_add(S, S, t, wp);
    /* int_M^oo = 2 arctan(1/sqrt M) */
    arb_rsqrt_ui(t, M, wp); arb_atan(t, t, wp); arb_mul_2exp_si(t, t, 1);
    arb_add(res, S, t, prec);
    ode_jet_clear(&J);
    fmpz_poly_clear(p2); fmpz_poly_clear(p1); fmpz_poly_clear(p0);
    arb_clear(S); arb_clear(t); arb_clear(f0); arb_clear(f1);
}

const constant_t CONST_THEODORUS = {
    "theodorus", "the constant of Theodorus sum_{k>=1} 1/((k+1) sqrt k)",
    theodorus_setup, theodorus_clear, TH_dual, TH_k, 2, TH_finish, TH_main_term, NULL, TH_ref_em, 2,
    TH_kcount, TH_dcount, NULL };
