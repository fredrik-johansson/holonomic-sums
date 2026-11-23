/*
    The trace of Delta^{-3/2} for the Laplacian on the unit sphere S^2 (eigenvalues k(k+1), multiplicity 2k+1):

        S = Tr Delta^{-3/2} = sum_{k>=1} (2k+1)/(k(k+1))^{3/2} = 2.0705444763216059050931498281...

    (Section "Spectral sums and partition functions" of the paper). With y = k + 1/2 the summand is
        G(y) = 2y (y^2 - 1/4)^{-3/2} = 2 sum_{n>=0} c_n y^{-2n-2},   c_n = (3/2)_n/(n! 4^n),
    a hypergeometric function of y^{-2}, summed over the half-integers y >= 3/2. Its kernel in y^2 is
        h(u) = 2 sum_n G_n u^n = 2 1F1(3/2; 1; u/4),   G_n = c_n/n! = (3/2)_n/(n!^2 4^n),
    with theta^2 h = (u/4)(theta + 3/2) h. The theta function of the half-integer lattice,
        sum_{y in Z+1/2} e^{-y^2 u} = sqrt(pi/u) sum_{m in Z} (-1)^m e^{-pi^2 m^2/u},
    gives, with split point u0 = 4^-a,

        S = sum_{y>=3/2} I_y + M + sqrt(pi) sum_{m>=1} (-1)^m J_m,

    k-side (kappa = y^2, x = kappa u0, idx = k - 1, y = k + 1/2):
        I_y = int_{u0}^oo e^{-kappa u} h(u) du = 2 e^{-x} sum_n T_n e_n(x),  T_n = c_n kappa^{-n-1},
    with e_n(x) = sum_{i<=n} x^i/i!: a double series summed by binary splitting
    (state A_n = T_n e_n(x), B_n = T_n x^{n+1}/(n+1)!). The number of terms is chosen for absolute accuracy
    2^-prec (the working precision is reduced by the size e^{-(kappa - 1/4) u0} of the term).

    Dual side (c = pi^2 m^2): J_m = Z_{1/2}[h](c), from the moment system of (h/2, theta h/2) built by tsys.c,
    starting values from Gamma(1/2, y).

    Main term: M = int_0^{u0} h(u) (sqrt(pi/u)/2 - e^{-u/4}) du
                 = sqrt(pi) sum_n G_n u0^{n+1/2}/(n+1/2) - 2 u0 sum_n (-1/2)_n (-u0/4)^n/(n!^2 (n+1)),
    using e^{-u/4} h(u) = 2 1F1(-1/2; 1; -u/4) (Kummer).

    References: Euler-Maclaurin summation (--method em; F(x) = (2x+1)(x(x+1))^{-3/2} satisfies
    q F' = r F with q = 2x(x+1)(2x+1), r = -(8x^2 + 8x + 3), and int_M^oo F = 2 (M(M+1))^{-1/2}), and the
    zeta-value expansion (--method zeta) S = 2 sum_n c_n zeta(2n+2, 3/2), zeta(s, 3/2) = (2^s - 1) zeta(s) - 2^s.
*/
#include <math.h>
#include <stdlib.h>
#include "tsys.h"

static arb_t SP_main, SP_sqrtpi;
static moment_sys_t SP_S;
static int SP_done = 0;

/* ======================= main term: two hypergeometric series in u0 ======================= */

/* X_n = G_n u0^n, sum of 2 X_n/(2n+1) */
static void m1_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * v)
{
    fmpz_mul_ui(q, U0_DEN, 8 * (ulong) (n + 1) * (n + 1)); fmpz_mul_ui(q, q, 2 * n + 1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, (2 * n + 3) * (2 * n + 1));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), U0_DEN, 16 * (ulong) (n + 1) * (n + 1));
}

/* X_n = (-1/2)_n (-u0/4)^n/n!^2, sum of X_n/(n+1) */
static void m2_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * v)
{
    fmpz_mul_ui(q, U0_DEN, 8 * (ulong) (n + 1) * (n + 1) * (n + 1));
    fmpz_mul_si(fmpz_mat_entry(T, 0, 0), U0_NUM, -(slong) (2 * n - 1) * (n + 1));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), U0_DEN, 8 * (ulong) (n + 1) * (n + 1));
}

static void mseries(arb_t res, bs_leaf_fn leaf, slong wp)
{
    bs_t B; arb_t x0;
    slong N = fact_terms(U0_D, wp) + 10;
    arb_init(x0); arb_one(x0);
    B.d = 1; B.s = 1; B.leaf = leaf; B.ctx = NULL;
    bs_eval(NULL, res, x0, 0, N, &B, wp);
    arb_clear(x0);
}

/* ======================= dual moment system ======================= */

/* G_{n+1} = (2n+3)/(8(n+1)^2) G_n */
static void cS_leaf(fmpz_mat_t M, fmpz_t q, slong n)
{
    fmpz_set_ui(fmpz_mat_entry(M, 0, 0), 2 * n + 3);
    fmpz_set_ui(q, 8 * (ulong) (n + 1) * (n + 1));
}
static void cS_init(fmpq * g) { fmpq_one(g); }
/* functions 0 = h/2 = sum G_n u^n, 1 = theta(h/2) = sum n G_n u^n */
static void cS_weight(fmpq * w, int f, slong n)
{
    if (f == 0) fmpq_one(w);
    else fmpq_set_si(w, n, 1);
}
static const coef_t COS = { 1, cS_leaf, cS_init, cS_weight };
/* theta f0 = f1;  theta f1 = (1/4) u f1 + (3/8) u f0  (den = 8) */
static const tterm_t TTS[] = { {0, 1, 0, 8}, {1, 1, 1, 2}, {1, 0, 1, 3} };
static const tcomp_t TCS[] = { {0, 0, 0}, {1, 0, 0}, {0, -1, -1}, {1, -1, -1} };
static const int ILS[] = { 0, 0 };
/* nf, den, nterms, ncomp, twot0 (= 2 t0), R2, terms, comps, islog, co, tden */
static tsys_t TS = { 2, 8, 3, 4, 1, 1, TTS, TCS, ILS, &COS, 2 };

/* ======================= setup ======================= */

static void sphere_setup(slong prec)
{
    slong wp = prec + 64;
    arb_t s, t;
    if (SP_done) return;
    SP_done = 1;
    arb_init(SP_main); arb_init(SP_sqrtpi); arb_init(s); arb_init(t);
    arb_const_sqrt_pi(SP_sqrtpi, wp);
    tsys_build(&SP_S, &TS, prec);
    /* sqrt(pi) u0^(1/2) sum G_n u0^n/(n + 1/2) */
    mseries(s, m1_leaf, wp);
    arb_mul(s, s, SQRT_U0, wp); arb_mul(SP_main, s, SP_sqrtpi, wp);
    /* - 2 u0 sum (-1/2)_n (-u0/4)^n/(n!^2 (n+1)) */
    mseries(t, m2_leaf, wp);
    arb_mul(t, t, U0, wp); arb_mul_2exp_si(t, t, 1);
    arb_sub(SP_main, SP_main, t, wp);
    arb_clear(s); arb_clear(t);
}

static void sphere_clear(void)
{
    if (!SP_done) return;
    tsys_clear(&SP_S, &TS);
    arb_clear(SP_main); arb_clear(SP_sqrtpi);
    SP_done = 0;
}

/* ======================= k-terms ======================= */

typedef struct { ulong K2; } kS_ctx;   /* K2 = (2k+1)^2 = 4 kappa */

/* A_{n+1} = r (A_n + B_n), B_{n+1} = r x/(n+2) B_n, r = (2n+3)/(2(n+1) K2), x = K2 u0/4;
   common denominator q = 8 (n+1)(n+2) K2 u0den */
static void kS_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * v)
{
    const kS_ctx * c = v;
    fmpz_mul_ui(q, U0_DEN, 8 * (ulong) (n + 1) * (n + 2)); fmpz_mul_ui(q, q, c->K2);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_DEN, 4 * (ulong) (2 * n + 3) * (n + 2));
    fmpz_set(fmpz_mat_entry(T, 0, 1), fmpz_mat_entry(T, 0, 0));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), U0_NUM, (ulong) (2 * n + 3)); fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), c->K2);
    fmpz_set(fmpz_mat_entry(T, 2, 0), q);
}

static void SP_k(arb_t res, slong idx, slong prec, void * ctx)
{
    ulong k = idx + 1, K2 = (2 * k + 1) * (2 * k + 1);
    double kap = K2 / 4.0, x = kap * U0_D;
    slong wp = kd_prec(-LOG2E * (x - U0_D / 4), prec) + 2 * FLINT_BIT_COUNT(k) + 32, N;
    kS_ctx c; bs_t B;
    arb_t X0[2], s, ex;
    arb_zero(res);
    if (wp < 64) return;
    arb_init(X0[0]); arb_init(X0[1]); arb_init(s); arb_init(ex);
    c.K2 = K2;
    /* A_0 = 1/kappa = 4/K2, B_0 = u0 */
    arb_set_ui(X0[0], 4); arb_div_ui(X0[0], X0[0], K2, wp);
    arb_set(X0[1], U0);
    N = kseries_terms(1.0 / (4 * kap), x, prec) + 4;
    B.d = 2; B.s = 1; B.leaf = kS_leaf; B.ctx = &c;
    bs_eval(NULL, s, (arb_srcptr) X0, 0, N, &B, wp);
    /* I = 2 e^{-x} sum A_n */
    arb_mul_ui(ex, U0, K2, ARF_PREC_EXACT); arb_mul_2exp_si(ex, ex, -2);
    arb_neg(ex, ex); arb_exp(ex, ex, wp);
    arb_mul(res, s, ex, wp); arb_mul_2exp_si(res, res, 1);
    arb_clear(X0[0]); arb_clear(X0[1]); arb_clear(s); arb_clear(ex);
}

/* ======================= dual terms ======================= */

static void SP_dual(arb_t res, slong idx, slong prec, void * ctx)
{
    slong m = idx + 1;
    double cd = 9.8696044010893586 * m * m;
    slong wp = prec - (slong) (LOG2E * cd / U0_D) + 64;
    arb_t c; arb_ptr V;
    arb_zero(res);
    if (wp < 64) return;
    V = _arb_vec_init(SP_S.d);
    arb_init(c);
    pi2c(c, (double) m, 2 * prec + 64);
    dual_state(V, &SP_S, c, wp);
    /* sqrt(pi) (-1)^m J_m, J_m = Z_{1/2}[h] = 2 Z_{1/2}[h/2] */
    arb_mul(res, V + 0, SP_sqrtpi, wp);
    arb_mul_2exp_si(res, res, 1);
    if (m & 1) arb_neg(res, res);
    arb_clear(c); _arb_vec_clear(V, SP_S.d);
}

static void SP_main_term(arb_t res) { arb_set(res, SP_main); }

static void SP_finish(arb_t res, const arb_t lin, slong prec) { arb_set(res, lin); }

static slong SP_kcount(slong prec)
{
    slong k;
    for (k = 1; ; k++) if (LOG2E * ((k + 0.5) * (k + 0.5) - 0.25) * U0_D > prec + 64) return k + 2;
}

static slong SP_dcount(slong prec)
{
    slong m;
    for (m = 1; ; m++) if (LOG2E * 9.8696044010893586 * m * m / U0_D > prec + 64) return m + 2;
}

/* ======================= reference: Euler-Maclaurin ======================= */

#define SPEMBLK 512
typedef struct { ulong M; slong wp, nblocks; arb_ptr part; } spem_ctx;

/* F(k) = (2k+1) (k(k+1))^{-3/2} */
static void sp_F(arb_t t, ulong k, slong wp)
{
    arb_t u; arb_init(u);
    arb_set_ui(u, k); arb_mul_ui(u, u, k + 1, wp);
    arb_rsqrt(t, u, wp); arb_pow_ui(t, t, 3, wp); arb_mul_ui(t, t, 2 * k + 1, wp);
    arb_clear(u);
}

static void spem_block(slong b, void * vctx)
{
    spem_ctx * c = vctx;
    ulong k, k0 = 1 + (ulong) b * SPEMBLK, k1 = FLINT_MIN(c->M, k0 + SPEMBLK);
    arb_t t;
    arb_init(t);
    for (k = k0; k < k1; k++) { sp_F(t, k, c->wp); arb_add(c->part + b, c->part + b, t, c->wp); }
    arb_clear(t);
}

static void SP_ref_em(arb_t res, slong prec, int threads)
{
    ulong M = em_cutoff(prec);
    slong wp = prec + 64, len, b;
    spem_ctx c;
    arb_t S, t, f0, f1;
    fmpz_poly_t p2, p1, p0;
    ode_jet_t J; jet_stream_t js;
    len = em_length((double) M, prec) + 2;
    arb_init(S); arb_init(t); arb_init(f0); arb_init(f1);
    c.M = M; c.wp = wp; c.nblocks = (M - 1 + SPEMBLK - 1) / SPEMBLK; c.part = _arb_vec_init(c.nblocks);
    parallel_for(c.nblocks, spem_block, &c, threads);
    for (b = 0; b < c.nblocks; b++) arb_add(S, S, c.part + b, wp);
    _arb_vec_clear(c.part, c.nblocks);
    /* q F'' + (q' - r) F' - r' F = 0 with q = 4x^3 + 6x^2 + 2x, r = -(8x^2 + 8x + 3):
       p2 = 4x^3 + 6x^2 + 2x, p1 = 20x^2 + 20x + 5, p0 = 16x + 8 */
    fmpz_poly_init(p2); fmpz_poly_init(p1); fmpz_poly_init(p0);
    fmpz_poly_set_coeff_ui(p2, 3, 4); fmpz_poly_set_coeff_ui(p2, 2, 6); fmpz_poly_set_coeff_ui(p2, 1, 2);
    fmpz_poly_set_coeff_ui(p1, 2, 20); fmpz_poly_set_coeff_ui(p1, 1, 20); fmpz_poly_set_coeff_ui(p1, 0, 5);
    fmpz_poly_set_coeff_ui(p0, 1, 16); fmpz_poly_set_coeff_ui(p0, 0, 8);
    sp_F(f0, M, wp + 32);
    /* F'(M) = F(M) r(M)/q(M) */
    {
        fmpz_t rr, qq; fmpz_init(rr); fmpz_init(qq);
        fmpz_set_ui(rr, M); fmpz_mul_ui(rr, rr, M + 1); fmpz_mul_ui(rr, rr, 8); fmpz_add_ui(rr, rr, 3); fmpz_neg(rr, rr);
        fmpz_set_ui(qq, M); fmpz_mul_ui(qq, qq, M + 1); fmpz_mul_ui(qq, qq, 2 * M + 1); fmpz_mul_ui(qq, qq, 2);
        arb_mul_fmpz(f1, f0, rr, wp + 32); arb_div_fmpz(f1, f1, qq, wp + 32);
        fmpz_clear(rr); fmpz_clear(qq);
    }
    ode_jet_init(&J, p2, p1, p0, M, f0, f1, wp + 32);
    js.restart = ode_jet_restart; js.next = ode_jet_next; js.st = &J;
    em_bernoulli_stream(t, f0, &js, len, wp);
    arb_sub(S, S, t, wp);
    arb_mul_2exp_si(t, f0, -1); arb_add(S, S, t, wp);
    /* int_M^oo F = 2 (M(M+1))^{-1/2} */
    arb_set_ui(t, M); arb_mul_ui(t, t, M + 1, wp); arb_rsqrt(t, t, wp); arb_mul_2exp_si(t, t, 1);
    arb_add(res, S, t, prec);
    ode_jet_clear(&J);
    fmpz_poly_clear(p2); fmpz_poly_clear(p1); fmpz_poly_clear(p0);
    arb_clear(S); arb_clear(t); arb_clear(f0); arb_clear(f1);
}

/* ======================= reference: zeta-value expansion ======================= */

static void SP_ref_zeta(arb_t res, slong prec, int threads)
{
    slong N = (slong) ((prec + 64) / log2(9.0)) + 16, wp = prec + 64 + FLINT_BIT_COUNT(N), n;
    arb_ptr z = _arb_vec_init(N);
    arb_t c, t, p2, sum;
    arb_init(c); arb_init(t); arb_init(p2); arb_init(sum);
    zeta_vec_mixed(z, 2, 2, N, wp);          /* zeta(2), zeta(4), ..., zeta(2N) */
    arb_one(c);
    for (n = 0; n < N; n++)
    {
        /* zeta(2n+2, 3/2) = 2^(2n+2) (zeta(2n+2) - 1) - zeta(2n+2) */
        arb_sub_ui(t, z + n, 1, wp); arb_mul_2exp_si(t, t, 2 * n + 2); arb_sub(t, t, z + n, wp);
        arb_addmul(sum, c, t, wp);
        arb_mul_ui(c, c, 2 * n + 3, wp); arb_div_ui(c, c, 8 * (n + 1), wp);
    }
    arb_mul_2exp_si(res, sum, 1);
    arb_set_round(res, res, prec);
    arb_clear(c); arb_clear(t); arb_clear(p2); arb_clear(sum);
    _arb_vec_clear(z, N);
}

const constant_t CONST_SPHERE = {
    "sphere", "trace of Delta^(-3/2) for the Laplacian on the unit sphere S^2, sum_{k>=1} (2k+1)/(k(k+1))^(3/2)",
    sphere_setup, sphere_clear, SP_dual, SP_k, 1, SP_finish, SP_main_term, SP_ref_zeta, SP_ref_em, 2,
    SP_kcount, SP_dcount, NULL };
