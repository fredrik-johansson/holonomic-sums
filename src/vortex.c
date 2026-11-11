/*
    Velocity induced in a periodic array of coaxial thin-cored vortex rings (spacing lambda times the radius)
    by all the other rings (Vasilev 1916, Levy-Forsdyke 1928; Masroor-Stremler 2022, eq. 3.6):

      U(lambda) = (1/2pi) sum_{n>=1} int_0^{2pi} (1 - cos phi) / (2(1 - cos phi) + n^2 lambda^2)^{3/2} dphi
                = lambda^-3 sum_{n>=1} n^-3 2F1(3/2, 3/2; 2; -beta/n^2),     beta = 4/lambda^2,

    for lambda = 2/s with integer s (environment variable HOLSUM_VORTEX_S, default 2, i.e. lambda = 1).
    Kernel u^{1/2} 1F1(3/2; 2; -beta u); dual moments Z_0 with E1 starting values; the k-side series
    converge for n^2 > beta, and the terms n^2 <= 2 beta are computed as the full integral (a 2F1 by
    Pfaff's transformation) minus the integral over [0, u0]. See the paper for the formulas.
*/
#include <math.h>
#include <stdlib.h>
#include "constants.h"

static slong BETA = 4;        /* beta = s^2 */
static slong SPAR = 2;
static slong K0;              /* k-side series for n >= K0 (n^2 >= 2 beta + 1) */

/* ---------------- k-side, n >= K0: state (B, C, A), sums (B, A) ---------------- */
typedef struct { ulong K; } kctx;
static void k_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    ulong K = ((const kctx *) v)->K;
    ulong o = 2 * j + 3;
    fmpz_t a, b; fmpz_init(a); fmpz_init(b);
    fmpz_set_si(a, -BETA); fmpz_mul_ui(a, a, o * o); fmpz_mul(a, a, U0_DEN);          /* -beta o^2 U0_DEN */
    fmpz_set_si(b, -2 * BETA); fmpz_mul_ui(b, b, o); fmpz_mul_ui(b, b, K); fmpz_mul(b, b, U0_NUM);   /* -2 beta o K U0_NUM */
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), b);
    fmpz_set(fmpz_mat_entry(T, 1, 1), b);
    fmpz_set(fmpz_mat_entry(T, 2, 2), a);
    fmpz_set_ui(q, 4 * (ulong) (j + 1) * (j + 2)); fmpz_mul_ui(q, q, K); fmpz_mul(q, q, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 3, 0), q);
    fmpz_set(fmpz_mat_entry(T, 4, 2), q);
    fmpz_clear(a); fmpz_clear(b);
}

/* number of terms and log2 of the largest term of e^-x sqrt(x) A_j R_j (relative to 1) */
static slong k_terms(ulong K, slong prec, double * lmax)
{
    double x = K * U0_D, lA = 0, lr = 1.0 - 0.5 * log2(M_PI) + 1, lR, lt, lx = log2(x);
    slong j;
    lR = lr;            /* R_0 = r_0 = 2/sqrt(pi) (times the 2/sqrt(pi) normalization; harmless) */
    *lmax = -1e300;
    for (j = 0; ; j++)
    {
        lt = lA + lR - 1.4426950408889634 * x + 0.5 * lx;
        if (lt > *lmax) *lmax = lt;
        if (j > x + 10 && lt < -prec - 64) return j + 2;
        lA += log2((double) BETA * (2 * j + 3) * (2 * j + 3) / (4.0 * (j + 1) * (j + 2) * K));
        lr += lx + 1 - log2(2.0 * j + 3);
        lR = (lr > lR) ? lr + log2(1 + pow(2.0, lR - lr)) : lR + log2(1 + pow(2.0, lr - lR));
    }
}

static void k_term(arb_t res, ulong n, slong prec)
{
    ulong K = n * n;
    kctx kc; bs_t B; arb_ptr x0 = _arb_vec_init(3), s = _arb_vec_init(2);
    arb_t x, ex, G, t;
    double lmax;
    slong N = k_terms(K, prec, &lmax), wp;
    wp = prec + 64 + (slong) lmax;
    if (wp < 64) { arb_zero(res); _arb_vec_clear(x0, 3); _arb_vec_clear(s, 2); return; }
    arb_init(x); arb_init(ex); arb_init(G); arb_init(t);
    kc.K = K;
    B.d = 3; B.s = 2; B.leaf = k_leaf; B.ctx = &kc;
    arb_one(x0 + 0); arb_one(x0 + 1); arb_one(x0 + 2);
    bs_eval(NULL, s, x0, 0, N, &B, wp + 32);
    arb_mul_ui(x, U0, K, ARF_PREC_EXACT);
    arb_neg(ex, x); arb_exp(ex, ex, wp + 32);
    arb_sqrt(t, x, wp + 32); arb_mul(t, t, ex, wp + 32); arb_mul(t, t, s + 0, wp + 32); arb_mul_2exp_si(t, t, 1);
    gamma_upper_exact(G, 1, x, wp + 32);
    arb_addmul(t, G, s + 1, wp + 32);
    /* times (1/2) K^-3/2 = 1/(2 n^3) */
    arb_div_ui(t, t, n, wp + 32); arb_div_ui(t, t, K, wp + 32); arb_mul_2exp_si(res, t, -1);
    _arb_vec_clear(x0, 3); _arb_vec_clear(s, 2);
    arb_clear(x); arb_clear(ex); arb_clear(G); arb_clear(t);
}

/* ---------------- n < K0: T_n - L_n ---------------- */
typedef struct { ulong K; } sctx;
/* 2F1(3/2,1/2;2;w), w = beta/(beta+K): t_{j+1}/t_j = (2j+3)(2j+1) beta / (4 (j+1)(j+2)(beta+K)) */
static void g_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    ulong K = ((const sctx *) v)->K;
    fmpz_set_ui(q, 4 * (ulong) (j + 1) * (j + 2)); fmpz_mul_ui(q, q, BETA + K);
    fmpz_set_ui(fmpz_mat_entry(T, 0, 0), (ulong) (2 * j + 3) * (2 * j + 1)); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), BETA);
    fmpz_set(fmpz_mat_entry(T, 1, 0), q);
}
/* L: G_j = g_j U0^j, g = y e^{-K u}: (n+1)(n+2) G_{n+1} = -U0 (2K(n+1) + beta(n+3/2)) G_n - U0^2 K (K+beta) G_{n-1};
   state (G_n, G_{n-1}), sum 2 G_n/(2n+3) */
static void l_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * v)
{
    ulong K = ((const sctx *) v)->K;
    ulong o = 2 * n + 3;
    fmpz_t D0, t; fmpz_init(D0); fmpz_init(t);
    fmpz_set_ui(D0, 2 * (ulong) (n + 1) * (n + 2)); fmpz_mul(D0, D0, U0_DEN); fmpz_mul(D0, D0, U0_DEN);
    fmpz_mul_ui(q, D0, o);
    fmpz_set_ui(t, 4 * K * (n + 1) + BETA * o); fmpz_mul(t, t, U0_NUM); fmpz_mul(t, t, U0_DEN); fmpz_mul_ui(t, t, o); fmpz_neg(t, t);
    fmpz_set(fmpz_mat_entry(T, 0, 0), t);
    fmpz_mul(t, U0_NUM, U0_NUM); fmpz_mul_ui(t, t, 2 * K * (K + BETA)); fmpz_mul_ui(t, t, o); fmpz_neg(t, t);
    fmpz_set(fmpz_mat_entry(T, 0, 1), t);
    fmpz_set(fmpz_mat_entry(T, 1, 0), q);
    fmpz_mul_2exp(fmpz_mat_entry(T, 2, 0), D0, 1);
    fmpz_clear(D0); fmpz_clear(t);
}

static void small_term(arb_t res, ulong n, slong prec)
{
    ulong K = n * n;
    sctx sc; bs_t B; arb_ptr x0 = _arb_vec_init(2), s = _arb_vec_init(1);
    arb_t T, L, t;
    slong wp = prec + 64, N;
    double w = (double) BETA / (BETA + K);
    arb_init(T); arb_init(L); arb_init(t);
    sc.K = K;
    /* T_n */
    N = (slong) ((wp + 64) / -log2(w)) + 20;
    B.d = 1; B.s = 1; B.leaf = g_leaf; B.ctx = &sc;
    arb_one(x0 + 0);
    bs_eval(NULL, s, x0, 0, N, &B, wp);
    arb_set_ui(t, K + BETA); arb_rsqrt(t, t, wp); arb_pow_ui(t, t, 3, wp);
    arb_mul(T, s + 0, t, wp);
    arb_const_sqrt_pi(t, wp); arb_mul(T, T, t, wp); arb_mul_2exp_si(T, T, -1);
    /* L_n: magnitudes by the recurrence in doubles */
    {
        /* g0, g1 scaled by 2^lsc to avoid underflow */
        double g0 = 1, g1 = 0, gn, lmax = 0, a, b, lsc = 0, lg; slong m;
        for (m = 0; ; m++)
        {
            a = U0_D * (2.0 * K * (m + 1) + BETA * (m + 1.5)); b = U0_D * U0_D * K * (K + BETA);
            gn = (a * g0 + b * g1) / ((m + 1.0) * (m + 2.0));
            g1 = g0; g0 = gn;
            if (g0 < 1e-100) { g0 *= 1e100; g1 *= 1e100; lsc -= 100 * log2(10.0); }
            lg = log2(g0) + lsc;
            if (lg > lmax) lmax = lg;
            if (m > 20 && lg < -wp - 64 - lmax) break;
        }
        N = m + 10;
        wp += (slong) lmax;
    }
    B.d = 2; B.s = 1; B.leaf = l_leaf; B.ctx = &sc;
    arb_one(x0 + 0); arb_zero(x0 + 1);
    bs_eval(NULL, s, x0, 0, N, &B, wp);
    arb_sqrt(t, U0, wp); arb_mul(t, t, U0, wp);
    arb_mul(L, s + 0, t, wp);
    arb_sub(res, T, L, prec + 64);
    _arb_vec_clear(x0, 2); _arb_vec_clear(s, 1);
    arb_clear(T); arb_clear(L); arb_clear(t);
}

/* ---------------- dual system ---------------- */
/* state (c^j P_j, c^j Q_j, c^{j-1} P_{j-1}, c^{j-1} Q_{j-1}), P_t = Z_t[y], Q_t = Z_t[theta y], t0 = 0:
   c P_{t+1} = E U0^{1-t} y(U0) - (1-t) P_t - Q_t
   c Q_{t+1} = E U0^{1-t} (theta y)(U0) + t Q_t + beta Q_{t-1} + (3 beta/2) P_{t-1}
   amat writes 2 D A(l) with c0 = C/D */
static void amatV(fmpz * A, slong l, const fmpz_t C, const fmpz_t D)
{
    fmpz_mul_si(A + 0, D, 2 * (l - 1)); fmpz_mul_si(A + 1, D, -2);
    fmpz_mul_si(A + 5, D, 2 * l); fmpz_mul_si(A + 6, C, 3 * BETA); fmpz_mul_si(A + 7, C, 2 * BETA);
    fmpz_mul_si(A + 8, D, 2);
    fmpz_mul_si(A + 13, D, 2);
}

/* starting values: y_j alpha_{j+1} =: A_j, y_j beta_{j+1} =: B_j, y_j U0^{j+2} =: U_j with
   D_s = alpha_s E1(c/U0) + beta_s E, alpha_s = (-c)^s/s!, beta_s = (U0^s - c beta_{s-1})/s.
   sums: A (1, j, 1/(j+2), j/(j+2)), B (same), U (1/(j+2), j/(j+2)) */
/* c0, E = e^{-c0/U0}, base = Gamma(a, c0/U0) (a = 1/2 or 0); W = wp + 1.44 c/U0 + 6 sqrt(c) + 64 */
static void v_init_common(arb_t c, arb_t E, arb_t base, int half, const fmpz_t C, slong e, slong wp, slong * W, slong * N)
{
    arb_t y; double cd;
    arb_init(y);
    arb_set_fmpz(c, C); arb_mul_2exp_si(c, c, -e);
    cd = arf_get_d(arb_midref(c), ARF_RND_NEAR);
    *W = wp + (slong) (1.4427 * cd / U0_D + 6 * sqrt(BETA * cd)) + 64;
    *N = 0;
    arb_mul_fmpz(y, c, U0_DEN, ARF_PREC_EXACT); arb_div_fmpz(y, y, U0_NUM, *W);
    arb_neg(E, y); arb_exp(E, E, wp + 64);
    gamma_upper_exact(base, half, y, wp + 64);
    arb_clear(y);
}

typedef struct { fmpz_t C, D; } ictx;
static void i_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    const ictx * c = v;
    ulong o = 2 * j + 3, j1 = j + 1, j2 = j + 2;
    fmpz_t t; fmpz_init(t);
    fmpz_set_ui(q, 2 * j1 * j2 * j2); fmpz_mul(q, q, c->D); fmpz_mul(q, q, U0_DEN);
    fmpz_mul_ui(t, c->C, BETA * o); fmpz_mul(t, t, U0_DEN);                     /* beta o C U0_DEN */
    fmpz_set(fmpz_mat_entry(T, 0, 0), t); fmpz_set(fmpz_mat_entry(T, 1, 1), t);
    fmpz_mul_ui(t, c->D, BETA * o); fmpz_mul(t, t, U0_DEN); fmpz_neg(t, t);     /* -beta o D U0_DEN */
    fmpz_set(fmpz_mat_entry(T, 1, 2), t);
    fmpz_mul_ui(t, c->D, BETA * o * j2); fmpz_mul(t, t, U0_NUM); fmpz_neg(t, t); /* -beta o (j+2) D U0_NUM */
    fmpz_set(fmpz_mat_entry(T, 2, 2), t);
    /* sums */
    fmpz_divexact_ui(t, q, j2);
    fmpz_set(fmpz_mat_entry(T, 3, 0), q); fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), q, j);
    fmpz_set(fmpz_mat_entry(T, 5, 0), t); fmpz_mul_ui(fmpz_mat_entry(T, 6, 0), t, j);
    fmpz_set(fmpz_mat_entry(T, 7, 1), q); fmpz_mul_ui(fmpz_mat_entry(T, 8, 1), q, j);
    fmpz_set(fmpz_mat_entry(T, 9, 1), t); fmpz_mul_ui(fmpz_mat_entry(T, 10, 1), t, j);
    fmpz_set(fmpz_mat_entry(T, 11, 2), t); fmpz_mul_ui(fmpz_mat_entry(T, 12, 2), t, j);
    fmpz_clear(t);
}

static void initV(arb_ptr V, arb_t E, const fmpz_t C, slong e, slong wp, const void * sys)
{
    ictx ic; bs_t B; arb_t c, B1, t; arb_ptr x0 = _arb_vec_init(3), s = _arb_vec_init(10);
    slong W, N, j;
    double cd, la;
    arb_init(c); arb_init(B1); arb_init(t);
    v_init_common(c, E, B1, 0, C, e, wp, &W, &N);     /* B1 = E1(c/U0) */
    cd = arf_get_d(arb_midref(c), ARF_RND_NEAR);
    /* terms: the alpha part ~ (beta c)^j/(j!)^2; the beta part ~ y_j U0^{j+1}/(j+1) ~ (beta U0)^j/j!
       (since D_s ~ E U0^s/s for large s), which decays more slowly */
    la = 0;
    {
        double lb = 0;
        for (j = 1; ; j++)
        {
            la += log2(BETA * (cd + 1) + 1) - 2 * log2((double) j) + 3;
            lb += log2(BETA * U0_D) - log2((double) j) + 2;
            if (j > 10 && la < -W - 64 && lb < -W - 64) break;
        }
    }
    N = j + 10;
    fmpz_init_set(ic.C, C); fmpz_init(ic.D); fmpz_one(ic.D); fmpz_mul_2exp(ic.D, ic.D, e);
    B.d = 3; B.s = 10; B.leaf = i_leaf; B.ctx = &ic;
    arb_neg(x0 + 0, c); arb_set(x0 + 1, U0); arb_sqr(x0 + 2, U0, W);
    bs_eval(NULL, s, x0, 0, N, &B, W);
    /* P_0 = B1 SA + E SB; Q_0 = B1 SjA + E SjB */
    arb_mul(V + 0, B1, s + 0, W); arb_addmul(V + 0, E, s + 4, W);
    arb_mul(V + 1, B1, s + 1, W); arb_addmul(V + 1, E, s + 5, W);
    /* P_{-1} = -c B1 S_{A/(j+2)} + E (S_{U/(j+2)} - c S_{B/(j+2)}), stored / c */
    arb_mul(V + 2, B1, s + 2, W); arb_mul(V + 2, V + 2, c, W); arb_neg(V + 2, V + 2);
    arb_mul(t, c, s + 6, W); arb_sub(t, s + 8, t, W); arb_addmul(V + 2, E, t, W); arb_div(V + 2, V + 2, c, W);
    arb_mul(V + 3, B1, s + 3, W); arb_mul(V + 3, V + 3, c, W); arb_neg(V + 3, V + 3);
    arb_mul(t, c, s + 7, W); arb_sub(t, s + 9, t, W); arb_addmul(V + 3, E, t, W); arb_div(V + 3, V + 3, c, W);
    _arb_vec_clear(x0, 3); _arb_vec_clear(s, 10); arb_clear(c); arb_clear(B1); arb_clear(t);
    fmpz_clear(ic.C); fmpz_clear(ic.D);
}

/* ---------------- setup: y-series at U0, main term ---------------- */
static moment_sys_t SV;
static arb_t MAIN;
/* Y_j = y_j U0^j; sums Y, j Y, Y/(j+1), 2Y/(2j+3) */
static void y_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    ulong o = 2 * j + 3;
    fmpz_set_ui(q, 2 * (ulong) (j + 1) * (j + 2) * o); fmpz_mul(q, q, U0_DEN);
    fmpz_set_si(fmpz_mat_entry(T, 0, 0), -BETA); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), o * o);
    fmpz_mul(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), U0_NUM);
    fmpz_set(fmpz_mat_entry(T, 1, 0), q);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), q, j);
    fmpz_divexact_ui(fmpz_mat_entry(T, 3, 0), q, j + 1);
    fmpz_divexact_ui(fmpz_mat_entry(T, 4, 0), q, o); fmpz_mul_2exp(fmpz_mat_entry(T, 4, 0), fmpz_mat_entry(T, 4, 0), 1);
}

static void vortex_setup(slong prec)
{
    const char * es = getenv("HOLSUM_VORTEX_S");
    if (es != NULL) SPAR = atol(es);
    BETA = SPAR * SPAR;
    for (K0 = 1; K0 * K0 <= 2 * BETA; K0++) ;
    slong wp = prec + 64, N;
    bs_t B; arb_ptr X0 = _arb_vec_init(1), R = _arb_vec_init(4);
    arb_t t, sp;
    double lg = 0;
    arb_init(t); arb_init(sp);
    for (N = 1; lg > -(double) (wp + 40); N++) lg += log2(BETA * U0_D) - log2((double) N) + 1;
    N += 10;
    B.d = 1; B.s = 4; B.leaf = y_leaf; B.ctx = NULL;
    arb_one(X0 + 0);
    bs_eval(NULL, R, X0, 0, N, &B, wp);
    SV.kappa = _arb_vec_init(2);
    arb_set(SV.kappa + 0, R + 0); arb_set(SV.kappa + 1, R + 1);
    /* M = (sqrt(pi)/2) U0 sum Y/(j+1) - (1/2) U0^{3/2} sum 2Y/(2j+3) */
    arb_const_sqrt_pi(sp, wp);
    arb_init(MAIN);
    arb_mul(MAIN, R + 2, U0, wp); arb_mul(MAIN, MAIN, sp, wp);
    arb_mul(t, R + 3, U0, wp); arb_mul(t, t, SQRT_U0, wp); arb_sub(MAIN, MAIN, t, wp);
    arb_mul_2exp_si(MAIN, MAIN, -1);
    SV.d = 4; SV.ng = 2; SV.amat = amatV; SV.init = initV; SV.t0 = 0;
    SV.fsel[0] = 0; SV.fsel[1] = 1; SV.fsel[2] = -1; SV.fsel[3] = -1;
    SV.lag[0] = 0; SV.lag[1] = 0; SV.lag[2] = -1; SV.lag[3] = -1;
    arb_init(SV.f0scale); arb_set(SV.f0scale, U0);
    _arb_vec_clear(X0, 1); _arb_vec_clear(R, 4); arb_clear(t); arb_clear(sp);
}


static void vortex_clear(void) { moment_sys_clear(&SV); arb_clear(MAIN); }

static void V_dual(arb_t res, slong idx, slong prec, void * ctx)
{
    slong m = idx + 1, wp = dual_term_prec(m, prec);
    arb_t c, sp; arb_ptr V;
    arb_zero(res);
    if (wp < 64) return;
    /* the moment recurrences lose about sqrt(beta c) bits to cancellation */
    wp += (slong) (3 * sqrt(BETA * 9.8696044010893586 * m * m)) + 32;
    V = _arb_vec_init(SYS_MAXD);
    arb_init(c); arb_init(sp);
    arb_const_pi(c, 2 * prec + 64); arb_mul_ui(c, c, m, 2 * prec + 64); arb_sqr(c, c, 2 * prec + 64);
    arb_const_sqrt_pi(sp, wp + 64);
    dual_state(V, &SV, c, wp);
    arb_mul(res, V + 0, sp, wp);
    arb_clear(c); arb_clear(sp); _arb_vec_clear(V, SYS_MAXD);
}

static void V_k(arb_t res, slong idx, slong prec, void * ctx)
{
    ulong n = idx + 1;
    if (n < (ulong) K0) small_term(res, n, prec); else k_term(res, n, prec);
}

static void V_main(arb_t res) { arb_set(res, MAIN); }

/* U = 2 Sigma / (sqrt(pi) lambda^3) = Sigma s^3 / (4 sqrt(pi)) */
static void V_finish(arb_t res, const arb_t lin, slong prec)
{
    arb_t t; arb_init(t);
    arb_const_sqrt_pi(t, prec + 64);
    arb_mul_ui(res, lin, SPAR * SPAR * SPAR, prec + 64); arb_div(res, res, t, prec); arb_mul_2exp_si(res, res, -2);
    arb_clear(t);
}

/* n^-3 2F1(3/2,3/2;2;-beta/n^2) = (n^2 + beta)^{-3/2} 2F1(3/2, 1/2; 2; beta/(beta + n^2)) */
static void vortex_direct_term(arb_t res, ulong n, slong wp)
{
    arb_t a, b, c, z, t;
    arb_init(a); arb_init(b); arb_init(c); arb_init(z); arb_init(t);
    arb_set_ui(z, BETA); arb_div_ui(z, z, BETA + n * n, wp);
    arb_set_d(a, 1.5); arb_set_d(b, 0.5); arb_set_ui(c, 2);
    arb_hypgeom_2f1(res, a, b, c, z, 0, wp);
    arb_set_ui(t, BETA + n * n); arb_rsqrt(t, t, wp); arb_pow_ui(t, t, 3, wp);
    arb_mul(res, res, t, wp);
    arb_clear(a); arb_clear(b); arb_clear(c); arb_clear(z); arb_clear(t);
}

/* lambda^-3 = s^3/8 */
static void mul_lambda3(arb_t res, const arb_t x, slong prec)
{
    arb_mul_ui(res, x, SPAR * SPAR * SPAR, prec); arb_mul_2exp_si(res, res, -3);
}

/* ======================= reference: zeta-value expansion =======================
   U = lambda^-3 [ sum_{n<=KS} n^-3 F(-beta/n^2) + sum_j a_j (-beta)^j (zeta(2j+3) - sum_{n<=KS} n^-(2j+3)) ],
   a_j = (3/2)_j^2/((2)_j j!) */
#define VKS 31
#define VBLK 128
typedef struct { slong J, wp, nblocks; arb_ptr a0, part; } vzctx;

static void vz_block(slong b, void * vctx)
{
    vzctx * c = vctx;
    slong j0 = b * VBLK, num = FLINT_MIN(VBLK, c->J - j0), i, n;
    slong wp = c->wp;
    arb_ptr z; arb_t a, pn, in;
    if (num <= 0) return;
    z = _arb_vec_init(num); arb_init(a); arb_init(pn); arb_init(in);
    zeta_vec_mixed(z, 2 * j0 + 3, 2, num, wp);
    for (i = 0; i < num; i++) arb_sub_ui(z + i, z + i, 1, wp);
    for (n = 2; n <= VKS; n++)
    {
        if ((2 * j0 + 3) * log2((double) n) > wp + 20) break;
        arb_ui_pow_ui(pn, n, 2 * j0 + 3, wp); arb_inv(pn, pn, wp);
        arb_set_ui(in, n * n); arb_inv(in, in, wp);
        for (i = 0; i < num; i++)
        {
            if ((2 * (j0 + i) + 3) * log2((double) n) > wp + 20) break;
            arb_sub(z + i, z + i, pn, wp); arb_mul(pn, pn, in, wp);
        }
    }
    arb_set(a, c->a0 + b);
    arb_zero(c->part + b);
    for (i = 0; i < num; i++)
    {
        slong j = j0 + i;
        arb_addmul(c->part + b, a, z + i, wp);
        arb_mul_si(a, a, -BETA * (2 * j + 3) * (2 * j + 3), wp); arb_div_ui(a, a, 4 * (ulong) (j + 1) * (j + 2), wp);
    }
    _arb_vec_clear(z, num); arb_clear(a); arb_clear(pn); arb_clear(in);
}

static void V_ref_zeta(arb_t res, slong prec, int threads)
{
    vzctx c;
    slong b, j;
    ulong n;
    arb_t a, S, t;
    if ((VKS + 1) * (VKS + 1) <= 2 * BETA) { flint_printf("vortex zeta reference: s too large\n"); flint_abort(); }
    c.J = (slong) ((prec + 64) / log2((VKS + 1.0) * (VKS + 1.0) / BETA)) + 16;
    c.wp = prec + 64 + (slong) (c.J * log2((double) BETA)) + 16;
    c.nblocks = (c.J + VBLK - 1) / VBLK;
    c.a0 = _arb_vec_init(c.nblocks); c.part = _arb_vec_init(c.nblocks);
    arb_init(a); arb_init(S); arb_init(t);
    arb_one(a);
    for (j = 0; j < c.J; j++)
    {
        if (j % VBLK == 0) arb_set(c.a0 + j / VBLK, a);
        arb_mul_si(a, a, -BETA * (2 * j + 3) * (2 * j + 3), c.wp); arb_div_ui(a, a, 4 * (ulong) (j + 1) * (j + 2), c.wp);
    }
    parallel_for(c.nblocks, vz_block, &c, threads);
    for (b = 0; b < c.nblocks; b++) arb_add(S, S, c.part + b, c.wp);
    arb_add_error_2exp_si(S, -prec - 40);      /* truncation (terms decay geometrically) */
    for (n = 1; n <= VKS; n++) { vortex_direct_term(t, n, prec + 64); arb_add(S, S, t, prec + 64); }
    mul_lambda3(res, S, prec);
    _arb_vec_clear(c.a0, c.nblocks); _arb_vec_clear(c.part, c.nblocks);
    arb_clear(a); arb_clear(S); arb_clear(t);
}

/* ======================= reference: Euler-Maclaurin =======================
   F(x) = x^-3 G(-beta/x^2), G = 2F1(3/2,3/2;2;.), satisfies x (beta + x^2) F'' + (beta + 5 x^2) F' + 3 x F = 0.
   Direct sum for n < M; Taylor coefficients of F(M + t) by the recurrence from the ODE (ode_jet), started from
   F(M) and F'(M) = -3 M^-4 G + (9/4) beta M^-6 2F1(5/2,5/2;3;-beta/M^2);
   int_M^oo F = sum_j g_j (-beta)^j M^-(2j+2)/(2j+2), g_j = (3/2)_j^2/((2)_j j!). */
typedef struct { ulong M; slong wp, nblocks; arb_ptr part; } vemctx;
#define VEMBLK 64
static void vem_block(slong b, void * vctx)
{
    vemctx * c = vctx;
    ulong n, n1 = 1 + b * VEMBLK, n2 = FLINT_MIN(c->M, n1 + VEMBLK);
    arb_t t; arb_init(t);
    arb_zero(c->part + b);
    for (n = n1; n < n2; n++) { vortex_direct_term(t, n, c->wp); arb_add(c->part + b, c->part + b, t, c->wp); }
    arb_clear(t);
}

/* the Taylor coefficients of F(M + t), from the differential equation */
static void vortex_jet_init(ode_jet_t * J, ulong M, slong wp)
{
    fmpz_poly_t p2, p1, p0;
    arb_t a, cc, z, G, t, f0, f1;
    fmpz_poly_init(p2); fmpz_poly_init(p1); fmpz_poly_init(p0);
    fmpz_poly_set_coeff_ui(p2, 3, 1); fmpz_poly_set_coeff_ui(p2, 1, BETA);      /* x^3 + beta x */
    fmpz_poly_set_coeff_ui(p1, 2, 5); fmpz_poly_set_coeff_ui(p1, 0, BETA);      /* 5 x^2 + beta */
    fmpz_poly_set_coeff_ui(p0, 1, 3);                                           /* 3 x */
    arb_init(a); arb_init(cc); arb_init(z); arb_init(G); arb_init(t); arb_init(f0); arb_init(f1);
    arb_set_si(z, -BETA); arb_div_ui(z, z, M, wp); arb_div_ui(z, z, M, wp);
    arb_set_d(a, 1.5); arb_set_ui(cc, 2);
    arb_hypgeom_2f1(G, a, a, cc, z, 0, wp);
    arb_set_ui(t, M); arb_pow_ui(t, t, 3, wp); arb_div(f0, G, t, wp);           /* F(M) */
    arb_set_d(a, 2.5); arb_set_ui(cc, 3);
    arb_hypgeom_2f1(f1, a, a, cc, z, 0, wp);
    arb_mul_ui(f1, f1, 9 * BETA, wp); arb_div_ui(f1, f1, 4 * M * M, wp);
    arb_submul_ui(f1, G, 3, wp);
    arb_set_ui(t, M); arb_pow_ui(t, t, 4, wp); arb_div(f1, f1, t, wp);         /* F'(M) */
    ode_jet_init(J, p2, p1, p0, M, f0, f1, wp);
    fmpz_poly_clear(p2); fmpz_poly_clear(p1); fmpz_poly_clear(p0);
    arb_clear(a); arb_clear(cc); arb_clear(z); arb_clear(G); arb_clear(t); arb_clear(f0); arb_clear(f1);
}

static void V_ref_em(arb_t res, slong prec, int threads)
{
    ulong M = em_cutoff(prec);
    slong wp = prec + 64, len = em_length((double) M, prec) + 2, b, j, NG;
    vemctx c;
    arb_t S, I, g, t, pw, F0;
    arb_init(S); arb_init(I); arb_init(g); arb_init(t); arb_init(pw); arb_init(F0);
    c.M = M; c.wp = wp; c.nblocks = (M - 1 + VEMBLK - 1) / VEMBLK; c.part = _arb_vec_init(c.nblocks);
    parallel_for(c.nblocks, vem_block, &c, threads);
    for (b = 0; b < c.nblocks; b++) arb_add(S, S, c.part + b, wp);
    _arb_vec_clear(c.part, c.nblocks);
    {
        ode_jet_t J; jet_stream_t js;
        vortex_jet_init(&J, M, wp + 32);
        js.restart = ode_jet_restart; js.next = ode_jet_next; js.st = &J;
        em_bernoulli_stream(t, F0, &js, len, wp);
        ode_jet_clear(&J);
    }
    arb_sub(S, S, t, wp);
    arb_mul_2exp_si(t, F0, -1); arb_add(S, S, t, wp);
    /* int_M^oo x^-3 G(-beta/x^2) dx */
    NG = (slong) ((wp + 20) / log2((double) M * M / BETA)) + 8;
    arb_one(g); arb_set_ui(pw, M); arb_mul_ui(pw, pw, M, wp); arb_inv(pw, pw, wp);
    for (j = 0; j < NG; j++)
    {
        arb_div_ui(t, pw, 2 * j + 2, wp); arb_addmul(I, g, t, wp);
        arb_mul_si(g, g, -BETA * (2 * j + 3) * (2 * j + 3), wp); arb_div_ui(g, g, 4 * (ulong) (j + 1) * (j + 2), wp);
        arb_div_ui(pw, pw, M, wp); arb_div_ui(pw, pw, M, wp);
    }
    arb_add(S, S, I, wp);
    mul_lambda3(res, S, prec);
    arb_clear(S); arb_clear(I); arb_clear(g); arb_clear(t); arb_clear(pw); arb_clear(F0);
}

/* the Euler-Maclaurin direct part needs vortex parameters even without the theta setup */
static void V_ref_em_entry(arb_t res, slong prec, int threads)
{
    const char * es = getenv("HOLSUM_VORTEX_S");
    if (es != NULL) SPAR = atol(es);
    BETA = SPAR * SPAR;
    V_ref_em(res, prec, threads);
}
static void V_ref_zeta_entry(arb_t res, slong prec, int threads)
{
    const char * es = getenv("HOLSUM_VORTEX_S");
    if (es != NULL) SPAR = atol(es);
    BETA = SPAR * SPAR;
    V_ref_zeta(res, prec, threads);
}

const constant_t CONST_VORTEX = {
    "vortex", "velocity induced in a periodic array of coaxial vortex rings, U(lambda = 2/s), s = HOLSUM_VORTEX_S (default 2)",
    vortex_setup, vortex_clear, V_dual, V_k, 1, V_finish, V_main, V_ref_zeta_entry, V_ref_em_entry, 1 };
