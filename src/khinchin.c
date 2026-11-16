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
#include "tsys.h"

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
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_DEN, 4); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), n2); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), (n + 1));
    fmpz_set(fmpz_mat_entry(T, 0, 1), fmpz_mat_entry(T, 0, 0));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), U0_NUM, 4); fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), K); fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), n2);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), U0_DEN, K * (n + 1));
}

/* main: S_a = sum_i (y^i/i!) W_i with W_i = sum_{n<=i} c^n/n^2: U' = (y/(i+1))U + (y c/(i+1)^3) V, V' = (y c/(i+1)) V */
typedef struct { fmpz_t yn, yd; ulong c; } uv_ctx;
static void uv_leaf(fmpz_mat_t T, fmpz_t q, slong i, const void * v)
{
    const uv_ctx * x = v; ulong i1 = i + 1;
    fmpz_mul_ui(q, x->yd, i1); fmpz_mul_ui(q, q, i1); fmpz_mul_ui(q, q, i1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), x->yn, i1 * i1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 1), x->yn, x->c);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), x->yn, x->c); fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), i1); fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), i1);
    fmpz_set(fmpz_mat_entry(T, 2, 0), q);
}
/* t_n = (4u0)^n/n!, sum t_n/n^2 */
static void h4_leaf(fmpz_mat_t T, fmpz_t q, slong n, const void * v)
{
    fmpz_mul_ui(q, U0_DEN, (ulong) (n + 1)); fmpz_mul_ui(q, q, n); fmpz_mul_ui(q, q, n);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, 4); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), (ulong) n); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), n);
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
    fmpz_set_ui(q, (ulong) (n + 1)); fmpz_mul_ui(q, q, (n + 1)); fmpz_mul_ui(q, q, (n + 2)); fmpz_mul_ui(q, q, (2 * n + 3));
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
    fmpz_mul_ui(a, U0_DEN, (ulong) (N + 1)); fmpz_mul_ui(a, a, D1); fmpz_mul_ui(a, a, N);            /* (N+1) ud D1 N */
    fmpz_mul_ui(b, U0_NUM, K); fmpz_mul_ui(b, b, D1); fmpz_mul_ui(b, b, N);                           /* un K D1 N */
    fmpz_mul_ui(q, a, K);
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), a);
    fmpz_set(fmpz_mat_entry(T, 1, 1), b);
    fmpz_set(fmpz_mat_entry(T, 2, 2), a); fmpz_set(fmpz_mat_entry(T, 2, 3), a);
    fmpz_mul_si(fmpz_mat_entry(T, 2, 0), U0_DEN, -(slong) ((N + 1) * N));      /* A_{N+1} - A_N = -1/D1 */
    fmpz_set(fmpz_mat_entry(T, 2, 1), fmpz_mat_entry(T, 2, 0));
    fmpz_set(fmpz_mat_entry(T, 3, 3), b);
    fmpz_mul_si(fmpz_mat_entry(T, 3, 1), U0_NUM, -(slong) (K * N));
    fmpz_mul_ui(fmpz_mat_entry(T, 4, 2), U0_DEN, K); fmpz_mul_ui(fmpz_mat_entry(T, 4, 2), fmpz_mat_entry(T, 4, 2), (N + 1)); fmpz_mul_ui(fmpz_mat_entry(T, 4, 2), fmpz_mat_entry(T, 4, 2), D1);
    fmpz_clear(a); fmpz_clear(b);
}

/* main, L_1 = e^-u0 sum_{i>=1} t_i W_i: state (t, tA, tW) */
static void m2a_leaf(fmpz_mat_t T, fmpz_t q, slong i, const void * v)
{
    ulong i1 = i + 1, D1 = 2 * (ulong) i * (2 * i + 1);
    fmpz_mul_ui(q, U0_DEN, i1); fmpz_mul_ui(q, q, i1); fmpz_mul_ui(q, q, D1);
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
    fmpz_mul_ui(q, U0_DEN, (n + 2)); fmpz_mul_ui(q, q, D1); fmpz_mul_ui(q, q, o); fmpz_mul_ui(q, q, n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, D1); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), o); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), U0_NUM, D1); fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), o); fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), n1);
    fmpz_mul_si(fmpz_mat_entry(T, 1, 0), U0_NUM, -(slong) (o * n1));
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 1), U0_DEN, 2); fmpz_mul_ui(fmpz_mat_entry(T, 2, 1), fmpz_mat_entry(T, 2, 1), (n + 2)); fmpz_mul_ui(fmpz_mat_entry(T, 2, 1), fmpz_mat_entry(T, 2, 1), D1); fmpz_mul_ui(fmpz_mat_entry(T, 2, 1), fmpz_mat_entry(T, 2, 1), n1);
    fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), U0_DEN, (n + 2)); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), fmpz_mat_entry(T, 3, 1), D1); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), fmpz_mat_entry(T, 3, 1), o);
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
    fmpz_mul_ui(a, U0_DEN, x->c); fmpz_mul_ui(a, a, m1); fmpz_mul_ui(a, a, m1); fmpz_mul_ui(a, a, m);
    fmpz_mul_ui(b, U0_NUM, x->c); fmpz_mul_ui(b, b, x->K); fmpz_mul_ui(b, b, m1); fmpz_mul_ui(b, b, m);
    fmpz_mul_ui(q, U0_DEN, x->K); fmpz_mul_ui(q, q, m1); fmpz_mul_ui(q, q, m1); fmpz_mul_ui(q, q, m);
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), a);
    fmpz_set(fmpz_mat_entry(T, 1, 1), b);
    fmpz_set(fmpz_mat_entry(T, 2, 2), a); fmpz_set(fmpz_mat_entry(T, 2, 3), a);
    fmpz_set(fmpz_mat_entry(T, 3, 3), b); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), U0_NUM, x->c); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), fmpz_mat_entry(T, 3, 1), x->K); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), fmpz_mat_entry(T, 3, 1), m);
    fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), U0_DEN, x->K); fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), fmpz_mat_entry(T, 4, 0), m1); fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), fmpz_mat_entry(T, 4, 0), m1);
    fmpz_set(fmpz_mat_entry(T, 5, 2), fmpz_mat_entry(T, 4, 0));
    fmpz_clear(a); fmpz_clear(b);
}
/* k-side odd, per c: (P, rho, U, V); sums P/(2m+1), U/(2m+1) */
static void k1o_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    const kcctx * x = v; ulong b = 2 * m + 3, a = 2 * m + 1;
    fmpz_t A, B; fmpz_init(A); fmpz_init(B);
    fmpz_mul_ui(A, U0_DEN, x->c); fmpz_mul_ui(A, A, b); fmpz_mul_ui(A, A, b); fmpz_mul_ui(A, A, a);
    fmpz_mul_ui(B, U0_NUM, 2); fmpz_mul_ui(B, B, x->c); fmpz_mul_ui(B, B, x->K); fmpz_mul_ui(B, B, b); fmpz_mul_ui(B, B, a);
    fmpz_mul_ui(q, U0_DEN, x->K); fmpz_mul_ui(q, q, b); fmpz_mul_ui(q, q, b); fmpz_mul_ui(q, q, a);
    fmpz_set(fmpz_mat_entry(T, 0, 0), A); fmpz_set(fmpz_mat_entry(T, 0, 1), A);
    fmpz_set(fmpz_mat_entry(T, 1, 1), B);
    fmpz_set(fmpz_mat_entry(T, 2, 2), A); fmpz_set(fmpz_mat_entry(T, 2, 3), A);
    fmpz_set(fmpz_mat_entry(T, 3, 3), B); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), U0_NUM, 2); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), fmpz_mat_entry(T, 3, 1), x->c); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), fmpz_mat_entry(T, 3, 1), x->K); fmpz_mul_ui(fmpz_mat_entry(T, 3, 1), fmpz_mat_entry(T, 3, 1), a);
    fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), U0_DEN, x->K); fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), fmpz_mat_entry(T, 4, 0), b); fmpz_mul_ui(fmpz_mat_entry(T, 4, 0), fmpz_mat_entry(T, 4, 0), b);
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
    fmpz_mul_ui(Q, U0_DEN, m1); fmpz_mul_ui(Q, Q, m1); fmpz_mul_ui(Q, Q, m); fmpz_mul_ui(Q, Q, o); fmpz_mul_ui(Q, Q, o);
    fmpz_set(q, Q);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, c); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), m1); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), m); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), o); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), o);
    fmpz_set(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 0, 0));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), U0_NUM, c); fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), fmpz_mat_entry(T, 1, 0), m); fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), fmpz_mat_entry(T, 1, 0), o); fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), fmpz_mat_entry(T, 1, 0), o);
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
    fmpz_mul_ui(Q, U0_DEN, a); fmpz_mul_ui(Q, Q, a); fmpz_mul_ui(Q, Q, a); fmpz_mul_ui(Q, Q, m2);
    fmpz_set(q, Q);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), U0_NUM, 2); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), c); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), a); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), a); fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), fmpz_mat_entry(T, 0, 0), m2);
    fmpz_set(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 0, 0));
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), U0_NUM, 2); fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), fmpz_mat_entry(T, 1, 0), c); fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), fmpz_mat_entry(T, 1, 0), a); fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), fmpz_mat_entry(T, 1, 0), m2);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), U0_DEN, a); fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), fmpz_mat_entry(T, 2, 0), a); fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), fmpz_mat_entry(T, 2, 0), m);
    fmpz_mul_ui(fmpz_mat_entry(T, 3, 0), U0_DEN, a * a);
    fmpz_mul_ui(fmpz_mat_entry(T, 4, 1), U0_DEN, a); fmpz_mul_ui(fmpz_mat_entry(T, 4, 1), fmpz_mat_entry(T, 4, 1), a); fmpz_mul_ui(fmpz_mat_entry(T, 4, 1), fmpz_mat_entry(T, 4, 1), m);
    fmpz_mul_ui(fmpz_mat_entry(T, 5, 0), U0_DEN, 2); fmpz_mul_ui(fmpz_mat_entry(T, 5, 0), fmpz_mat_entry(T, 5, 0), a); fmpz_mul_ui(fmpz_mat_entry(T, 5, 0), fmpz_mat_entry(T, 5, 0), m2);
    fmpz_mul_ui(fmpz_mat_entry(T, 6, 1), U0_DEN, 2); fmpz_mul_ui(fmpz_mat_entry(T, 6, 1), fmpz_mat_entry(T, 6, 1), a); fmpz_mul_ui(fmpz_mat_entry(T, 6, 1), fmpz_mat_entry(T, 6, 1), m2);
    fmpz_mul_ui(fmpz_mat_entry(T, 6, 0), U0_DEN, 2 * m2);
    fmpz_clear(Q);
}
/* L_k, even n = 2j: (wS, wSH, w4, w4H, w1, w1H), w = u0^j/j!; sums wS, wSH */
static void l1e_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    ulong k2 = ((const mctx *) v)->k2, j1 = j + 1;
    fmpz_mul_ui(q, U0_DEN, j1); fmpz_mul_ui(q, q, j1); fmpz_mul_ui(q, q, j1);
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
    fmpz_mul_ui(q, U0_DEN, b); fmpz_mul_ui(q, q, b); fmpz_mul_ui(q, q, b);
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
