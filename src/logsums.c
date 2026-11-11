/*
    Three constants with logarithmic summands (Section "Other constants" of the paper):

      A340440  A = sum_{k>=2} log k/(k^2 - 1)              = log(2)/2 + S_A/2,  S_A = sum_{k>=2} (2/k) artanh(1/k)
      A085361  C = sum_{k>=1} log k/(k(k+1))               = S_A/2 + O,          O = sum_{k>=2} -(1/(2k)) log(1 - 1/k^2)
               (exp(C - 1) is the Alladi-Grinstead constant, exp(C) Kalpazidou's Lueroth analogue of Khinchin's)
      Kminus1  Khinchin's harmonic mean K_{-1} = log(2)/T,  T = sum_{j>=2} -log(1 - 1/j^2)/(j - 1)

    Theta splitting at u0 = 4^-a with theta_3:  sum_k f(1/k) = sum_k I_k + sqrt(pi) sum_m J_m + M.
    Even parts have kernels in u^(m-1)/Gamma(m) (dual moments at t0 = 1/2, Gamma(1/2, y) starting values),
    odd parts in u^m/Gamma(m+1/2) (t0 = 1, E1(y) starting values). See the paper for the formulas.
*/
#include <math.h>
#include "constants.h"

/* ======================= k-side ======================= */
typedef struct { ulong K; } kctx;

static void zprod5(fmpz_t r, ulong a, ulong b, ulong c, ulong d, ulong e)
{
    fmpz_set_ui(r, a); fmpz_mul_ui(r, r, b); fmpz_mul_ui(r, r, c); fmpz_mul_ui(r, r, d); fmpz_mul_ui(r, r, e);
}

/* even part of S_A: P_{m+1} = (P + Q)/K, Q_{m+1} = u0 Q/(m+1), sum 2/(2m-1) P_m; m >= 1 */
static void kA_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    ulong K = ((const kctx *) v)->K;
    fmpz_t a; fmpz_init(a);
    fmpz_set_ui(a, (ulong) (m + 1) * (2 * m - 1)); fmpz_mul(a, a, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), a);
    fmpz_set_ui(fmpz_mat_entry(T, 1, 1), K); fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), 2 * m - 1);
    fmpz_mul(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), U0_NUM);
    fmpz_set_ui(fmpz_mat_entry(T, 2, 0), 2 * K); fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), fmpz_mat_entry(T, 2, 0), m + 1);
    fmpz_mul(fmpz_mat_entry(T, 2, 0), fmpz_mat_entry(T, 2, 0), U0_DEN);
    fmpz_mul_ui(q, a, K);
    fmpz_clear(a);
}

/* odd part O: P''_{m+1} = (P'' + R)/K, R_{m+1} = R 2u0/(2m+3), sum P''/(2m); m >= 1 */
static void kO_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    ulong K = ((const kctx *) v)->K;
    fmpz_t a; fmpz_init(a);
    fmpz_set_ui(a, (ulong) (2 * m + 3) * (2 * m)); fmpz_mul(a, a, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), a);
    fmpz_set_ui(fmpz_mat_entry(T, 1, 1), 4 * K); fmpz_mul_ui(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), m);
    fmpz_mul(fmpz_mat_entry(T, 1, 1), fmpz_mat_entry(T, 1, 1), U0_NUM);
    fmpz_set_ui(fmpz_mat_entry(T, 2, 0), K); fmpz_mul_ui(fmpz_mat_entry(T, 2, 0), fmpz_mat_entry(T, 2, 0), 2 * m + 3);
    fmpz_mul(fmpz_mat_entry(T, 2, 0), fmpz_mat_entry(T, 2, 0), U0_DEN);
    fmpz_mul_ui(q, a, K);
    fmpz_clear(a);
}

/* T even: state (P, Q, U = H_{m-1} P, V = H_{m-1} Q), sum U; q = K m (m+1) ud */
static void kCe_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    ulong K = ((const kctx *) v)->K;
    fmpz_t a, b, c; fmpz_init(a); fmpz_init(b); fmpz_init(c);
    fmpz_set_ui(a, (ulong) m * (m + 1)); fmpz_mul(a, a, U0_DEN);
    fmpz_set_ui(b, (ulong) K * m); fmpz_mul(b, b, U0_NUM);
    fmpz_set_ui(c, m + 1); fmpz_mul(c, c, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), a);
    fmpz_set(fmpz_mat_entry(T, 1, 1), b);
    fmpz_set(fmpz_mat_entry(T, 2, 2), a); fmpz_set(fmpz_mat_entry(T, 2, 3), a);
    fmpz_set(fmpz_mat_entry(T, 2, 0), c); fmpz_set(fmpz_mat_entry(T, 2, 1), c);
    fmpz_set(fmpz_mat_entry(T, 3, 3), b);
    fmpz_set_ui(fmpz_mat_entry(T, 3, 1), K); fmpz_mul(fmpz_mat_entry(T, 3, 1), fmpz_mat_entry(T, 3, 1), U0_NUM);
    fmpz_mul_ui(q, a, K);
    fmpz_set(fmpz_mat_entry(T, 4, 2), q);
    fmpz_clear(a); fmpz_clear(b); fmpz_clear(c);
}

/* T odd: state (P'', R, U'' = H_m P'', V'' = H_m R), sum U''; q = K (m+1)(2m+3) ud */
static void kCo_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    ulong K = ((const kctx *) v)->K;
    fmpz_t a, b, c; fmpz_init(a); fmpz_init(b); fmpz_init(c);
    fmpz_set_ui(a, (ulong) (m + 1) * (2 * m + 3)); fmpz_mul(a, a, U0_DEN);
    fmpz_set_ui(b, 2 * (ulong) K * (m + 1)); fmpz_mul(b, b, U0_NUM);
    fmpz_set_ui(c, 2 * m + 3); fmpz_mul(c, c, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 0, 0), a); fmpz_set(fmpz_mat_entry(T, 0, 1), a);
    fmpz_set(fmpz_mat_entry(T, 1, 1), b);
    fmpz_set(fmpz_mat_entry(T, 2, 2), a); fmpz_set(fmpz_mat_entry(T, 2, 3), a);
    fmpz_set(fmpz_mat_entry(T, 2, 0), c); fmpz_set(fmpz_mat_entry(T, 2, 1), c);
    fmpz_set(fmpz_mat_entry(T, 3, 3), b);
    fmpz_set_ui(fmpz_mat_entry(T, 3, 1), 2 * K); fmpz_mul(fmpz_mat_entry(T, 3, 1), fmpz_mat_entry(T, 3, 1), U0_NUM);
    fmpz_mul_ui(q, a, K);
    fmpz_set(fmpz_mat_entry(T, 4, 2), q);
    fmpz_clear(a); fmpz_clear(b); fmpz_clear(c);
}

/* number of terms of a k-side series (absolute 2^-prec after the factor e^-x) */
static slong k_terms(ulong K, slong prec, int harmonic)
{
    double x = K * U0_D, lx = log2(x), lK = log2((double) K), lt;
    slong m;
    for (m = 2; ; m++)
    {
        double poi = (m - 1 < x) ? (m - 1) * lx - lgamma((double) m) / log(2.0) + 1 : 1.4427 * x;
        lt = -m * lK + FLINT_MIN(1.4427 * x, poi) + (harmonic ? log2(log((double) m) + 2) : 1);
        if (lt - 1.4427 * x < -prec - 40) return m + 1;
    }
}

/* even k-side part: e^-x sum_{m>=1} a_m X_m */
static void k_even(arb_t res, ulong K, slong wp, slong prec, int harm)
{
    kctx kc; bs_t B; arb_ptr x0 = _arb_vec_init(4); arb_t s, x;
    slong N = k_terms(K, prec, harm);
    arb_init(s); arb_init(x);
    kc.K = K;
    B.d = harm ? 4 : 2; B.s = 1; B.leaf = harm ? kCe_leaf : kA_leaf; B.ctx = &kc;
    arb_set_ui(x0 + 0, 1); arb_div_ui(x0 + 0, x0 + 0, K, wp); arb_set(x0 + 1, U0);
    bs_eval(NULL, s, x0, 1, N, &B, wp);
    arb_mul_ui(x, U0, K, wp); arb_neg(x, x); arb_exp(x, x, wp);
    arb_mul(res, s, x, wp);
    _arb_vec_clear(x0, 4); arb_clear(s); arb_clear(x);
}

/* odd k-side part: (1/k)[Gamma(1/2,x)/sqrt(pi) L_k + e^-x sqrt(x) (2/sqrt(pi)) sum a P''] */
static void k_odd(arb_t res, ulong k, slong wp, slong prec, int harm)
{
    ulong K = k * k;
    kctx kc; bs_t B; arb_ptr x0 = _arb_vec_init(4); arb_t s, x, ex, G, L, t, sp;
    slong N = k_terms(K, prec, harm);
    arb_init(s); arb_init(x); arb_init(ex); arb_init(G); arb_init(L); arb_init(t); arb_init(sp);
    kc.K = K;
    B.d = harm ? 4 : 2; B.s = 1; B.leaf = harm ? kCo_leaf : kO_leaf; B.ctx = &kc;
    arb_set_ui(x0 + 0, 1); arb_div_ui(x0 + 0, x0 + 0, K, wp);
    arb_mul_2exp_si(x0 + 1, U0, 1); arb_div_ui(x0 + 1, x0 + 1, 3, wp);
    if (harm) { arb_set(x0 + 2, x0 + 0); arb_set(x0 + 3, x0 + 1); }
    bs_eval(NULL, s, x0, 1, N, &B, wp);
    arb_mul_ui(x, U0, K, ARF_PREC_EXACT);
    arb_neg(ex, x); arb_exp(ex, ex, wp);
    arb_const_sqrt_pi(sp, wp);
    arb_sqrt(t, x, wp); arb_mul(s, s, t, wp); arb_mul(s, s, ex, wp); arb_mul_2exp_si(s, s, 1); arb_div(s, s, sp, wp);
    gamma_upper_exact(G, 1, x, wp);
    /* L_k = -log(1 - 1/K)/2 (O) or -log(1 - 1/K)/(1 - 1/K) (T) */
    arb_set_ui(t, K - 1); arb_div_ui(t, t, K, wp); arb_log(L, t, wp); arb_neg(L, L);
    if (harm) { arb_set_ui(t, K); arb_div_ui(t, t, K - 1, wp); arb_mul(L, L, t, wp); }
    else arb_mul_2exp_si(L, L, -1);
    arb_mul(G, G, L, wp); arb_div(G, G, sp, wp);
    arb_add(res, G, s, wp);
    arb_div_ui(res, res, k, wp);
    _arb_vec_clear(x0, 4); arb_clear(s); arb_clear(x); arb_clear(ex); arb_clear(G); arb_clear(L); arb_clear(t); arb_clear(sp);
}

/* ======================= dual systems ======================= */
/* S_A: state (nu, Y, Ylag), t0 = 1/2 */
static void amatA(fmpz * A, slong l, const fmpz_t C, const fmpz_t D)
{
    fmpz_mul_si(A + 0, D, 2 * l); fmpz_mul_si(A + 1, D, -2);
    fmpz_mul_si(A + 4, D, 2 * l - 1); fmpz_mul_si(A + 5, C, -2);
    fmpz_mul_si(A + 7, D, 2);
}
/* O: state (nu, Phi, Philag, Ct), t0 = 1 */
static void amatB(fmpz * A, slong l, const fmpz_t C, const fmpz_t D)
{
    fmpz_mul_si(A + 0, D, 2 * l); fmpz_neg(A + 1, D);
    fmpz_mul_si(A + 5, D, 2 * l - 1); fmpz_mul_si(A + 6, C, -2); fmpz_mul_si(A + 7, D, -2);
    fmpz_mul_si(A + 9, D, 2);
    fmpz_mul_si(A + 15, D, 2 * (l - 1));
}
/* T even: state (nu, nulag, Y, Ylag, C), t0 = 1/2 */
static void amatCe(fmpz * A, slong l, const fmpz_t C, const fmpz_t D)
{
    fmpz_mul_si(A + 0, D, 2 * l - 1); fmpz_mul_si(A + 1, C, -2); fmpz_mul_si(A + 2, D, -2); fmpz_mul_si(A + 4, D, 2);
    fmpz_mul_si(A + 5, D, 2);
    fmpz_mul_si(A + 12, D, 2 * l - 1); fmpz_mul_si(A + 13, C, -2);
    fmpz_mul_si(A + 17, D, 2);
    fmpz_mul_si(A + 24, D, 2 * l - 1);
}
/* T odd: state (nu, nulag, eta, Phi, Philag, Ct), t0 = 1 */
static void amatCo(fmpz * A, slong l, const fmpz_t C, const fmpz_t D)
{
    fmpz_mul_si(A + 0, D, 2 * l - 1); fmpz_mul_si(A + 1, C, -2); fmpz_mul_si(A + 2, D, 2); fmpz_mul_si(A + 3, D, -2);
    fmpz_mul_si(A + 6, D, 2);
    fmpz_mul_si(A + 14, D, 2 * l); fmpz_neg(A + 15, D);
    fmpz_mul_si(A + 21, D, 2 * l - 1); fmpz_mul_si(A + 22, C, -2); fmpz_mul_si(A + 23, D, -2);
    fmpz_mul_si(A + 27, D, 2);
    fmpz_mul_si(A + 35, D, 2 * (l - 1));
}

/* ---------------- starting values ---------------- */
typedef struct { fmpz_t C, D; } ictx;

/* half-integer family, b_j = 1/j!: state (Pa, Pb, T) = b_j (alpha_{j-1/2}, beta_{j-1/2}, u0^{j+1/2});
   sums for S_A: nu (2/(2j+1)), Y (1), Ylag (j) for alpha and beta */
static void iA_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    const ictx * c = v;
    fmpz_t t; fmpz_init(t);
    ulong base = (ulong) (j + 1) * (2 * j + 3) * (2 * j + 1);
    fmpz_set_ui(q, base); fmpz_mul(q, q, c->D); fmpz_mul(q, q, U0_DEN);
    fmpz_mul_si(t, c->C, -2 * (2 * j + 1)); fmpz_mul(t, t, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 0, 0), t); fmpz_set(fmpz_mat_entry(T, 1, 1), t);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 2), c->D, 2 * (2 * j + 1)); fmpz_mul(fmpz_mat_entry(T, 1, 2), fmpz_mat_entry(T, 1, 2), U0_NUM);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 2), c->D, (ulong) (2 * j + 3) * (2 * j + 1)); fmpz_mul(fmpz_mat_entry(T, 2, 2), fmpz_mat_entry(T, 2, 2), U0_NUM);
    fmpz_mul_ui(t, c->D, 2 * (ulong) (j + 1) * (2 * j + 3)); fmpz_mul(t, t, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 3, 0), t); fmpz_set(fmpz_mat_entry(T, 4, 1), t);
    fmpz_set(fmpz_mat_entry(T, 5, 0), q); fmpz_set(fmpz_mat_entry(T, 6, 1), q);
    fmpz_mul_ui(fmpz_mat_entry(T, 7, 0), q, j); fmpz_mul_ui(fmpz_mat_entry(T, 8, 1), q, j);
    fmpz_clear(t);
}

/* half-integer family with harmonic copies (T even): state (Pa, Pb, T, Ha, Hb, HT) */
static void iCe_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    const ictx * c = v;
    fmpz_t t, r, s, w;
    ulong rr = j + 1;
    fmpz_init(t); fmpz_init(r); fmpz_init(s); fmpz_init(w);
    zprod5(q, j + 1, j + 1, 2 * j + 3, 2 * j + 1, 1); fmpz_mul(q, q, c->D); fmpz_mul(q, q, U0_DEN);
    fmpz_mul_si(t, c->C, -2 * (2 * j + 1)); fmpz_mul(t, t, U0_DEN);
    fmpz_mul_ui(r, t, rr);
    fmpz_mul_ui(s, c->D, 2 * (2 * j + 1)); fmpz_mul(s, s, U0_NUM);
    fmpz_mul_ui(w, c->D, (ulong) (2 * j + 3) * (2 * j + 1)); fmpz_mul(w, w, U0_NUM);
    fmpz_set(fmpz_mat_entry(T, 0, 0), r);
    fmpz_set(fmpz_mat_entry(T, 1, 1), r); fmpz_mul_ui(fmpz_mat_entry(T, 1, 2), s, rr);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 2), w, rr);
    fmpz_set(fmpz_mat_entry(T, 3, 3), r); fmpz_set(fmpz_mat_entry(T, 3, 0), t);
    fmpz_set(fmpz_mat_entry(T, 4, 4), r); fmpz_mul_ui(fmpz_mat_entry(T, 4, 5), s, rr);
    fmpz_set(fmpz_mat_entry(T, 4, 2), s); fmpz_set(fmpz_mat_entry(T, 4, 1), t);
    fmpz_mul_ui(fmpz_mat_entry(T, 5, 5), w, rr); fmpz_set(fmpz_mat_entry(T, 5, 2), w);
    fmpz_set(fmpz_mat_entry(T, 6, 3), q); fmpz_set(fmpz_mat_entry(T, 7, 4), q);
    fmpz_mul_ui(fmpz_mat_entry(T, 8, 3), q, j); fmpz_neg(fmpz_mat_entry(T, 8, 0), q);
    fmpz_mul_ui(fmpz_mat_entry(T, 9, 4), q, j); fmpz_neg(fmpz_mat_entry(T, 9, 1), q);
    fmpz_set(fmpz_mat_entry(T, 10, 0), q); fmpz_set(fmpz_mat_entry(T, 11, 1), q);
    fmpz_mul_ui(fmpz_mat_entry(T, 12, 0), q, j); fmpz_mul_ui(fmpz_mat_entry(T, 13, 1), q, j);
    fmpz_clear(t); fmpz_clear(r); fmpz_clear(s); fmpz_clear(w);
}

/* integer family, b_m = 4^m m!/(2m)!: state (Pa, Pb, T) = b_m (alpha_{m-1}, beta_{m-1}, u0^m);
   sums for O: nu (1/(2m)), Phi (1), Philag ((2m-1)/2; the m = 1 term is removed afterwards) */
static void iB_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    const ictx * c = v;
    fmpz_t t; fmpz_init(t);
    zprod5(q, 4 * m, 2 * m + 1, m + 1, 1, 1); fmpz_mul(q, q, c->D); fmpz_mul(q, q, U0_DEN);
    fmpz_mul_si(t, c->C, -8 * m); fmpz_mul(t, t, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 0, 0), t); fmpz_set(fmpz_mat_entry(T, 1, 1), t);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 2), c->D, 8 * m); fmpz_mul(fmpz_mat_entry(T, 1, 2), fmpz_mat_entry(T, 1, 2), U0_NUM);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 2), c->D, 8 * (ulong) m * (m + 1)); fmpz_mul(fmpz_mat_entry(T, 2, 2), fmpz_mat_entry(T, 2, 2), U0_NUM);
    fmpz_mul_ui(t, c->D, 2 * (ulong) (2 * m + 1) * (m + 1)); fmpz_mul(t, t, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 3, 0), t); fmpz_set(fmpz_mat_entry(T, 4, 1), t);
    fmpz_set(fmpz_mat_entry(T, 5, 0), q); fmpz_set(fmpz_mat_entry(T, 6, 1), q);
    zprod5(t, 2 * m, 2 * m - 1, 2 * m + 1, m + 1, 1); fmpz_mul(t, t, c->D); fmpz_mul(t, t, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 7, 0), t); fmpz_set(fmpz_mat_entry(T, 8, 1), t);
    fmpz_clear(t);
}

/* integer family with harmonic copies (T odd): state (Pa, Pb, T, Ha, Hb, HT) */
static void iCo_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * v)
{
    const ictx * c = v;
    fmpz_t t, r, s, w, z;
    ulong rr = m + 1;
    fmpz_init(t); fmpz_init(r); fmpz_init(s); fmpz_init(w); fmpz_init(z);
    zprod5(q, 4 * m, 2 * m + 1, m + 1, m + 1, 1); fmpz_mul(q, q, c->D); fmpz_mul(q, q, U0_DEN);
    fmpz_mul_si(t, c->C, -8 * m); fmpz_mul(t, t, U0_DEN);
    fmpz_mul_ui(r, t, rr);
    fmpz_mul_ui(s, c->D, 8 * m); fmpz_mul(s, s, U0_NUM);
    fmpz_mul_ui(w, c->D, 8 * (ulong) m * (m + 1)); fmpz_mul(w, w, U0_NUM);
    fmpz_set(fmpz_mat_entry(T, 0, 0), r);
    fmpz_set(fmpz_mat_entry(T, 1, 1), r); fmpz_mul_ui(fmpz_mat_entry(T, 1, 2), s, rr);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 2), w, rr);
    fmpz_set(fmpz_mat_entry(T, 3, 3), r); fmpz_set(fmpz_mat_entry(T, 3, 0), t);
    fmpz_set(fmpz_mat_entry(T, 4, 4), r); fmpz_mul_ui(fmpz_mat_entry(T, 4, 5), s, rr);
    fmpz_set(fmpz_mat_entry(T, 4, 2), s); fmpz_set(fmpz_mat_entry(T, 4, 1), t);
    fmpz_mul_ui(fmpz_mat_entry(T, 5, 5), w, rr); fmpz_set(fmpz_mat_entry(T, 5, 2), w);
    fmpz_set(fmpz_mat_entry(T, 6, 3), q); fmpz_set(fmpz_mat_entry(T, 7, 4), q);
    zprod5(z, 2 * m, 2 * m + 1, m + 1, m + 1, 2 * m - 1); fmpz_mul(z, z, c->D); fmpz_mul(z, z, U0_DEN);
    zprod5(w, 2 * (2 * m + 1), m + 1, m + 1, 2 * m - 1, 1); fmpz_mul(w, w, c->D); fmpz_mul(w, w, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 8, 3), z); fmpz_neg(fmpz_mat_entry(T, 8, 0), w);
    fmpz_set(fmpz_mat_entry(T, 9, 4), z); fmpz_neg(fmpz_mat_entry(T, 9, 1), w);
    zprod5(t, 2 * (2 * m + 1), m + 1, m + 1, 1, 1); fmpz_mul(t, t, c->D); fmpz_mul(t, t, U0_DEN);
    fmpz_set(fmpz_mat_entry(T, 10, 0), t); fmpz_set(fmpz_mat_entry(T, 11, 1), t);
    fmpz_set(fmpz_mat_entry(T, 12, 0), q); fmpz_set(fmpz_mat_entry(T, 13, 1), q);
    fmpz_set(fmpz_mat_entry(T, 14, 0), z); fmpz_set(fmpz_mat_entry(T, 15, 1), z);
    fmpz_clear(t); fmpz_clear(r); fmpz_clear(s); fmpz_clear(w); fmpz_clear(z);
}

/* number of terms of a starting-value series: alpha part ~ (4c)^j/(2j)!, beta part ~ u0^j/j! */
static slong init_terms(double c, slong W)
{
    double la = 0, lb = 0; slong j;
    for (j = 1; ; j++)
    {
        la += log2(4 * c + 4) - 2 * log2(j + 0.5) + 2;
        lb += log2(U0_D) - log2((double) j) + 2;
        if (j > 10 && la < -W - 64 && lb < -W - 64) return j + 1;
    }
}

static slong init_common(arb_t c, arb_t E, arb_t base, int half, const fmpz_t C, slong e, slong wp, slong * N)
{
    slong W;
    double cd = ldexp(fmpz_get_d(C), -(int) e);
    W = dual_init_common(c, E, base, half, C, e, wp, 6 * sqrt(cd));
    *N = init_terms(cd, W);
    return W;
}

static void initA(arb_ptr V, arb_t E, const fmpz_t C, slong e, slong wp, const void * sys)
{
    ictx ic; bs_t B; arb_t c, G; arb_ptr x0 = _arb_vec_init(3), s = _arb_vec_init(6);
    slong W, N;
    arb_init(c); arb_init(G);
    W = init_common(c, E, G, 1, C, e, wp, &N);
    fmpz_init_set(ic.C, C); fmpz_init(ic.D); fmpz_one(ic.D); fmpz_mul_2exp(ic.D, ic.D, e);
    B.d = 3; B.s = 6; B.leaf = iA_leaf; B.ctx = &ic;
    arb_mul_si(x0 + 0, c, -2, W); arb_mul_2exp_si(x0 + 1, SQRT_U0, 1); arb_set(x0 + 2, SQRT_U0);
    bs_eval(NULL, s, x0, 0, N, &B, W);
    arb_mul(V + 0, G, s + 0, W); arb_addmul(V + 0, E, s + 1, W);
    arb_mul(V + 1, G, s + 2, W); arb_addmul(V + 1, E, s + 3, W);
    arb_mul(V + 2, G, s + 4, W); arb_addmul(V + 2, E, s + 5, W); arb_div(V + 2, V + 2, c, W);
    _arb_vec_clear(x0, 3); _arb_vec_clear(s, 6); arb_clear(c); arb_clear(G);
    fmpz_clear(ic.C); fmpz_clear(ic.D);
}

static void initB(arb_ptr V, arb_t E, const fmpz_t C, slong e, slong wp, const void * sys)
{
    ictx ic; bs_t B; arb_t c, B1, t; arb_ptr x0 = _arb_vec_init(3), s = _arb_vec_init(6);
    slong W, N;
    arb_init(c); arb_init(B1); arb_init(t);
    W = init_common(c, E, B1, 0, C, e, wp, &N);
    fmpz_init_set(ic.C, C); fmpz_init(ic.D); fmpz_one(ic.D); fmpz_mul_2exp(ic.D, ic.D, e);
    B.d = 3; B.s = 6; B.leaf = iB_leaf; B.ctx = &ic;
    arb_mul_si(x0 + 0, c, -2, W); arb_mul_2exp_si(x0 + 1, U0, 1); arb_mul_2exp_si(x0 + 2, U0, 1);
    bs_eval(NULL, s, x0, 1, N + 1, &B, W);
    arb_add(s + 4, s + 4, c, W); arb_sub(s + 5, s + 5, U0, W);
    arb_mul(V + 0, B1, s + 0, W); arb_addmul(V + 0, E, s + 1, W);
    arb_mul(V + 1, B1, s + 2, W); arb_addmul(V + 1, E, s + 3, W);
    arb_mul(V + 2, B1, s + 4, W); arb_addmul(V + 2, E, s + 5, W); arb_div(V + 2, V + 2, c, W);
    arb_mul(V + 3, c, B1, W); arb_neg(V + 3, V + 3); arb_addmul(V + 3, U0, E, W);
    arb_const_sqrt_pi(t, W);
    _arb_vec_scalar_div(V, V, 4, t, W);
    _arb_vec_clear(x0, 3); _arb_vec_clear(s, 6); arb_clear(c); arb_clear(B1); arb_clear(t);
    fmpz_clear(ic.C); fmpz_clear(ic.D);
}

static void initCe(arb_ptr V, arb_t E, const fmpz_t C, slong e, slong wp, const void * sys)
{
    ictx ic; bs_t B; arb_t c, G; arb_ptr x0 = _arb_vec_init(6), s = _arb_vec_init(8);
    slong W, N;
    arb_init(c); arb_init(G);
    W = init_common(c, E, G, 1, C, e, wp, &N);
    fmpz_init_set(ic.C, C); fmpz_init(ic.D); fmpz_one(ic.D); fmpz_mul_2exp(ic.D, ic.D, e);
    B.d = 6; B.s = 8; B.leaf = iCe_leaf; B.ctx = &ic;
    arb_mul_si(x0 + 0, c, -2, W); arb_mul_2exp_si(x0 + 1, SQRT_U0, 1); arb_set(x0 + 2, SQRT_U0);
    bs_eval(NULL, s, x0, 0, N, &B, W);
    arb_add(s + 2, s + 2, x0 + 0, W); arb_add(s + 3, s + 3, x0 + 1, W);
    arb_mul(V + 0, G, s + 0, W); arb_addmul(V + 0, E, s + 1, W);
    arb_mul(V + 1, G, s + 2, W); arb_addmul(V + 1, E, s + 3, W); arb_div(V + 1, V + 1, c, W);
    arb_mul(V + 2, G, s + 4, W); arb_addmul(V + 2, E, s + 5, W);
    arb_mul(V + 3, G, s + 6, W); arb_addmul(V + 3, E, s + 7, W); arb_div(V + 3, V + 3, c, W);
    arb_mul(V + 4, E, SQRT_U0, W); arb_submul(V + 4, c, G, W); arb_mul_2exp_si(V + 4, V + 4, 1);
    _arb_vec_clear(x0, 6); _arb_vec_clear(s, 8); arb_clear(c); arb_clear(G);
    fmpz_clear(ic.C); fmpz_clear(ic.D);
}

static void initCo(arb_ptr V, arb_t E, const fmpz_t C, slong e, slong wp, const void * sys)
{
    ictx ic; bs_t B; arb_t c, B1, t; arb_ptr x0 = _arb_vec_init(6), s = _arb_vec_init(10);
    slong W, N;
    arb_init(c); arb_init(B1); arb_init(t);
    W = init_common(c, E, B1, 0, C, e, wp, &N);
    fmpz_init_set(ic.C, C); fmpz_init(ic.D); fmpz_one(ic.D); fmpz_mul_2exp(ic.D, ic.D, e);
    B.d = 6; B.s = 10; B.leaf = iCo_leaf; B.ctx = &ic;
    arb_mul_si(x0 + 0, c, -2, W); arb_mul_2exp_si(x0 + 1, U0, 1); arb_mul_2exp_si(x0 + 2, U0, 1);
    arb_set(x0 + 3, x0 + 0); arb_set(x0 + 4, x0 + 1); arb_set(x0 + 5, x0 + 2);
    bs_eval(NULL, s, x0, 1, N + 1, &B, W);
    arb_add(s + 8, s + 8, c, W); arb_sub(s + 9, s + 9, U0, W);
    arb_mul(V + 0, B1, s + 0, W); arb_addmul(V + 0, E, s + 1, W);
    arb_mul(V + 1, B1, s + 2, W); arb_addmul(V + 1, E, s + 3, W); arb_div(V + 1, V + 1, c, W);
    arb_mul(V + 2, B1, s + 4, W); arb_addmul(V + 2, E, s + 5, W);
    arb_mul(V + 3, B1, s + 6, W); arb_addmul(V + 3, E, s + 7, W);
    arb_mul(V + 4, B1, s + 8, W); arb_addmul(V + 4, E, s + 9, W); arb_div(V + 4, V + 4, c, W);
    arb_mul(V + 5, c, B1, W); arb_neg(V + 5, V + 5); arb_addmul(V + 5, U0, E, W);
    arb_const_sqrt_pi(t, W);
    _arb_vec_scalar_div(V, V, 6, t, W);
    _arb_vec_clear(x0, 6); _arb_vec_clear(s, 10); arb_clear(c); arb_clear(B1); arb_clear(t);
    fmpz_clear(ic.C); fmpz_clear(ic.D);
}

/* ======================= main terms and systems ======================= */
static moment_sys_t SA, SB, SCe, SCo;
static arb_t MA, MO, MC;
static int setup_done = 0;

/* even, j >= 0: X = (x, xH, xo, xHs), x = u0^j/j!, H = H_j, o = sum_{i<j} 1/(2i+1), Hs = sum_{i<j} H_i */
static void setup_even_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    fmpz_t D, F; fmpz_init(D); fmpz_init(F);
    ulong j1 = j + 1, o = 2 * j + 1;
    fmpz_set_ui(D, 2 * j1 * j1); fmpz_mul_ui(D, D, o * o); fmpz_mul(D, D, U0_DEN);
    fmpz_set_ui(F, 2 * j1); fmpz_mul_ui(F, F, o * o); fmpz_mul(F, F, U0_NUM);
    fmpz_set(fmpz_mat_entry(T, 0, 0), F);
    fmpz_set(fmpz_mat_entry(T, 1, 1), F); fmpz_divexact_ui(fmpz_mat_entry(T, 1, 0), F, j1);
    fmpz_set(fmpz_mat_entry(T, 2, 2), F); fmpz_divexact_ui(fmpz_mat_entry(T, 2, 0), F, o);
    fmpz_set(fmpz_mat_entry(T, 3, 3), F); fmpz_set(fmpz_mat_entry(T, 3, 1), F);
    fmpz_divexact_ui(fmpz_mat_entry(T, 4, 0), D, o); fmpz_mul_2exp(fmpz_mat_entry(T, 4, 0), fmpz_mat_entry(T, 4, 0), 1);
    fmpz_set(fmpz_mat_entry(T, 5, 1), D);
    fmpz_divexact_ui(fmpz_mat_entry(T, 6, 0), D, o * o); fmpz_mul_2exp(fmpz_mat_entry(T, 6, 0), fmpz_mat_entry(T, 6, 0), 1);
    fmpz_divexact_ui(fmpz_mat_entry(T, 7, 0), F, o);
    fmpz_divexact_ui(fmpz_mat_entry(T, 8, 1), D, o);
    fmpz_tdiv_q_2exp(fmpz_mat_entry(T, 9, 1), F, 1);
    fmpz_set(fmpz_mat_entry(T, 10, 2), D);
    fmpz_set(fmpz_mat_entry(T, 11, 3), D);
    fmpz_set(q, D);
    fmpz_clear(D); fmpz_clear(F);
}

/* odd, j >= 1: X = (y, yH, yHS), y = b_j u0^j, H = H_j, HS = sum_{m<=j} H_m */
static void setup_odd_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * v)
{
    fmpz_t D, F; fmpz_init(D); fmpz_init(F);
    ulong j1 = j + 1, o = 2 * j + 1;
    fmpz_set_ui(D, 4 * (ulong) j * j); fmpz_mul_ui(D, D, o * j1); fmpz_mul(D, D, U0_DEN);
    fmpz_set_ui(F, 8 * (ulong) j * j); fmpz_mul_ui(F, F, j1); fmpz_mul(F, F, U0_NUM);
    fmpz_set(fmpz_mat_entry(T, 0, 0), F);
    fmpz_set(fmpz_mat_entry(T, 1, 1), F); fmpz_divexact_ui(fmpz_mat_entry(T, 1, 0), F, j1);
    fmpz_set(fmpz_mat_entry(T, 2, 2), F); fmpz_set(fmpz_mat_entry(T, 2, 1), F); fmpz_divexact_ui(fmpz_mat_entry(T, 2, 0), F, j1);
    fmpz_divexact_ui(fmpz_mat_entry(T, 3, 0), D, 2 * j);
    fmpz_set(fmpz_mat_entry(T, 4, 0), D);
    fmpz_set(fmpz_mat_entry(T, 5, 1), D);
    fmpz_divexact_ui(fmpz_mat_entry(T, 6, 0), D, 4 * (ulong) j * j);
    fmpz_divexact_ui(fmpz_mat_entry(T, 7, 0), D, 2 * (ulong) j * o);
    fmpz_divexact_ui(fmpz_mat_entry(T, 8, 1), D, 2 * j);
    fmpz_divexact_ui(fmpz_mat_entry(T, 9, 1), D, o);
    fmpz_divexact_ui(fmpz_mat_entry(T, 10, 2), D, o); fmpz_mul_2exp(fmpz_mat_entry(T, 10, 2), fmpz_mat_entry(T, 10, 2), 1);
    fmpz_set(q, D);
    fmpz_clear(D); fmpz_clear(F);
}

static void sys_set(moment_sys_t * S, int d, int ng, void (*amat)(fmpz *, slong, const fmpz_t, const fmpz_t),
    void (*init)(arb_ptr, arb_t, const fmpz_t, slong, slong, const void *), double t0,
    const int * fsel, const int * lag, const arb_t f0scale)
{
    int i;
    S->d = d; S->ng = ng; S->amat = amat; S->init = init; S->t0 = t0;
    for (i = 0; i < d; i++) { S->fsel[i] = fsel[i]; S->lag[i] = lag[i]; }
    arb_init(S->f0scale); arb_set(S->f0scale, f0scale);
}

static void logsums_setup(slong prec)
{
    slong wp = prec + 64, N;
    double lg = 0, lu = log2(U0_D);
    arb_t t, sp, em, s1, s2, s3, s4, s5, s6, one;
    if (setup_done) return;
    setup_done = 1;
    for (N = 1; lg > -(double) (wp + 40); N++) lg += lu - log2((double) N) + 1;
    N += 10;
    arb_init(t); arb_init(sp); arb_init(em); arb_init(one);
    arb_init(s1); arb_init(s2); arb_init(s3); arb_init(s4); arb_init(s5); arb_init(s6);
    arb_const_sqrt_pi(sp, wp);
    arb_neg(em, U0); arb_exp(em, em, wp);
    arb_one(one);
    {
        bs_t B; arb_ptr X0 = _arb_vec_init(4), R = _arb_vec_init(8); arb_t spu;
        arb_init(spu);
        B.d = 4; B.s = 8; B.leaf = setup_even_leaf; B.ctx = NULL;
        arb_one(X0 + 0);
        bs_eval(NULL, R, X0, 0, N, &B, wp);
        arb_mul(spu, sp, SQRT_U0, wp);
        arb_set(s1, R + 0); arb_set(s2, R + 1);
        arb_mul(s3, spu, R + 2, wp); arb_sub(s3, s3, R + 3, wp);
        arb_mul(s4, spu, R + 4, wp); arb_sub(s4, s4, R + 5, wp);
        arb_set(s5, R + 6); arb_set(s6, R + 7);
        _arb_vec_clear(X0, 4); _arb_vec_clear(R, 8); arb_clear(spu);
    }
    SA.kappa = _arb_vec_init(2);
    arb_set(SA.kappa + 0, s1); arb_exp(SA.kappa + 1, U0, wp);
    arb_init(MA); arb_mul(t, em, s5, wp); arb_mul_2exp_si(t, t, 1); arb_sub(MA, s3, t, wp);
    arb_init(MC); arb_mul(t, em, s6, wp); arb_sub(MC, s4, t, wp);
    SCe.kappa = _arb_vec_init(3);
    arb_set(SCe.kappa + 0, s2); arb_exp(SCe.kappa + 1, U0, wp); arb_one(SCe.kappa + 2);
    {
        arb_t hoB, phi, hoC, MOa, MCa, P1, P2, q;
        bs_t B; arb_ptr X0 = _arb_vec_init(3), R = _arb_vec_init(8);
        arb_init(hoB); arb_init(phi); arb_init(hoC); arb_init(MOa); arb_init(MCa);
        arb_init(P1); arb_init(P2); arb_init(q);
        B.d = 3; B.s = 8; B.leaf = setup_odd_leaf; B.ctx = NULL;
        arb_mul_2exp_si(X0 + 0, U0, 1); arb_set(X0 + 1, X0 + 0); arb_set(X0 + 2, X0 + 0);
        bs_eval(NULL, R, X0, 1, N, &B, wp);
        arb_div(q, SQRT_U0, sp, wp);
        arb_set(hoB, R + 0); arb_set(phi, R + 1); arb_set(hoC, R + 2);
        arb_mul(MOa, q, R + 4, wp); arb_sub(MOa, R + 3, MOa, wp);
        arb_mul(MCa, q, R + 6, wp); arb_sub(MCa, R + 5, MCa, wp);
        arb_mul_2exp_si(P1, R + 6, 1); arb_set(P2, R + 7);
        _arb_vec_clear(X0, 3); _arb_vec_clear(R, 8); arb_clear(q);
        SB.kappa = _arb_vec_init(3);
        arb_div(SB.kappa + 0, hoB, sp, wp);
        arb_div(SB.kappa + 1, phi, sp, wp);
        arb_div(SB.kappa + 2, U0, sp, wp);
        SCo.kappa = _arb_vec_init(4);
        arb_div(SCo.kappa + 0, hoC, sp, wp);
        arb_set(SCo.kappa + 1, SB.kappa + 0);
        arb_set(SCo.kappa + 2, SB.kappa + 1);
        arb_set(SCo.kappa + 3, SB.kappa + 2);
        arb_init(MO);
        arb_mul(t, em, SQRT_U0, wp); arb_mul(t, t, P1, wp); arb_div(t, t, sp, wp); arb_mul_2exp_si(t, t, -1);
        arb_sub(MO, MOa, t, wp);
        arb_add(MC, MC, MCa, wp);
        arb_mul(t, em, SQRT_U0, wp); arb_mul(t, t, P2, wp); arb_div(t, t, sp, wp);
        arb_sub(MC, MC, t, wp);
        arb_clear(hoB); arb_clear(phi); arb_clear(hoC); arb_clear(MOa); arb_clear(MCa);
        arb_clear(P1); arb_clear(P2);
    }
    {
        static const int fA[] = {0, 1, -1}, lA[] = {0, 0, -1};
        static const int fB[] = {0, 1, -1, 2}, lB[] = {0, 0, -1, 0};
        static const int fCe[] = {0, -1, 1, -1, 2}, lCe[] = {0, -1, 0, -1, 0};
        static const int fCo[] = {0, -1, 1, 2, -1, 3}, lCo[] = {0, -1, 0, 0, -1, 0};
        sys_set(&SA, 3, 2, amatA, initA, 0.5, fA, lA, SQRT_U0);
        sys_set(&SB, 4, 3, amatB, initB, 1.0, fB, lB, one);
        sys_set(&SCe, 5, 3, amatCe, initCe, 0.5, fCe, lCe, SQRT_U0);
        sys_set(&SCo, 6, 4, amatCo, initCo, 1.0, fCo, lCo, one);
    }
    arb_clear(t); arb_clear(sp); arb_clear(em); arb_clear(one);
    arb_clear(s1); arb_clear(s2); arb_clear(s3); arb_clear(s4); arb_clear(s5); arb_clear(s6);
}

static void logsums_clear(void)
{
    if (!setup_done) return;
    moment_sys_clear(&SA); moment_sys_clear(&SB); moment_sys_clear(&SCe); moment_sys_clear(&SCo);
    arb_clear(MA); arb_clear(MO); arb_clear(MC);
    setup_done = 0;
}

/* dual state value V[0] of S at c = pi^2 m^2, times sqrt(pi); 0 if negligible */
static void dual_value(arb_t res, const moment_sys_t * S, slong m, slong prec)
{
    slong wp = dual_term_prec(m, prec);
    arb_t c, sp; arb_ptr V;
    arb_zero(res);
    if (wp < 64) return;
    V = _arb_vec_init(SYS_MAXD);
    arb_init(c); arb_init(sp);
    arb_const_pi(c, 2 * prec + 64); arb_mul_ui(c, c, m, 2 * prec + 64); arb_sqr(c, c, 2 * prec + 64);
    arb_const_sqrt_pi(sp, wp + 64);
    dual_state(V, S, c, wp);
    arb_mul(res, V + 0, sp, wp);
    arb_clear(c); arb_clear(sp); _arb_vec_clear(V, SYS_MAXD);
}

static slong k_prec(ulong k, slong prec)
{
    return prec - (slong) (1.4426950408889634 * ((double) k * k - 1) * U0_D) + 64;
}

/* ---------------- A340440 ---------------- */
static void A_dual(arb_t res, slong idx, slong prec, void * ctx) { dual_value(res, &SA, idx + 1, prec); }
static void A_k(arb_t res, slong idx, slong prec, void * ctx)
{
    ulong k = idx + 2; slong wp = k_prec(k, prec);
    arb_zero(res);
    if (wp >= 64) k_even(res, k * k, wp, prec, 0);
}
static void A_main(arb_t res) { arb_set(res, MA); }
static void A_finish(arb_t res, const arb_t lin, slong prec)
{
    arb_t t; arb_init(t);
    arb_const_log2(t, prec); arb_add(res, lin, t, prec); arb_mul_2exp_si(res, res, -1);
    arb_clear(t);
}

/* ---------------- A085361 ---------------- */
static void C_dual(arb_t res, slong idx, slong prec, void * ctx)
{
    arb_t t; arb_init(t);
    dual_value(res, &SA, idx + 1, prec); arb_mul_2exp_si(res, res, -1);
    dual_value(t, &SB, idx + 1, prec); arb_add(res, res, t, prec + 64);
    arb_clear(t);
}
static void C_k(arb_t res, slong idx, slong prec, void * ctx)
{
    ulong k = idx + 2; slong wp = k_prec(k, prec);
    arb_t t;
    arb_zero(res);
    if (wp < 64) return;
    arb_init(t);
    k_even(res, k * k, wp, prec, 0); arb_mul_2exp_si(res, res, -1);
    k_odd(t, k, wp, prec, 0); arb_add(res, res, t, wp);
    arb_clear(t);
}
static void C_main(arb_t res) { arb_mul_2exp_si(res, MA, -1); arb_add(res, res, MO, ARF_PREC_EXACT); }
static void C_finish(arb_t res, const arb_t lin, slong prec) { arb_set_round(res, lin, prec); }

/* ---------------- K_{-1} ---------------- */
static void K_dual(arb_t res, slong idx, slong prec, void * ctx)
{
    arb_t t; arb_init(t);
    dual_value(res, &SCe, idx + 1, prec);
    dual_value(t, &SCo, idx + 1, prec); arb_add(res, res, t, prec + 64);
    arb_clear(t);
}
static void K_k(arb_t res, slong idx, slong prec, void * ctx)
{
    ulong k = idx + 2; slong wp = k_prec(k, prec);
    arb_t t;
    arb_zero(res);
    if (wp < 64) return;
    arb_init(t);
    k_even(res, k * k, wp, prec, 1);
    k_odd(t, k, wp, prec, 1); arb_add(res, res, t, wp);
    arb_clear(t);
}
static void K_main(arb_t res) { arb_set(res, MC); }
static void K_finish(arb_t res, const arb_t lin, slong prec)
{
    arb_t t; arb_init(t);
    arb_const_log2(t, prec); arb_div(res, t, lin, prec);
    arb_clear(t);
}

/* ======================= reference: zeta-value expansions =======================
   With z_n = zeta(n) - sum_{k<=KS} k^-n:
     sum_{k>KS} (1/k) artanh(1/k)          = sum_{n even} z_n/(n-1)
     sum_{k>KS} -(1/(2k)) log(1 - 1/k^2)   = sum_{n odd}  z_n/(n-1)
     sum_{k>KS} -(x/(1-x)) log(1 - x^2)    = sum_n H_{floor((n-1)/2)} z_n,   x = 1/k
   The values zeta(n) are computed in blocks of consecutive n, in parallel (zeta_vec_mixed in refs.c). */
#define ZKS 31
#define ZBLK 256

typedef struct
{
    slong N, wp, nblocks;
    int need_odd, need_T;
    arb_ptr SA, SO, Z, W;      /* per block */
} zctx;

static void z_block(slong b, void * vctx)
{
    zctx * c = vctx;
    slong step = c->need_odd ? 1 : 2;
    slong n0 = 2 + b * ZBLK * step, num, i, k, wp = c->wp;
    arb_ptr z;
    arb_t t, h, pk, ik;
    num = FLINT_MIN(ZBLK, (c->N - n0) / step + 1);
    if (num <= 0) return;
    z = _arb_vec_init(num);
    arb_init(t); arb_init(h); arb_init(pk); arb_init(ik);
    zeta_vec_mixed(z, n0, step, num, wp);
    for (i = 0; i < num; i++) arb_sub_ui(z + i, z + i, 1, wp);
    for (k = 2; k <= ZKS; k++)
    {
        if (n0 * log2((double) k) > wp + 20) break;
        arb_ui_pow_ui(pk, k, n0, wp); arb_inv(pk, pk, wp);
        arb_set_ui(ik, k); arb_pow_ui(ik, ik, step, wp); arb_inv(ik, ik, wp);
        for (i = 0; i < num; i++)
        {
            if ((n0 + i * step) * log2((double) k) > wp + 20) break;
            arb_sub(z + i, z + i, pk, wp);
            arb_mul(pk, pk, ik, wp);
        }
    }
    arb_zero(c->SA + b); arb_zero(c->SO + b); arb_zero(c->Z + b); arb_zero(c->W + b);
    arb_zero(h);        /* H_{floor((n-1)/2)} - H_{floor((n0-1)/2)} */
    for (i = 0; i < num; i++)
    {
        ulong n = n0 + i * step;
        if (i > 0 && c->need_T && n % 2 == 1 && n >= 3)
        {
            /* entering n odd: floor((n-1)/2) increases to (n-1)/2 */
            arb_set_ui(t, 2); arb_div_ui(t, t, n - 1, wp); arb_add(h, h, t, wp);
        }
        arb_div_ui(t, z + i, n - 1, wp);
        if (n % 2 == 0) arb_add(c->SA + b, c->SA + b, t, wp); else arb_add(c->SO + b, c->SO + b, t, wp);
        if (c->need_T) { arb_add(c->Z + b, c->Z + b, z + i, wp); arb_addmul(c->W + b, h, z + i, wp); }
    }
    _arb_vec_clear(z, num);
    arb_clear(t); arb_clear(h); arb_clear(pk); arb_clear(ik);
}

/* tails over k > ZKS plus the terms 2 <= k <= ZKS in closed form */
static void zeta_logsums(arb_t SAh, arb_t O, arb_t T, int need_odd, int need_T, slong prec, int threads)
{
    zctx c;
    slong b, n0, i, k, wp = prec + 64;
    arb_t H, x, t, u;
    c.N = (slong) ((prec + 64) / log2(ZKS + 1.0)) + 16;
    c.wp = wp; c.need_odd = need_odd; c.need_T = need_T;
    c.nblocks = (c.N - 2) / (ZBLK * (need_odd ? 1 : 2)) + 1;
    c.SA = _arb_vec_init(c.nblocks); c.SO = _arb_vec_init(c.nblocks); c.Z = _arb_vec_init(c.nblocks); c.W = _arb_vec_init(c.nblocks);
    parallel_for(c.nblocks, z_block, &c, threads);
    arb_init(H); arb_init(x); arb_init(t); arb_init(u);
    arb_zero(SAh); arb_zero(O); arb_zero(T);
    i = 0;   /* H holds H_i */
    for (b = 0; b < c.nblocks; b++)
    {
        arb_add(SAh, SAh, c.SA + b, wp);
        arb_add(O, O, c.SO + b, wp);
        if (need_T)
        {
            n0 = 2 + b * ZBLK;
            while (i < (n0 - 1) / 2) { i++; arb_set_ui(t, 1); arb_div_ui(t, t, i, wp); arb_add(H, H, t, wp); }
            arb_addmul(T, H, c.Z + b, wp);
            arb_add(T, T, c.W + b, wp);
        }
    }
    /* tail bound: terms below (ZKS+1)^-N N */
    {
        mag_t e; mag_init(e); mag_set_ui_2exp_si(e, 1, -(slong) (c.N * log2(ZKS + 1.0)) + 2 * FLINT_BIT_COUNT(c.N));
        arb_add_error_mag(SAh, e); arb_add_error_mag(O, e); arb_add_error_mag(T, e); mag_clear(e);
    }
    for (k = 2; k <= ZKS; k++)
    {
        arb_set_ui(x, 1); arb_div_ui(x, x, k, wp);
        arb_atanh(t, x, wp); arb_mul(t, t, x, wp); arb_add(SAh, SAh, t, wp);
        arb_mul(u, x, x, wp); arb_neg(u, u); arb_log1p(u, u, wp);                 /* log(1 - x^2) */
        arb_mul(t, u, x, wp); arb_mul_2exp_si(t, t, -1); arb_sub(O, O, t, wp);
        arb_mul(t, u, x, wp); arb_set_ui(H, k - 1); arb_div_ui(H, H, k, wp); arb_div(t, t, H, wp); arb_sub(T, T, t, wp);
    }
    _arb_vec_clear(c.SA, c.nblocks); _arb_vec_clear(c.SO, c.nblocks); _arb_vec_clear(c.Z, c.nblocks); _arb_vec_clear(c.W, c.nblocks);
    arb_clear(H); arb_clear(x); arb_clear(t); arb_clear(u);
}

static void A_ref_zeta(arb_t res, slong prec, int threads)
{
    arb_t SAh, O, T, t; arb_init(SAh); arb_init(O); arb_init(T); arb_init(t);
    zeta_logsums(SAh, O, T, 0, 0, prec, threads);
    arb_const_log2(t, prec + 64); arb_mul_2exp_si(t, t, -1); arb_add(res, SAh, t, prec);
    arb_clear(SAh); arb_clear(O); arb_clear(T); arb_clear(t);
}
static void C_ref_zeta(arb_t res, slong prec, int threads)
{
    arb_t SAh, O, T; arb_init(SAh); arb_init(O); arb_init(T);
    zeta_logsums(SAh, O, T, 1, 0, prec, threads);
    arb_add(res, SAh, O, prec);
    arb_clear(SAh); arb_clear(O); arb_clear(T);
}
static void K_ref_zeta(arb_t res, slong prec, int threads)
{
    arb_t SAh, O, T, t; arb_init(SAh); arb_init(O); arb_init(T); arb_init(t);
    zeta_logsums(SAh, O, T, 1, 1, prec, threads);
    arb_const_log2(t, prec + 64); arb_div(res, t, T, prec);
    arb_clear(SAh); arb_clear(O); arb_clear(T); arb_clear(t);
}

/* ======================= reference: Euler-Maclaurin =======================
   sum_{k>=k0} F(k) = sum_{k0<=k<M} F(k) + int_M^oo F + F(M)/2 - sum_j B_2j/(2j) c_{2j-1},
   c_i the Taylor coefficients of F at M, for the original definitions
     A: F = log x/(x^2-1);  C: F = log x/(x(x+1));  T: F = log(1 + 1/(x(x+2)))/x. */
enum { EM_A, EM_C, EM_T };

typedef struct { int which; ulong k0, M; slong wp, nblocks; arb_ptr part; } emctx;
#define EMBLK 256

static void em_direct_term(arb_t res, int which, ulong k, slong wp)
{
    arb_t t, u;
    arb_init(t); arb_init(u);
    if (which == EM_A)
    {
        arb_log_ui(t, k, wp); arb_set_ui(u, k); arb_mul_ui(u, u, k, wp); arb_sub_ui(u, u, 1, wp); arb_div(res, t, u, wp);
    }
    else if (which == EM_C)
    {
        arb_log_ui(t, k, wp); arb_set_ui(u, k); arb_mul_ui(u, u, k + 1, wp); arb_div(res, t, u, wp);
    }
    else
    {
        arb_set_ui(u, k); arb_mul_ui(u, u, k + 2, wp); arb_inv(u, u, wp); arb_log1p(t, u, wp); arb_div_ui(res, t, k, wp);
    }
    arb_clear(t); arb_clear(u);
}

static void em_block(slong b, void * vctx)
{
    emctx * c = vctx;
    ulong k, k1 = c->k0 + b * EMBLK, k2 = FLINT_MIN(c->M, k1 + EMBLK);
    arb_t t; arb_init(t);
    arb_zero(c->part + b);
    for (k = k1; k < k2; k++) { em_direct_term(t, c->which, k, c->wp); arb_add(c->part + b, c->part + b, t, c->wp); }
    arb_clear(t);
}

/* Taylor coefficients of F(M + t) = L(t)/q(t), generated one at a time (jet_stream_t), where
   L = sum_a w_a log(M + a + t) for a = 0, 1, 2 and q = q0 + q1 t + q2 t^2:
   q0 F_n = L_n - q1 F_{n-1} - q2 F_{n-2}, with L_n = sum_a w_a (-1)^(n-1) (M+a)^-n / n for n >= 1. */
typedef struct
{
    ulong M, q0, q1, q2;
    slong w[3], n, prec;
    arb_t L0, F1, F2, p[3], inv[3], t;
} logjet_t;

static void logjet_init(logjet_t * J, ulong M, const slong * w, ulong q0, ulong q1, ulong q2, slong prec)
{
    slong a;
    J->M = M; J->q0 = q0; J->q1 = q1; J->q2 = q2; J->prec = prec;
    arb_init(J->L0); arb_init(J->F1); arb_init(J->F2); arb_init(J->t);
    for (a = 0; a < 3; a++)
    {
        J->w[a] = w[a];
        arb_init(J->p[a]); arb_init(J->inv[a]);
        arb_set_ui(J->inv[a], M + a); arb_inv(J->inv[a], J->inv[a], prec);
        if (w[a] != 0) { arb_log_ui(J->t, M + a, prec); arb_addmul_si(J->L0, J->t, w[a], prec); }
    }
    J->n = 0;
}

static void logjet_clear(logjet_t * J)
{
    slong a;
    arb_clear(J->L0); arb_clear(J->F1); arb_clear(J->F2); arb_clear(J->t);
    for (a = 0; a < 3; a++) { arb_clear(J->p[a]); arb_clear(J->inv[a]); }
}

static void logjet_restart(void * st)
{
    logjet_t * J = st; slong a;
    J->n = 0;
    for (a = 0; a < 3; a++) arb_one(J->p[a]);
}

static void logjet_next(arb_t c, void * st)
{
    logjet_t * J = st;
    slong a, n = J->n, prec = J->prec;
    if (n == 0)
        arb_set(c, J->L0);
    else
    {
        arb_zero(c);
        for (a = 0; a < 3; a++)
            if (J->w[a] != 0)
            {
                arb_mul(J->p[a], J->p[a], J->inv[a], prec);           /* (M+a)^-n */
                arb_addmul_si(c, J->p[a], J->w[a], prec);
            }
        arb_div_si(c, c, (n % 2) ? n : -n, prec);
    }
    if (n >= 1) arb_submul_ui(c, J->F1, J->q1, prec);
    if (n >= 2 && J->q2 != 0) arb_submul_ui(c, J->F2, J->q2, prec);
    arb_div_ui(c, c, J->q0, prec);
    arb_swap(J->F2, J->F1); arb_set(J->F1, c);
    J->n++;
}

static void em_logsum(arb_t res, int which, ulong k0, slong prec, int threads)
{
    ulong M = em_cutoff(prec);
    slong wp = prec + 64, len = em_length((double) M, prec) + 2, b, n;
    emctx c;
    arb_t S, I, t, lm, pw, F0;
    arb_init(S); arb_init(I); arb_init(t); arb_init(lm); arb_init(pw); arb_init(F0);
    /* direct part */
    c.which = which; c.k0 = k0; c.M = M; c.wp = wp; c.nblocks = (M - k0 + EMBLK - 1) / EMBLK;
    c.part = _arb_vec_init(c.nblocks);
    parallel_for(c.nblocks, em_block, &c, threads);
    for (b = 0; b < c.nblocks; b++) arb_add(S, S, c.part + b, wp);
    _arb_vec_clear(c.part, c.nblocks);
    /* Euler-Maclaurin corrections from the Taylor coefficients of F at M */
    {
        static const slong wA[3] = { 1, 0, 0 }, wT[3] = { -1, 2, -1 };
        logjet_t J; jet_stream_t js;
        if (which == EM_A)
            logjet_init(&J, M, wA, M * M - 1, 2 * M, 1, wp);                 /* log x/((x-1)(x+1)) */
        else if (which == EM_C)
            logjet_init(&J, M, wA, M * (M + 1), 2 * M + 1, 1, wp);           /* log x/(x(x+1)) */
        else   /* (2 log(x+1) - log x - log(x+2))/x: the constant terms cancel to O(1/M^2), so extra guard bits */
            logjet_init(&J, M, wT, M, 1, 0, wp + 2 * FLINT_BIT_COUNT(M) + 16);
        js.restart = logjet_restart; js.next = logjet_next; js.st = &J;
        em_bernoulli_stream(t, F0, &js, len, wp);
        logjet_clear(&J);
    }
    arb_sub(S, S, t, wp);
    arb_mul_2exp_si(t, F0, -1); arb_add(S, S, t, wp);
    /* int_M^oo F */
    arb_log_ui(lm, M, wp);
    arb_zero(I);
    if (which == EM_A)
    {
        /* sum_{n>=0} (log M/(2n+1) + 1/(2n+1)^2) M^-(2n+1) */
        arb_set_ui(pw, M); arb_inv(pw, pw, wp);
        for (n = 0; ; n++)
        {
            ulong o = 2 * n + 1;
            if (o * log2((double) M) > wp + 20) break;
            arb_div_ui(t, lm, o, wp); { arb_t v; arb_init(v); arb_set_ui(v, 1); arb_div_ui(v, v, o * o, wp); arb_add(t, t, v, wp); arb_clear(v); }
            arb_addmul(I, t, pw, wp);
            arb_div_ui(pw, pw, M, wp); arb_div_ui(pw, pw, M, wp);
        }
    }
    else if (which == EM_C)
    {
        /* sum_{m>=0} (-1)^m (log M/(m+1) + 1/(m+1)^2) M^-(m+1) */
        arb_set_ui(pw, M); arb_inv(pw, pw, wp);
        for (n = 0; ; n++)
        {
            ulong o = n + 1;
            if (o * log2((double) M) > wp + 20) break;
            { arb_t v; arb_init(v); arb_div_ui(t, lm, o, wp); arb_set_ui(v, 1); arb_div_ui(v, v, o * o, wp); arb_add(t, t, v, wp); arb_clear(v); }
            if (n % 2) arb_submul(I, t, pw, wp); else arb_addmul(I, t, pw, wp);
            arb_div_ui(pw, pw, M, wp);
        }
    }
    else
    {
        /* sum_{n>=1} (-1)^(n-1) (2 - 2^n)/(n^2 M^n) */
        arb_t p2; arb_init(p2);
        arb_set_ui(pw, M); arb_inv(pw, pw, wp); arb_set_ui(p2, 2);
        for (n = 1; ; n++)
        {
            if (n * log2(M / 2.0) > wp + 20) break;
            arb_sub_ui(t, p2, 2, wp); arb_neg(t, t); arb_mul(t, t, pw, wp); arb_div_ui(t, t, (ulong) n * n, wp);
            if (n % 2) arb_add(I, I, t, wp); else arb_sub(I, I, t, wp);
            arb_mul_2exp_si(p2, p2, 1); arb_div_ui(pw, pw, M, wp);
        }
        arb_clear(p2);
    }
    arb_add(res, S, I, wp);
    arb_clear(S); arb_clear(I); arb_clear(t); arb_clear(lm); arb_clear(pw); arb_clear(F0);
}

static void A_ref_em(arb_t res, slong prec, int threads) { em_logsum(res, EM_A, 2, prec, threads); }
static void C_ref_em(arb_t res, slong prec, int threads) { em_logsum(res, EM_C, 2, prec, threads); }
static void K_ref_em(arb_t res, slong prec, int threads)
{
    arb_t T, t; arb_init(T); arb_init(t);
    em_logsum(T, EM_T, 1, prec, threads);
    arb_const_log2(t, prec + 64); arb_div(res, t, T, prec);
    arb_clear(T); arb_clear(t);
}

const constant_t CONST_A340440 = {
    "A340440", "sum_{k>=2} log k/(k^2-1) (OEIS A340440)",
    logsums_setup, logsums_clear, A_dual, A_k, 2, A_finish, A_main, A_ref_zeta, A_ref_em, 2 };
const constant_t CONST_A085361 = {
    "A085361", "sum_{k>=1} log k/(k(k+1)) (OEIS A085361; exp(C-1) = Alladi-Grinstead)",
    logsums_setup, logsums_clear, C_dual, C_k, 2, C_finish, C_main, C_ref_zeta, C_ref_em, 2 };
const constant_t CONST_KMINUS1 = {
    "Kminus1", "Khinchin's harmonic mean K_{-1} = log 2 / sum_{k>=1} log(1+1/(k(k+2)))/k",
    logsums_setup, logsums_clear, K_dual, K_k, 2, K_finish, K_main, K_ref_zeta, K_ref_em, 2 };
