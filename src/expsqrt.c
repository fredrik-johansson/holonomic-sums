/*
    The stretched-exponential sum S = sum_{k>=1} e^(-sqrt k) = 1.6704068179663397212... (Lambda_{1/2}(0, 1) in the
    paper), by the kernel splitting of Proposition "expsplit" with r = 1/2, tau = 1, s = 0:

        S = sum_{k>=1} I_k + sqrt(pi) sum_{m>=1} J_m + M.

    The kernel is h(u) = sum_j c_j u^(-j/4 - 1), c_j = (-1)^j/(j! Gamma(-j/4)); the classes j = 4m + rr with
    rr = 1, 2, 3 contribute (the class rr = 0 vanishes at s = 0). Per class, with w = 1/u,
        h_rr(u) = kappa_rr w^(1 + rr/4) H_rr(w),  kappa_rr = 1/Gamma(-rr/4),  H_rr(w) = sum_m g_m w^m,
        g_0 = (-1)^rr/rr!,  g_{m+1}/g_m = -(m + 1 + rr/4)/((4m+rr+1)(4m+rr+2)(4m+rr+3)(4m+rr+4)),
    and H_rr satisfies prod_{i=0}^{3} (4 theta + rr - i) H = -w (theta + 1 + rr/4) H, theta = w d/dw.

    k-side (x = k^2 u0): I_k = sum_rr (-1)^rr [k^(rr/2) Q(1 - rr/4, x) S1 - e^-x u0^(-rr/4) S2/Gamma(1 - rr/4)],
        S1 = sum_m k^(2m)/(4m+rr)!,  S2 = sum_m k^(2m) G_m/(4m+rr)!,  G_m = sum_{i<=m} prod_{l=1}^{i} (1 - rr/4 - l)/x,
    one incomplete gamma function per class and two rational series (binary splitting).

    Dual side: J_m = sum_rr kappa_rr Z_rr(pi^2 m^2), Z_rr(c) = int_0^u0 u^(-t*) e^(-c/u) H_rr(1/u) du u^(...) with
    t* = 3/2 + rr/4, i.e. Z_rr(c) = sum_m g_m D_{a0 - m}(c), a0 = -1/2 - rr/4, D_a(c) = int_0^u0 u^(a-1) e^(-c/u) du.
    The vector Z_i = Z[theta^i H] (i = 0..3) and Phi_i = e^(-c/u0) u0^(1-t*) (theta^i H)(1/u0) satisfy
        c^2 Z' = -(A1 A0' + c A0') Z - (A1 + c) Phi,   Phi' = -Phi/u0,
    with A0 the companion matrix of prod (theta + (rr - i)/4), A0' = A0 + (t* - 1) I and A1 the matrix with last row
    (-(1 + rr/4)/256, -1/256, 0, 0). Z is evaluated at c = pi^2 m^2 by the bit-burst algorithm, from a dyadic
    starting point where the series in m gives Z exactly in terms of e^(-c0/u0) and one incomplete gamma function;
    the Taylor steps use the equivalent first-order moment-shift recurrence (see xst_leaf) instead of this system.

    Main term: M = 2 - (sqrt(pi)/2) T_{1/2} - (1 - T_1)/2,  T_w = -sum_rr kappa_rr sum_m g_m u0^(e_m)/e_m,
    e_m = -m - rr/4 + w - 1.

    Reference (--method em): Euler-Maclaurin summation; F(x) = e^-sqrt(x) satisfies 4 x F'' + 2 F' - F = 0,
    and int_M^oo F = 2 (sqrt(M) + 1) e^-sqrt(M).
*/
#include <math.h>
#include <stdlib.h>
#include "constants.h"

#define LOG2E 1.4426950408889634

static arb_t X_gam[4];        /* Gamma(rr/4), rr = 1, 2, 3 */
static arb_t X_kappa[4];      /* 1/Gamma(-rr/4) */
static arb_t X_ig1[4];        /* 1/Gamma(1 - rr/4) */
static arb_t X_u0p[4];        /* u0^(-rr/4) */
static arb_t X_main, X_sqrtpi;

/* ======================= k-side ======================= */

/* state (t_m, t_m g_m, t_m G_m), t_m = k^(2m)/(4m+rr)!; sums t_m and t_m G_m */
typedef struct { ulong K2; int rr; } xk_ctx;

static void xk_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * vctx)
{
    const xk_ctx * c = vctx;
    ulong b = 4 * m + c->rr;
    fmpz_set_ui(q, b + 1); fmpz_mul_ui(q, q, b + 2); fmpz_mul_ui(q, q, b + 3); fmpz_mul_ui(q, q, b + 4);
    fmpz_mul_2exp(q, q, 2);
    fmpz_set_ui(fmpz_mat_entry(T, 0, 0), 4 * c->K2);
    fmpz_mul_si(fmpz_mat_entry(T, 1, 1), U0_DEN, -(slong) b);
    fmpz_set(fmpz_mat_entry(T, 2, 1), fmpz_mat_entry(T, 1, 1));
    fmpz_set_ui(fmpz_mat_entry(T, 2, 2), 4 * c->K2);
    fmpz_set(fmpz_mat_entry(T, 3, 0), q);
    fmpz_set(fmpz_mat_entry(T, 4, 2), q);
}

static slong xk_len(slong k, int rr, double x, slong W, double * peak)
{
    /* log2 |t_m| and log2 sum |g_i| */
    double lt = -lgamma(rr + 1.0) / log(2.0), lg = 0, lG = 0, mx = lt, cur;
    slong m;
    for (m = 0; ; m++)
    {
        cur = lt + FLINT_MAX(0, lG);
        mx = FLINT_MAX(mx, cur);
        if (m > 4 && cur < mx - W - 64 && cur < -(double) W) break;
        lt += 2 * log2((double) k) - log2((4.0 * m + rr + 1) * (4.0 * m + rr + 2) * (4.0 * m + rr + 3) * (4.0 * m + rr + 4));
        lg += log2((4.0 * m + rr) / 4.0) - log2(x);
        lG = (lg > lG) ? lg + 1 : lG + 1e-9;
    }
    *peak = mx;
    return m + 2;
}

static void X_k(arb_t res, slong idx, slong prec, void * unused)
{
    slong k = idx + 1, W, N;
    int rr;
    double x = (double) k * k * U0_D, peak;
    arb_t xa, em, B, t, u, sk, acc;
    arb_ptr x0, sm;
    xk_ctx c;
    bs_t Bs;
    (void) unused;
    if (-x * LOG2E + sqrt((double) k) * LOG2E + 3 * log2(k + 1.0) < -(prec + 64)) { arb_zero(res); return; }
    arb_init(xa); arb_init(em); arb_init(B); arb_init(t); arb_init(u); arb_init(sk); arb_init(acc);
    x0 = _arb_vec_init(3); sm = _arb_vec_init(2);
    arb_set_ui(xa, (ulong) k * k); arb_mul_2exp_si(xa, xa, -2 * U0_EXP);
    for (rr = 1; rr <= 3; rr++)
    {
        fmpq_t a;
        fmpq_init(a);
        /* the pieces have size up to e^-x 2^peak; the result is about e^-x */
        N = xk_len(k, rr, x, prec + 64 - (slong) (x * LOG2E), &peak);
        W = prec + 64 - (slong) (x * LOG2E) + (slong) FLINT_MAX(peak, 0) + 32;
        if (W < 64) W = 64;
        c.K2 = (ulong) k * k; c.rr = rr;
        Bs.d = 3; Bs.s = 2; Bs.leaf = xk_leaf; Bs.ctx = &c;
        arb_one(x0); arb_div_ui(x0, x0, rr == 1 ? 1 : (rr == 2 ? 2 : 6), W + 32);
        arb_set(x0 + 1, x0); arb_set(x0 + 2, x0);
        bs_eval(NULL, sm, x0, 0, N, &Bs, W + 32);
        /* B = Q(1 - rr/4, x) */
        fmpq_set_si(a, 4 - rr, 4);
        gamma_upper_fmpq_exact(B, a, xa, X_gam[4 - rr], W + 32);
        arb_mul(B, B, X_ig1[rr], W + 32);
        /* k^(rr/2) */
        if (rr == 2) arb_set_ui(sk, k);
        else { arb_sqrt_ui(sk, k, W + 32); if (rr == 3) arb_mul_ui(sk, sk, k, W + 32); }
        arb_mul(t, sk, B, W + 32); arb_mul(t, t, sm, W + 32);
        arb_neg(em, xa); arb_exp(em, em, W + 32);
        arb_mul(u, em, X_u0p[rr], W + 32); arb_mul(u, u, X_ig1[rr], W + 32); arb_mul(u, u, sm + 1, W + 32);
        arb_sub(t, t, u, W + 32);
        if (rr % 2) arb_sub(acc, acc, t, prec + 64); else arb_add(acc, acc, t, prec + 64);
        fmpq_clear(a);
    }
    arb_set(res, acc);
    arb_clear(xa); arb_clear(em); arb_clear(B); arb_clear(t); arb_clear(u); arb_clear(sk); arb_clear(acc);
    _arb_vec_clear(x0, 3); _arb_vec_clear(sm, 2);
}

/* ======================= dual side ======================= */

/* integer matrices (scaled): a0p = 256 A0', a1 = 1024 A1 (only the last row), n0p = a1 a0p = 2^18 A1 A0' */
typedef struct { fmpz a0p[16], a1[16], n0p[16]; } xsys_t;
static xsys_t XS[4];

static void xsys_init(xsys_t * S, int rr)
{
    /* monic prod_{i=0}^{3} (theta + (rr - i)/4), times 256: prod (4 theta + rr - i) */
    slong cf[5] = {1, 0, 0, 0, 0}, i, j, l;
    slong ncf = 1;
    for (i = 0; i < 4; i++)
    {
        slong nw[5] = {0, 0, 0, 0, 0};
        for (j = 0; j < ncf; j++) { nw[j + 1] += 4 * cf[j]; nw[j] += (rr - i) * cf[j]; }
        ncf++;
        for (j = 0; j < 5; j++) cf[j] = nw[j];
    }
    /* cf[4] = 256; A0 = companion of cf/256: A0[i][i+1] = 1, A0[3][d] = -cf[d]/256 */
    for (i = 0; i < 16; i++) { fmpz_init(S->a0p + i); fmpz_init(S->a1 + i); fmpz_init(S->n0p + i); }
    for (i = 0; i < 3; i++) fmpz_set_ui(S->a0p + 4 * i + i + 1, 256);
    for (j = 0; j < 4; j++) fmpz_set_si(S->a0p + 12 + j, -cf[j]);
    /* A0' = A0 + (t* - 1) I, t* - 1 = (2 + rr)/4 */
    for (i = 0; i < 4; i++) fmpz_add_ui(S->a0p + 5 * i, S->a0p + 5 * i, 64 * (2 + rr));
    /* A1 last row (-(1 + rr/4)/256, -1/256, 0, 0), times 1024 */
    fmpz_set_si(S->a1 + 12, -(4 + rr)); fmpz_set_si(S->a1 + 13, -4);
    for (i = 0; i < 4; i++)
        for (j = 0; j < 4; j++)
            for (l = 0; l < 4; l++)
                fmpz_addmul(S->n0p + 4 * i + j, S->a1 + 4 * i + l, S->a0p + 4 * l + j);
}

static void xsys_clear(xsys_t * S)
{
    slong i;
    for (i = 0; i < 16; i++) { fmpz_clear(S->a0p + i); fmpz_clear(S->a1 + i); fmpz_clear(S->n0p + i); }
}

/* Taylor step c0 = C/2^e -> c1 = C1/2^E (h = H/2^E) by the moment shift: the derivatives of
   Z_t[G] (G = (theta_w^i H)_i) are -dZ_t/dc = Z_{t+1}, and integration by parts with the equation of H gives
       (c I + N) Z_{t+1} = (A0 + (t - 1) I) Z_t + e^(-c/u0) u0^(1-t) G(u0),   N = -A1,  N^2 = 0,
   so (c I + N)^-1 = (I - N/c)/c. With T_j = (-h)^j Z_{t*+j}(c0)/j! and Phi_j = (-h)^j e^(-c0/u0) u0^(1-t*-j) G(u0)/j!:
       q T_{j+1} = -H 2^e (1024 C I - n 2^e) ((a0p + 256 j I) T_j + 256 Phi_j),
       q Phi_{j+1} = -H ud 2^18 C^2 Phi_j,     q = 2^(E+18) C^2 (j+1),
   with n = 1024 N, a0p = 256 (A0 + (t*-1) I), ud = 1/u0; Z(c1) = sum_j T_j. State (T_j, Phi_j) of dimension 8. */
typedef struct { const xsys_t * S; fmpz_t C, H; slong e, E; int rr; } xst_ctx;

static void xst_leaf(fmpz_mat_t T, fmpz_t q, slong j, const void * vctx)
{
    const xst_ctx * c = vctx;
    const xsys_t * S = c->S;
    slong e = c->e, E = c->E, i, l;
    fmpz_t C2, He, t, m1, m3a, m3b;
    fmpz M2[16], P[16];
    fmpz_init(C2); fmpz_init(He); fmpz_init(t); fmpz_init(m1); fmpz_init(m3a); fmpz_init(m3b);
    for (i = 0; i < 16; i++) { fmpz_init(M2 + i); fmpz_init(P + i); }
    fmpz_mul(C2, c->C, c->C);
    fmpz_mul_ui(q, C2, j + 1); fmpz_mul_2exp(q, q, 18 + E);
    fmpz_mul_2exp(He, c->H, e); fmpz_neg(He, He);
    /* M2 = a0p + 256 j I */
    for (i = 0; i < 16; i++) fmpz_set(M2 + i, S->a0p + i);
    for (i = 0; i < 4; i++) fmpz_add_ui(M2 + 5 * i, M2 + 5 * i, 256 * j);
    /* M1 = 1024 C I - n 2^e, n row 3 = (4 + rr, 4, 0, 0): P = M1 M2 */
    fmpz_mul_2exp(m1, c->C, 10);
    fmpz_set_ui(m3a, 4 + c->rr); fmpz_mul_2exp(m3a, m3a, e);
    fmpz_set_ui(m3b, 4); fmpz_mul_2exp(m3b, m3b, e);
    for (i = 0; i < 4; i++)
        for (l = 0; l < 4; l++)
        {
            fmpz_mul(P + 4 * i + l, m1, M2 + 4 * i + l);
            if (i == 3) { fmpz_submul(P + 12 + l, m3a, M2 + l); fmpz_submul(P + 12 + l, m3b, M2 + 4 + l); }
        }
    for (i = 0; i < 4; i++)
    {
        for (l = 0; l < 4; l++)
        {
            fmpz_mul(fmpz_mat_entry(T, i, l), P + 4 * i + l, He);
            /* Phi block: He 256 M1 */
            fmpz_zero(t);
            if (i == l) fmpz_set(t, m1);
            if (i == 3 && l == 0) fmpz_neg(t, m3a);
            if (i == 3 && l == 1) fmpz_neg(t, m3b);
            if (!fmpz_is_zero(t)) { fmpz_mul(t, t, He); fmpz_mul_2exp(t, t, 8); fmpz_set(fmpz_mat_entry(T, i, 4 + l), t); }
        }
    }
    fmpz_mul(t, U0_DEN, C2); fmpz_mul_2exp(t, t, 18); fmpz_mul(t, t, c->H); fmpz_neg(t, t);
    for (i = 0; i < 4; i++)
    {
        fmpz_set(fmpz_mat_entry(T, 4 + i, 4 + i), t);
        fmpz_set(fmpz_mat_entry(T, 8 + i, i), q);
    }
    fmpz_clear(C2); fmpz_clear(He); fmpz_clear(t); fmpz_clear(m1); fmpz_clear(m3a); fmpz_clear(m3b);
    for (i = 0; i < 16; i++) { fmpz_clear(M2 + i); fmpz_clear(P + i); }
}

/* Z (4) and Phi (4) at c0 = C/2^e -> at c1 = C1/2^E */
static void xstep(arb_ptr Z, arb_ptr Phi, int rr, const fmpz_t C, slong e, const fmpz_t C1, slong E, slong wp)
{
    xst_ctx c;
    bs_t Bs;
    arb_ptr x0, sm;
    arb_t t;
    slong L, i;
    double lc, ldel, lsum, t0 = 1.5 + rr / 4.0;
    fmpz_init(c.C); fmpz_init(c.H);
    fmpz_set(c.C, C);
    fmpz_mul_2exp(c.H, C, E - e); fmpz_sub(c.H, C1, c.H);
    c.e = e; c.E = E; c.S = &XS[rr]; c.rr = rr;
    if (fmpz_is_zero(c.H)) { fmpz_clear(c.C); fmpz_clear(c.H); return; }
    lc = fmpz_dlog(C) / log(2) - e;
    ldel = (double) fmpz_bits(c.H) - E;
    lsum = 0;
    for (L = 1; ; L++)
    {
        lsum += ldel + log2(FLINT_MAX(1.0 / U0_D, (L + t0 + 1) / pow(2.0, lc))) - log2((double) L) + 1;
        if (L >= 2 && lsum < -(wp + 64)) break;
    }
    L += 2;
    x0 = _arb_vec_init(8); sm = _arb_vec_init(4); arb_init(t);
    _arb_vec_set(x0, Z, 4);
    _arb_vec_set(x0 + 4, Phi, 4);
    Bs.d = 8; Bs.s = 4; Bs.leaf = xst_leaf; Bs.ctx = &c;
    { double t0 = cpu_seconds();
    bs_eval(NULL, sm, x0, 0, L, &Bs, wp + 64);
    if (getenv("HOLSUM_PROF")) flint_fprintf(stderr, "xstep rr=%d e=%wd E=%wd L=%wd wp=%wd %.3f s\n", rr, e, E, L, wp, cpu_seconds() - t0); }
    _arb_vec_set(Z, sm, 4);
    /* Phi(c1) = Phi(c0) e^(-h/u0) */
    arb_set_fmpz(t, c.H); arb_mul_2exp_si(t, t, -E); arb_mul_fmpz(t, t, U0_DEN, ARF_PREC_EXACT); arb_neg(t, t);
    arb_exp(t, t, wp + 64);
    for (i = 0; i < 4; i++) arb_mul(Phi + i, Phi + i, t, wp + 64);
    _arb_vec_clear(x0, 8); _arb_vec_clear(sm, 4); arb_clear(t);
    fmpz_clear(c.C); fmpz_clear(c.H);
}

/* starting values at c0 = C/2^e: Z_i = E u0^a0 sum_m g_m m^i al_m + D_a0 sum_m g_m m^i be_m,
   Phi_i = E u0^a0 sum_m g_m m^i ud^m, where D_{a0-m} = u0^a0 al_m E + be_m D_a0.
   State v1 = g_m al_m, v2 = g_m ud^m, v3 = g_m be_m (al_0 = 0, be_0 = 1):
   16 D4 C v1' = -(4m+4+rr) 2^e (4 v2 + (2+rr+4m) v1),  16 D4 C v2' = -(4m+4+rr) 4 ud C v2,
   16 D4 C v3' = -(4m+4+rr)(2+rr+4m) 2^e v3; sums m^i v1, m^i v2, m^i v3. */
typedef struct { fmpz_t C; slong e; int rr; } xi_ctx;

static void xi_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * vctx)
{
    const xi_ctx * c = vctx;
    slong b = 4 * m + c->rr, i, j;
    fmpz_t f, mp;
    fmpz_init(f); fmpz_init(mp);
    fmpz_set_ui(q, b + 1); fmpz_mul_ui(q, q, b + 2); fmpz_mul_ui(q, q, b + 3); fmpz_mul_ui(q, q, b + 4);
    fmpz_mul_ui(q, q, 16); fmpz_mul(q, q, c->C);
    fmpz_set_si(f, -(b + 4)); fmpz_mul_2exp(f, f, c->e);              /* -(4m+4+rr) 2^e */
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 1), f, 4);
    fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), f, b + 2);
    fmpz_mul_ui(fmpz_mat_entry(T, 2, 2), f, b + 2);
    fmpz_set_si(f, -(b + 4)); fmpz_mul_ui(f, f, 4); fmpz_mul(f, f, U0_DEN); fmpz_mul(f, f, c->C);
    fmpz_set(fmpz_mat_entry(T, 1, 1), f);
    fmpz_set(mp, q);
    for (i = 0; i < 4; i++)
    {
        for (j = 0; j < 3; j++) fmpz_set(fmpz_mat_entry(T, 3 + 3 * i + j, j), mp);
        fmpz_mul_ui(mp, mp, m);
    }
    fmpz_clear(f); fmpz_clear(mp);
}

static void xinit(arb_ptr Z, arb_ptr Phi, int rr, const fmpz_t C, slong e, slong wp)
{
    xi_ctx c;
    bs_t Bs;
    arb_t c0, y, E, D, t, ua0;
    arb_ptr x0, sm;
    slong N, i, W;
    double cd, l1, l2, l3, mx, ud = 1.0 / U0_D;
    fmpz_init_set(c.C, C); c.e = e; c.rr = rr;
    arb_init(c0); arb_init(y); arb_init(E); arb_init(D); arb_init(t); arb_init(ua0);
    x0 = _arb_vec_init(3); sm = _arb_vec_init(12);
    arb_set_fmpz(c0, C); arb_mul_2exp_si(c0, c0, -e);
    cd = arf_get_d(arb_midref(c0), ARF_RND_NEAR);
    W = wp + 64;
    /* length: magnitudes of v1, v2, v3 (v3 scaled by u0/c0, like D_a0 against u0^a0 E) */
    l1 = -1e300; l2 = -lgamma(rr + 1.0) / log(2.0); l3 = l2 + log2(U0_D / cd); mx = l2;
    for (N = 0; ; N++)
    {
        double g = log2((4.0 * N + 4 + rr) / 4.0) - log2((4.0 * N + rr + 1) * (4.0 * N + rr + 2) * (4.0 * N + rr + 3) * (4.0 * N + rr + 4));
        double n1, n2, n3, cur;
        cur = FLINT_MAX(l1, FLINT_MAX(l2, l3)) + 2 * log2(N + 1.0);
        mx = FLINT_MAX(mx, cur);
        if (N > 4 && cur < mx - W - 64) break;
        n2 = l2 + g + log2(ud);
        n1 = g - log2(cd) + log2(4 * exp2(l2 - FLINT_MAX(l1, l2)) + (2 + rr + 4.0 * N) * exp2(l1 - FLINT_MAX(l1, l2))) + FLINT_MAX(l1, l2);
        n3 = l3 + g + log2((2 + rr + 4.0 * N) / 4.0) - log2(cd);
        l1 = n1; l2 = n2; l3 = n3;
    }
    N += 2;
    Bs.d = 3; Bs.s = 12; Bs.leaf = xi_leaf; Bs.ctx = &c;
    arb_zero(x0); arb_one(x0 + 1); arb_div_ui(x0 + 1, x0 + 1, rr == 1 ? 1 : (rr == 2 ? 2 : 6), W); arb_set(x0 + 2, x0 + 1);
    if (rr % 2) { arb_neg(x0 + 1, x0 + 1); arb_neg(x0 + 2, x0 + 2); }
    bs_eval(NULL, sm, x0, 0, N, &Bs, W);
    /* E = e^(-y0), y0 = c0/u0; D_a0 = c0^a0 Gamma(-a0, y0), -a0 = 1/2 + rr/4 */
    arb_mul_fmpz(y, c0, U0_DEN, ARF_PREC_EXACT);
    arb_neg(E, y); arb_exp(E, E, W);
    if (rr == 2) arb_set(D, E);
    else
    {
        fmpq_t a; fmpq_init(a);
        fmpq_set_si(a, rr == 1 ? 3 : 1, 4);
        gamma_upper_fmpq_exact(D, a, y, X_gam[rr == 1 ? 3 : 1], W);
        if (rr == 3)
        {
            arb_mul_2exp_si(D, D, -2);
            arb_root_ui(t, y, 4, W); arb_mul(t, t, E, W); arb_add(D, D, t, W);
        }
        fmpq_clear(a);
    }
    /* c0^a0 = 1/(c0^(1/2) c0^(rr/4)) */
    arb_root_ui(t, c0, 4, W); arb_pow_ui(t, t, rr + 2, W); arb_div(D, D, t, W);
    /* u0^a0 = ud^(1/2 + rr/4) = 2^(a (2 + rr)/2) */
    arb_set_fmpz(ua0, U0_DEN); arb_root_ui(ua0, ua0, 4, W); arb_pow_ui(ua0, ua0, 2 + rr, W);
    arb_mul(ua0, ua0, E, W);
    for (i = 0; i < 4; i++)
    {
        arb_mul(Z + i, sm + 3 * i, ua0, W);
        arb_addmul(Z + i, sm + 3 * i + 2, D, W);
        arb_mul(Phi + i, sm + 3 * i + 1, ua0, W);
    }
    fmpz_clear(c.C);
    arb_clear(c0); arb_clear(y); arb_clear(E); arb_clear(D); arb_clear(t); arb_clear(ua0);
    _arb_vec_clear(x0, 3); _arb_vec_clear(sm, 12);
}

static void X_dual(arb_t res, slong idx, slong prec, void * unused)
{
    slong m = idx + 1, wp, e, E, Efin;
    int rr;
    double cd = 9.8696044010893586 * m * m;
    arb_t c, acc;
    arb_ptr Z, Phi;
    fmpz_t C, C1;
    (void) unused;
    wp = prec + 64 - (slong) (cd / U0_D * LOG2E) + 16;
    if (wp < 64) { arb_zero(res); return; }
    arb_init(c); arb_init(acc); fmpz_init(C); fmpz_init(C1);
    Z = _arb_vec_init(4); Phi = _arb_vec_init(4);
    arb_const_pi(c, wp + 128); arb_mul_ui(c, c, m, wp + 128); arb_sqr(c, c, wp + 128);
    Efin = wp + 64;
    for (rr = 1; rr <= 3; rr++)
    {
        /* starting point with wp/256 bits, between 64 and 1024: the series for the starting values costs about
           as much as the first Taylor steps it saves */
        e = getenv("HOLSUM_XE") ? atol(getenv("HOLSUM_XE")) : FLINT_MAX(64, FLINT_MIN(1024, wp / 256));
        arf_get_fmpz_fixed_si(C, arb_midref(c), -e);
        { double t0 = cpu_seconds(); xinit(Z, Phi, rr, C, e, wp);
          if (getenv("HOLSUM_PROF")) flint_fprintf(stderr, "xinit rr=%d %.3f s\n", rr, cpu_seconds() - t0); }
        for (;;)
        {
            int last;
            E = 4 * e;
            last = (E >= Efin);
            if (last) E = FLINT_MAX(Efin, e + 1);
            arf_get_fmpz_fixed_si(C1, arb_midref(c), -E);
            xstep(Z, Phi, rr, C, e, C1, E, wp);
            fmpz_swap(C, C1);
            e = E;
            if (last) break;
        }
        /* distance to c: |Z'| <~ |Z| (1/u0 + 4) */
        {
            mag_t r, z;
            mag_init(r); mag_init(z);
            mag_set_ui_2exp_si(r, 1, -e + 1); mag_add(r, r, arb_radref(c));
            arb_get_mag(z, Z); mag_mul_ui(z, z, (ulong) (1.0 / U0_D) + 4);
            mag_mul(r, r, z);
            arb_add_error_mag(Z, r);
            mag_clear(r); mag_clear(z);
        }
        arb_addmul(acc, Z, X_kappa[rr], wp);
    }
    arb_mul(res, acc, X_sqrtpi, prec + 64);
    arb_clear(c); arb_clear(acc); fmpz_clear(C); fmpz_clear(C1);
    _arb_vec_clear(Z, 4); _arb_vec_clear(Phi, 4);
}

/* ======================= setup, main term ======================= */

/* sum_m g_m ud^m / (4m + rr + sh): s_{m+1}/s_m = -(4m+4+rr) ud (4m+rr+sh) / (4 D4 (4m+4+rr+sh)) */
typedef struct { int rr, sh; } xt_ctx;
static void xt_leaf(fmpz_mat_t T, fmpz_t q, slong m, const void * vctx)
{
    const xt_ctx * c = vctx;
    slong b = 4 * m + c->rr;
    fmpz_set_ui(q, b + 1); fmpz_mul_ui(q, q, b + 2); fmpz_mul_ui(q, q, b + 3); fmpz_mul_ui(q, q, b + 4);
    fmpz_mul_ui(q, q, 4 * (b + 4 + c->sh));
    fmpz_mul_si(fmpz_mat_entry(T, 0, 0), U0_DEN, -(b + 4) * (b + c->sh));
    fmpz_set(fmpz_mat_entry(T, 1, 0), q);
}

static slong expsqrt_dual_count(slong prec)
{
    slong m;
    for (m = 1; ; m++)
        if (9.8696044010893586 * m * m / U0_D * LOG2E > prec + 80) return m;
}

static slong expsqrt_k_count(slong prec)
{
    slong k;
    for (k = 2; ; k++)
        if (-(double) k * k * U0_D * LOG2E + sqrt((double) k) * LOG2E + 3 * log2(k + 1.0) < -(prec + 64)) return k;
}

static void expsqrt_setup(slong prec)
{
    slong wp = prec + 256, rr, N;
    arb_t t, T12, T1, s, f;
    fmpq_t a;
    arb_init(t); arb_init(T12); arb_init(T1); arb_init(s); arb_init(f); fmpq_init(a);
    arb_init(X_main); arb_init(X_sqrtpi);
    arb_const_sqrt_pi(X_sqrtpi, wp);
    for (rr = 0; rr < 4; rr++) { arb_init(X_gam[rr]); arb_init(X_kappa[rr]); arb_init(X_ig1[rr]); arb_init(X_u0p[rr]); }
    for (rr = 1; rr <= 3; rr++)
    {
        fmpq_set_si(a, rr, 4); arb_gamma_fmpq(X_gam[rr], a, wp);
        xsys_init(&XS[rr], rr);
    }
    /* 1/Gamma(1 - rr/4) = 1/Gamma((4 - rr)/4); 1/Gamma(-rr/4) = -(rr/4)/Gamma(1 - rr/4) */
    for (rr = 1; rr <= 3; rr++)
    {
        arb_inv(X_ig1[rr], X_gam[4 - rr], wp);
        arb_mul_si(X_kappa[rr], X_ig1[rr], -rr, wp); arb_mul_2exp_si(X_kappa[rr], X_kappa[rr], -2);
        arb_set_fmpz(X_u0p[rr], U0_DEN); arb_root_ui(X_u0p[rr], X_u0p[rr], 4, wp); arb_pow_ui(X_u0p[rr], X_u0p[rr], rr, wp);
    }
    /* T_w = -sum_rr kappa u0^(w-1-rr/4) sum_m g_m ud^m/(-m - rr/4 + w - 1)
           = 4 sum_rr kappa u0^(w-1-rr/4) sum_m g_m ud^m/(4m + rr + 4(1 - w)) */
    for (rr = 1; rr <= 3; rr++)
    {
        int sh;
        for (sh = 0; sh <= 2; sh += 2)            /* sh = 4(1 - w): w = 1 -> 0, w = 1/2 -> 2 */
        {
            xt_ctx c; bs_t B; arb_t x0, sm;
            double l = 0;
            arb_init(x0); arb_init(sm);
            c.rr = rr; c.sh = sh;
            for (N = 0; ; N++)
            {
                l += log2((4.0 * N + 4 + rr) / U0_D) - log2(4 * (4.0 * N + rr + 1) * (4.0 * N + rr + 2) * (4.0 * N + rr + 3) * (4.0 * N + rr + 4));
                if (N > 2 && l < -(wp + 64)) break;
            }
            N += 2;
            B.d = 1; B.s = 1; B.leaf = xt_leaf; B.ctx = &c;
            arb_one(x0); arb_div_ui(x0, x0, (rr == 1 ? 1 : (rr == 2 ? 2 : 6)) * (rr + sh), wp);
            if (rr % 2) arb_neg(x0, x0);
            bs_eval(NULL, sm, x0, 0, N, &B, wp);
            /* u0^(w - 1 - rr/4) = ud^(1 - w) u0^(-rr/4); 1 - w = sh/4 */
            arb_set_fmpz(f, U0_DEN); arb_root_ui(f, f, 4, wp); arb_pow_ui(f, f, sh, wp);
            arb_mul(f, f, X_u0p[rr], wp);
            arb_mul(sm, sm, f, wp); arb_mul(sm, sm, X_kappa[rr], wp); arb_mul_2exp_si(sm, sm, 2);
            if (sh == 0) arb_add(T1, T1, sm, wp); else arb_add(T12, T12, sm, wp);
            arb_clear(x0); arb_clear(sm);
        }
    }
    /* M = 2 - (sqrt(pi)/2) T_{1/2} - (1 - T_1)/2 */
    arb_mul(t, X_sqrtpi, T12, wp); arb_mul_2exp_si(t, t, -1);
    arb_set_ui(X_main, 2); arb_sub(X_main, X_main, t, wp);
    arb_sub_ui(t, T1, 1, wp); arb_mul_2exp_si(t, t, -1);
    arb_add(X_main, X_main, t, wp);
    arb_clear(t); arb_clear(T12); arb_clear(T1); arb_clear(s); arb_clear(f); fmpq_clear(a);
}

static void expsqrt_clear(void)
{
    slong rr;
    for (rr = 0; rr < 4; rr++) { arb_clear(X_gam[rr]); arb_clear(X_kappa[rr]); arb_clear(X_ig1[rr]); arb_clear(X_u0p[rr]); }
    for (rr = 1; rr <= 3; rr++) xsys_clear(&XS[rr]);
    arb_clear(X_main); arb_clear(X_sqrtpi);
}

static void X_main_term(arb_t res) { arb_set(res, X_main); }
static void X_finish(arb_t res, const arb_t lin, slong prec) { arb_set_round(res, lin, prec + 64); }

/* ======================= reference: Euler-Maclaurin ======================= */

#define XEMBLK 512
typedef struct { ulong M; slong wp, nblocks; arb_ptr part; } xem_ctx;

static void xem_block(slong b, void * vctx)
{
    xem_ctx * c = vctx;
    ulong k, k0 = 1 + (ulong) b * XEMBLK, k1 = FLINT_MIN(c->M, k0 + XEMBLK);
    arb_t t;
    arb_init(t);
    for (k = k0; k < k1; k++)
    {
        arb_sqrt_ui(t, k, c->wp); arb_neg(t, t); arb_exp(t, t, c->wp);
        arb_add(c->part + b, c->part + b, t, c->wp);
    }
    arb_clear(t);
}

static void X_ref_em(arb_t res, slong prec, int threads)
{
    ulong M = em_cutoff(prec);
    slong wp = prec + 64, len, b;
    xem_ctx c;
    arb_t S, t, sq, f0, f1;
    fmpz_poly_t p2, p1, p0;
    ode_jet_t J; jet_stream_t js;
    len = em_length((double) M, prec) + 2;
    arb_init(S); arb_init(t); arb_init(sq); arb_init(f0); arb_init(f1);
    c.M = M; c.wp = wp; c.nblocks = (M - 1 + XEMBLK - 1) / XEMBLK; c.part = _arb_vec_init(c.nblocks);
    parallel_for(c.nblocks, xem_block, &c, threads);
    for (b = 0; b < c.nblocks; b++) arb_add(S, S, c.part + b, wp);
    _arb_vec_clear(c.part, c.nblocks);
    /* 4 x F'' + 2 F' - F = 0, F(M) = e^-sqrt(M), F'(M) = -F(M)/(2 sqrt M) */
    fmpz_poly_init(p2); fmpz_poly_init(p1); fmpz_poly_init(p0);
    fmpz_poly_set_coeff_ui(p2, 1, 4); fmpz_poly_set_coeff_ui(p1, 0, 2); fmpz_poly_set_coeff_si(p0, 0, -1);
    arb_sqrt_ui(sq, M, wp + 32);
    arb_neg(f0, sq); arb_exp(f0, f0, wp + 32);
    arb_div(f1, f0, sq, wp + 32); arb_mul_2exp_si(f1, f1, -1); arb_neg(f1, f1);
    ode_jet_init(&J, p2, p1, p0, M, f0, f1, wp + 32);
    js.restart = ode_jet_restart; js.next = ode_jet_next; js.st = &J;
    em_bernoulli_stream(t, f0, &js, len, wp);
    arb_sub(S, S, t, wp);
    arb_mul_2exp_si(t, f0, -1); arb_add(S, S, t, wp);
    /* int_M^oo = 2 (sqrt M + 1) e^-sqrt M */
    arb_add_ui(t, sq, 1, wp); arb_mul(t, t, f0, wp); arb_mul_2exp_si(t, t, 1);
    arb_add(res, S, t, prec);
    ode_jet_clear(&J);
    fmpz_poly_clear(p2); fmpz_poly_clear(p1); fmpz_poly_clear(p0);
    arb_clear(S); arb_clear(t); arb_clear(sq); arb_clear(f0); arb_clear(f1);
}

const constant_t CONST_EXPSQRT = {
    "expsqrt", "the stretched-exponential sum sum_{k>=1} exp(-sqrt k)",
    expsqrt_setup, expsqrt_clear, X_dual, X_k, 1, X_finish, X_main_term, NULL, X_ref_em, 2,
    expsqrt_k_count, expsqrt_dual_count, NULL };
