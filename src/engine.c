/* Shared engine for the theta-splitting programs; see engine.h. */
#include <math.h>
#include <pthread.h>
#include <time.h>
#include <sys/resource.h>
#include "engine.h"

fmpz_t U0_NUM, U0_DEN;
arb_t U0, SQRT_U0;
double U0_D;
slong U0_EXP;
int ENGINE_THREADS = 1;

void engine_set_u0(slong a, slong prec)
{
    fmpz_init(U0_NUM); fmpz_init(U0_DEN);
    fmpz_one(U0_NUM); fmpz_one(U0_DEN); fmpz_mul_2exp(U0_DEN, U0_DEN, 2 * a);
    arb_init(U0); arb_init(SQRT_U0);
    arb_one(U0); arb_mul_2exp_si(U0, U0, -2 * a);              /* exact */
    arb_one(SQRT_U0); arb_mul_2exp_si(SQRT_U0, SQRT_U0, -a);    /* exact */
    U0_D = ldexp(1.0, -2 * (int) a);
    U0_EXP = a;
    (void) prec;
}

void engine_clear(void)
{
    fmpz_clear(U0_NUM); fmpz_clear(U0_DEN); arb_clear(U0); arb_clear(SQRT_U0);
}

/* ======================= binary splitting ======================= */

static void shallow_init(fmpz_mat_t M, slong r, slong c)
{
    M->entries = flint_calloc(r * c, sizeof(fmpz)); M->r = r; M->c = c; M->stride = c;
}

static void bs_exact(fmpz_mat_t T, fmpz_t Q, slong a, slong b, const bs_t * B)
{
    slong d = B->d, s = B->s, i, j, m;
    fmpz_mat_t T2, L, P;
    fmpz_t Q2;
    if (b - a == 1)
    {
        fmpz_mat_zero(T);
        B->leaf(T, Q, a, B->ctx);
        return;
    }
    m = a + (b - a) / 2;
    fmpz_mat_init(T2, d + s, d); fmpz_init(Q2);
    bs_exact(T, Q, a, m, B);
    bs_exact(T2, Q2, m, b, B);
    /* [M2 0; S2 Q2 I] [M1; S1] */
    shallow_init(L, d + s, d + s);
    for (i = 0; i < d + s; i++)
        for (j = 0; j < d; j++)
            L->entries[i * (d + s) + j] = *fmpz_mat_entry(T2, i, j);
    for (i = 0; i < s; i++)
        L->entries[(d + i) * (d + s) + d + i] = *Q2;
    fmpz_mat_init(P, d + s, d);
    fmpz_mat_mul(P, L, T);
    flint_free(L->entries);
    fmpz_mat_swap(T, P);
    fmpz_mat_clear(P);
    fmpz_mul(Q, Q, Q2);
    fmpz_mat_clear(T2); fmpz_clear(Q2);
}

/* exact products below about 2 prec bits, ball products above */
static void bs_top(arb_mat_t T, arb_t Q, slong a, slong b, const bs_t * B, slong lim, slong prec)
{
    slong d = B->d, s = B->s, i, j, m;
    if (b - a <= lim)
    {
        fmpz_mat_t Te; fmpz_t Qe;
        fmpz_mat_init(Te, d + s, d); fmpz_init(Qe);
        bs_exact(Te, Qe, a, b, B);
        arb_mat_set_round_fmpz_mat(T, Te, prec);
        arb_set_round_fmpz(Q, Qe, prec);
        fmpz_mat_clear(Te); fmpz_clear(Qe);
    }
    else
    {
        arb_mat_t T2, L, P; arb_t Q2;
        m = a + (b - a) / 2;
        arb_mat_init(T2, d + s, d); arb_init(Q2);
        bs_top(T, Q, a, m, B, lim, prec);
        bs_top(T2, Q2, m, b, B, lim, prec);
        arb_mat_init(L, d + s, d + s);
        for (i = 0; i < d + s; i++)
            for (j = 0; j < d; j++)
                arb_set(arb_mat_entry(L, i, j), arb_mat_entry(T2, i, j));
        for (i = 0; i < s; i++)
            arb_set(arb_mat_entry(L, d + i, d + i), Q2);
        arb_mat_init(P, d + s, d);
        arb_mat_mul(P, L, T, prec);
        arb_mat_swap(T, P);
        arb_mul(Q, Q, Q2, prec);
        arb_mat_clear(P); arb_mat_clear(L); arb_mat_clear(T2); arb_clear(Q2);
    }
}

void bs_eval(arb_ptr xend, arb_ptr sums, arb_srcptr x0, slong a, slong b, const bs_t * B, slong prec)
{
    slong d = B->d, s = B->s, i, j, lim, lb;
    arb_mat_t T; arb_t Q;
    if (b <= a)
    {
        if (xend) _arb_vec_set(xend, x0, d);
        if (sums) _arb_vec_zero(sums, s);
        return;
    }
    {
        fmpz_mat_t Tl; fmpz_t ql;
        fmpz_mat_init(Tl, d + s, d); fmpz_init(ql);
        fmpz_mat_zero(Tl);
        B->leaf(Tl, ql, b - 1, B->ctx);
        lb = FLINT_ABS(fmpz_mat_max_bits(Tl)) + fmpz_bits(ql) + 1;
        fmpz_mat_clear(Tl); fmpz_clear(ql);
    }
    lim = FLINT_MAX(1, 2 * prec / lb);
    arb_mat_init(T, d + s, d); arb_init(Q);
    bs_top(T, Q, a, b, B, lim, prec);
    if (xend)
        for (i = 0; i < d; i++)
        {
            arb_zero(xend + i);
            for (j = 0; j < d; j++) arb_addmul(xend + i, arb_mat_entry(T, i, j), x0 + j, prec);
            arb_div(xend + i, xend + i, Q, prec);
        }
    if (sums)
        for (i = 0; i < s; i++)
        {
            arb_zero(sums + i);
            for (j = 0; j < d; j++) arb_addmul(sums + i, arb_mat_entry(T, d + i, j), x0 + j, prec);
            arb_div(sums + i, sums + i, Q, prec);
        }
    arb_mat_clear(T); arb_clear(Q);
}

void bs_product(arb_mat_t T, arb_t Q, slong a, slong b, const bs_t * B, slong prec)
{
    slong lb;
    fmpz_mat_t Tl; fmpz_t ql;
    fmpz_mat_init(Tl, B->d + B->s, B->d); fmpz_init(ql);
    fmpz_mat_zero(Tl);
    B->leaf(Tl, ql, b - 1, B->ctx);
    lb = FLINT_ABS(fmpz_mat_max_bits(Tl)) + fmpz_bits(ql) + 1;
    fmpz_mat_clear(Tl); fmpz_clear(ql);
    bs_top(T, Q, a, b, B, FLINT_MAX(1, 2 * prec / lb), prec);
}

/* ======================= Gamma(a, y), a in {0, 1/2} ======================= */

/* Legendre's continued fraction with positive elements (consecutive convergents enclose the value).
   y = p/q; a = 1/2: b_n = 2p (n even), 2 (odd), al_n = 2 q n, value 2 q x;
   a = 0: b_n = p (even), 1 (odd), al_n = q ceil(n/2), value q x. */
typedef struct { int half; fmpz_t p, q; } cf_ctx;

static void cf_leaf(fmpz_mat_t T, fmpz_t qq, slong n, const void * vctx)
{
    const cf_ctx * c = vctx;
    if (c->half)
    {
        if (n % 2 == 0) fmpz_mul_2exp(fmpz_mat_entry(T, 0, 0), c->p, 1); else fmpz_set_ui(fmpz_mat_entry(T, 0, 0), 2);
        fmpz_mul_ui(fmpz_mat_entry(T, 0, 1), c->q, 2 * n);
    }
    else
    {
        if (n % 2 == 0) fmpz_set(fmpz_mat_entry(T, 0, 0), c->p); else fmpz_one(fmpz_mat_entry(T, 0, 0));
        fmpz_mul_ui(fmpz_mat_entry(T, 0, 1), c->q, (n + 1) / 2);
    }
    fmpz_one(fmpz_mat_entry(T, 1, 0));
    fmpz_one(qq);
}

static int gamma_cf(arb_t G, int half, const fmpz_t p, const fmpz_t q, slong nsteps, slong W)
{
    cf_ctx c; arb_mat_t T; arb_t Q, b0, xa, xb, y, t;
    slong prec = W + 64, lim, d = 2, i, j, m;
    int ok;
    bs_t B;
    c.half = half; fmpz_init_set(c.p, p); fmpz_init_set(c.q, q);
    B.d = d; B.s = 0; B.leaf = cf_leaf; B.ctx = &c;
    arb_mat_init(T, 2, 2); arb_init(Q); arb_init(b0); arb_init(xa); arb_init(xb); arb_init(y); arb_init(t);
    lim = FLINT_MAX(2, 2 * prec / (2 * (fmpz_bits(p) + fmpz_bits(q) + FLINT_BIT_COUNT(nsteps)) + 4));
    bs_top(T, Q, 1, nsteps + 1, &B, lim, prec);
    (void) i; (void) j; (void) m;
    /* T = P^T, P = prod [b_n 1; al_n 0]; convergents (b0 P00 + P10)/P00 and (b0 P01 + P11)/P01 */
    if (half) arb_set_fmpz(b0, p), arb_mul_2exp_si(b0, b0, 1); else arb_set_fmpz(b0, p);
    arb_mul(xa, b0, arb_mat_entry(T, 0, 0), prec); arb_add(xa, xa, arb_mat_entry(T, 0, 1), prec);
    arb_div(xa, xa, arb_mat_entry(T, 0, 0), prec);
    arb_mul(xb, b0, arb_mat_entry(T, 1, 0), prec); arb_add(xb, xb, arb_mat_entry(T, 1, 1), prec);
    arb_div(xb, xb, arb_mat_entry(T, 1, 0), prec);
    arb_union(xa, xa, xb, prec);
    arb_set_fmpz(y, p); arb_div_fmpz(y, y, q, prec);
    arb_set_fmpz(t, q); if (half) arb_mul_2exp_si(t, t, 1);
    arb_div(t, t, xa, prec);
    if (half) { arb_sqrt(b0, y, prec); arb_mul(t, t, b0, prec); }
    arb_neg(y, y); arb_exp(y, y, prec); arb_mul(G, t, y, prec);
    ok = arb_rel_accuracy_bits(G) >= W;
    arb_mat_clear(T); arb_clear(Q); arb_clear(b0); arb_clear(xa); arb_clear(xb); arb_clear(y); arb_clear(t);
    fmpz_clear(c.p); fmpz_clear(c.q);
    return ok;
}

/* Ein(y) = sum_{n>=1} (-1)^(n+1) y^n / (n n!): state t_n = (-1)^(n+1) y^n/n!, sum t_n/n */
typedef struct { fmpz_t p, q; } ein_ctx;
static void ein_leaf(fmpz_mat_t T, fmpz_t qq, slong n, const void * vctx)
{
    const ein_ctx * c = vctx;
    fmpz_mul_ui(qq, c->q, (ulong) n * (n + 1));
    fmpz_mul_si(fmpz_mat_entry(T, 0, 0), c->p, -n);
    fmpz_mul_ui(fmpz_mat_entry(T, 1, 0), c->q, n + 1);
}

static void exact_pq(fmpz_t p, fmpz_t q, const arb_t y)
{
    fmpz_t ex; fmpz_init(ex);
    arf_get_fmpz_2exp(p, ex, arb_midref(y));
    fmpz_one(q);
    if (fmpz_sgn(ex) >= 0) fmpz_mul_2exp(p, p, fmpz_get_si(ex)); else fmpz_mul_2exp(q, q, -fmpz_get_si(ex));
    fmpz_clear(ex);
}

void gamma_upper_exact(arb_t G, int half, const arb_t y, slong wp)
{
    fmpq_t a; mag_t tol, AE; arb_t t, s;
    slong NN, wpu = wp + 20, wpl;
    double yd = arf_get_d(arb_midref(y), ARF_RND_NEAR);
    fmpz_t p, q;
    fmpq_init(a); mag_init(tol); mag_init(AE); arb_init(t); arb_init(s); fmpz_init(p); fmpz_init(q);
    if (half) fmpq_set_si(a, 1, 2); else fmpq_zero(a);
    exact_pq(p, q, y);
    /* tolerance: 2^-wpu e^-y y^(a-1) */
    arb_neg(t, y); arb_exp(t, t, 64);
    if (half) { arb_rsqrt(s, y, 64); arb_mul(t, t, s, 64); } else arb_div(t, t, y, 64);
    arb_get_mag_lower(tol, t);
    mag_mul_2exp_si(tol, tol, -wpu);
    /* asymptotic series when it is accurate enough */
    NN = _arb_hypgeom_gamma_upper_fmpq_inf_choose_N(AE, a, y, tol);
    if (NN != -1)
    {
        _arb_hypgeom_gamma_upper_fmpq_inf_bsplit(G, a, y, NN, wpu);
        arb_add_error_mag(G, AE);
        goto done;
    }
    {
        double ncf = pow(wpu / 2.4, 2) / yd + 1000, nlow;
        slong Nlow = -1;
        if (half)
        {
            Nlow = _arb_hypgeom_gamma_lower_fmpq_0_choose_N(AE, a, y, tol);
            nlow = (double) Nlow;
        }
        else
        {
            double l = 0; slong n;
            for (n = 1; ; n++) { l += log2(yd) - log2((double) n); if (n > yd && l < -(wpu + 2.9 * yd + 64)) break; }
            nlow = n; Nlow = n;
        }
        /* continued fraction when it is clearly shorter than the lower series */
        if (Nlow < 0 || 1.5 * ncf < nlow)
        {
            slong ns = (slong) ncf;
            for (;;)
            {
                if (gamma_cf(G, half, p, q, ns, wpu)) goto done;
                if (ns > 4 * ncf) break;
                ns = ns * 3 / 2;
            }
        }
        if (half)
        {
            wpl = wpu + (slong) (yd * 1.4426950408889634) + 32;
            _arb_hypgeom_gamma_lower_fmpq_0_bsplit(G, a, y, Nlow, wpl);
            arb_add_error_mag(G, AE);
            arb_const_sqrt_pi(t, wpl);
            arb_sub(G, t, G, wpl);
        }
        else
        {
            /* E1(y) = -gamma - log y + Ein(y), cancellation of about 2.9 y bits */
            ein_ctx c; bs_t B; arb_t x0, sm;
            wpl = wpu + (slong) (2.9 * yd) + 64;
            fmpz_init_set(c.p, p); fmpz_init_set(c.q, q);
            B.d = 1; B.s = 1; B.leaf = ein_leaf; B.ctx = &c;
            arb_init(x0); arb_init(sm);
            arb_set(x0, y);
            bs_eval(NULL, sm, x0, 1, Nlow, &B, wpl);
            mag_set_ui_2exp_si(AE, 1, -(wpu + (slong) (2.9 * yd) + 60));
            arb_add_error_mag(sm, AE);
            arb_const_euler(t, wpl); arb_sub(sm, sm, t, wpl);
            arb_log(t, y, wpl); arb_sub(G, sm, t, wpl);
            arb_clear(x0); arb_clear(sm); fmpz_clear(c.p); fmpz_clear(c.q);
        }
    }
done:
    fmpq_clear(a); mag_clear(tol); mag_clear(AE); arb_clear(t); arb_clear(s); fmpz_clear(p); fmpz_clear(q);
}


/* ======================= Gamma(a, y), rational 0 < a < 1 ======================= */

/* Legendre's continued fraction y + (1-a)/(1 + 1/(y + (2-a)/(1 + 2/(y + ...)))), scaled by c_even = 2 q ad,
   c_odd = 2 ad: b_n = 2 p ad (n even), 2 ad (odd); al_n = 2 q ad ((n+1) ad - 2 an) (n odd), 2 q ad^2 n (even);
   the value is 2 q ad x and Gamma(a, y) = e^-y y^a 2 q ad / X. */
typedef struct { slong an, ad; fmpz_t p, q; } cfa_ctx;

static void cfa_leaf(fmpz_mat_t T, fmpz_t qq, slong n, const void * vctx)
{
    const cfa_ctx * c = vctx;
    if (n % 2 == 0) fmpz_mul_ui(fmpz_mat_entry(T, 0, 0), c->p, 2 * c->ad);
    else fmpz_set_ui(fmpz_mat_entry(T, 0, 0), 2 * c->ad);
    if (n % 2 == 1)
    {
        fmpz_mul_ui(fmpz_mat_entry(T, 0, 1), c->q, 2 * c->ad);
        fmpz_mul_si(fmpz_mat_entry(T, 0, 1), fmpz_mat_entry(T, 0, 1), (n + 1) * c->ad - 2 * c->an);
    }
    else
    {
        fmpz_mul_ui(fmpz_mat_entry(T, 0, 1), c->q, 2 * c->ad * c->ad);
        fmpz_mul_ui(fmpz_mat_entry(T, 0, 1), fmpz_mat_entry(T, 0, 1), n);
    }
    fmpz_one(fmpz_mat_entry(T, 1, 0));
    fmpz_one(qq);
}

static int gamma_cfa(arb_t G, const fmpq_t a, const fmpz_t p, const fmpz_t q, slong nsteps, slong W)
{
    cfa_ctx c; arb_mat_t T; arb_t Q, b0, xa, xb, y, t;
    slong prec = W + 64, lim;
    int ok;
    bs_t B;
    c.an = fmpz_get_si(fmpq_numref(a)); c.ad = fmpz_get_si(fmpq_denref(a));
    fmpz_init_set(c.p, p); fmpz_init_set(c.q, q);
    B.d = 2; B.s = 0; B.leaf = cfa_leaf; B.ctx = &c;
    arb_mat_init(T, 2, 2); arb_init(Q); arb_init(b0); arb_init(xa); arb_init(xb); arb_init(y); arb_init(t);
    lim = FLINT_MAX(2, 2 * prec / (2 * (fmpz_bits(p) + fmpz_bits(q) + FLINT_BIT_COUNT(nsteps) + 8) + 4));
    bs_top(T, Q, 1, nsteps + 1, &B, lim, prec);
    arb_set_fmpz(b0, p); arb_mul_ui(b0, b0, 2 * c.ad, prec);
    arb_mul(xa, b0, arb_mat_entry(T, 0, 0), prec); arb_add(xa, xa, arb_mat_entry(T, 0, 1), prec);
    arb_div(xa, xa, arb_mat_entry(T, 0, 0), prec);
    arb_mul(xb, b0, arb_mat_entry(T, 1, 0), prec); arb_add(xb, xb, arb_mat_entry(T, 1, 1), prec);
    arb_div(xb, xb, arb_mat_entry(T, 1, 0), prec);
    arb_union(xa, xa, xb, prec);
    arb_set_fmpz(y, p); arb_div_fmpz(y, y, q, prec);
    arb_set_fmpz(t, q); arb_mul_ui(t, t, 2 * c.ad, prec);
    arb_div(t, t, xa, prec);
    arb_pow_fmpq(b0, y, a, prec); arb_mul(t, t, b0, prec);
    arb_neg(y, y); arb_exp(y, y, prec); arb_mul(G, t, y, prec);
    ok = arb_rel_accuracy_bits(G) >= W;
    arb_mat_clear(T); arb_clear(Q); arb_clear(b0); arb_clear(xa); arb_clear(xb); arb_clear(y); arb_clear(t);
    fmpz_clear(c.p); fmpz_clear(c.q);
    return ok;
}

void gamma_upper_fmpq_exact(arb_t G, const fmpq_t a, const arb_t y, const arb_t gamma_a, slong wp)
{
    mag_t tol, AE; arb_t t;
    slong NN, wpu = wp + 20, wpl, Nlow;
    double yd = arf_get_d(arb_midref(y), ARF_RND_NEAR), ad = fmpq_get_d(a);
    fmpz_t p, q;
    mag_init(tol); mag_init(AE); arb_init(t); fmpz_init(p); fmpz_init(q);
    exact_pq(p, q, y);
    /* tolerance 2^-wpu e^-y y^(a-1) */
    arb_neg(t, y); arb_exp(t, t, 64);
    { arb_t s; arb_init(s); fmpq_t a1; fmpq_init(a1); fmpq_sub_ui(a1, a, 1); arb_pow_fmpq(s, y, a1, 64); arb_mul(t, t, s, 64); arb_clear(s); fmpq_clear(a1); }
    arb_get_mag_lower(tol, t);
    mag_mul_2exp_si(tol, tol, -wpu);
    NN = _arb_hypgeom_gamma_upper_fmpq_inf_choose_N(AE, a, y, tol);
    if (NN != -1)
    {
        _arb_hypgeom_gamma_upper_fmpq_inf_bsplit(G, a, y, NN, wpu);
        arb_add_error_mag(G, AE);
        goto done;
    }
    Nlow = _arb_hypgeom_gamma_lower_fmpq_0_choose_N(AE, a, y, tol);
    {
        double ncf = pow(wpu / 2.4, 2) / yd + 1000;
        if (Nlow < 0 || 1.5 * ncf < (double) Nlow)
        {
            slong ns = (slong) ncf;
            for (;;)
            {
                if (gamma_cfa(G, a, p, q, ns, wpu)) goto done;
                if (ns > 4 * ncf) break;
                ns = ns * 3 / 2;
            }
        }
    }
    (void) ad;
    wpl = wpu + (slong) (yd * 1.4426950408889634) + 32;
    _arb_hypgeom_gamma_lower_fmpq_0_bsplit(G, a, y, Nlow, wpl);
    arb_add_error_mag(G, AE);
    if (gamma_a != NULL && arb_rel_accuracy_bits(gamma_a) >= wpl) arb_set(t, gamma_a); else arb_gamma_fmpq(t, a, wpl);
    arb_sub(G, t, G, wpl);
done:
    mag_clear(tol); mag_clear(AE); arb_clear(t); fmpz_clear(p); fmpz_clear(q);
}

/* ======================= bit-burst for a moment system ======================= */

/* Taylor terms T_l = (-delta/c0)^l/l! V_l obey T_{l+1} = r_l (A(l) T_l + kappa Phi_l),
   Phi_{l+1} = -delta/(u0 (l+1)) Phi_l, r_l = -delta/(c0 (l+1)); delta = dn/dd, c0 = C/D */
typedef struct { const moment_sys_t * S; fmpz_t C, D, dn, dd; } tl_ctx;

static void taylor_leaf(fmpz_mat_t T, fmpz_t q, slong l, const void * vctx)
{
    const tl_ctx * c = vctx;
    const moment_sys_t * S = c->S;
    slong d = S->d, ng = S->ng, i, j;
    fmpz * A = _fmpz_vec_init(d * d);
    fmpz_t f, g;
    fmpz_init(f); fmpz_init(g);
    S->amat(A, l, c->C, c->D);
    fmpz_mul(q, c->dd, c->C); fmpz_mul_ui(q, q, 2 * (ulong) (l + 1)); fmpz_mul(q, q, U0_NUM);
    fmpz_mul(f, c->dn, U0_NUM); fmpz_neg(f, f);
    for (i = 0; i < d; i++)
    {
        for (j = 0; j < d; j++)
            if (!fmpz_is_zero(A + i * d + j))
                fmpz_mul(fmpz_mat_entry(T, i, j), A + i * d + j, f);
        if (S->fsel[i] >= 0)
        {
            fmpz_mul(g, c->D, f); fmpz_mul_2exp(g, g, 1);
            fmpz_set(fmpz_mat_entry(T, i, d + S->fsel[i]), g);
        }
    }
    fmpz_mul(g, c->C, c->dn); fmpz_mul(g, g, U0_DEN); fmpz_mul_2exp(g, g, 1); fmpz_neg(g, g);
    for (i = 0; i < ng; i++)
        fmpz_set(fmpz_mat_entry(T, d + i, d + i), g);
    for (i = 0; i < d; i++)
        fmpz_set(fmpz_mat_entry(T, d + ng + i, i), q);
    _fmpz_vec_clear(A, d * d);
    fmpz_clear(f); fmpz_clear(g);
}

void taylor_step(arb_ptr V, arb_t E, const moment_sys_t * S, const fmpz_t C, slong e, const fmpz_t C1, slong B, slong wp)
{
    tl_ctx c; bs_t Bs;
    slong d = S->d, ng = S->ng, i, L, prec = wp + 64;
    arb_ptr X0 = _arb_vec_init(d + ng), Acc = _arb_vec_init(d);
    arb_t F, r, t;
    double lc, ldel, lsum;
    arb_init(F); arb_init(r); arb_init(t);
    c.S = S;
    fmpz_init_set(c.C, C); fmpz_init(c.D); fmpz_one(c.D); fmpz_mul_2exp(c.D, c.D, e);
    fmpz_init(c.dn); fmpz_mul_2exp(c.dn, C, B - e); fmpz_sub(c.dn, C1, c.dn);
    fmpz_init(c.dd); fmpz_one(c.dd); fmpz_mul_2exp(c.dd, c.dd, B);
    /* number of terms: |T_l/T_0| ~ prod_j |delta| max(1/u0, (j + t0 + 1)/c0)/(j+1) */
    lc = fmpz_dlog(C) / log(2) - e;
    ldel = (double) fmpz_bits(c.dn) - B;
    lsum = 0;
    for (L = 1; ; L++)
    {
        lsum += ldel + log2(FLINT_MAX(1.0 / U0_D, (L + S->t0 + 1) / pow(2.0, lc))) - log2((double) L) + 1;
        if (L >= 2 && lsum < -(wp + 64)) break;
    }
    L++;
    Bs.d = d + ng; Bs.s = d; Bs.leaf = taylor_leaf; Bs.ctx = &c;
    _arb_vec_set(X0, V, d);
    arb_mul(F, E, S->f0scale, prec);
    for (i = 0; i < ng; i++) arb_mul(X0 + d + i, F, S->kappa + i, prec);
    bs_eval(NULL, Acc, X0, 0, L, &Bs, prec);
    /* lagged components: V_0(c1) = Acc (c0/c1) */
    arb_set_fmpz(r, C); arb_mul_2exp_si(r, r, B - e); arb_div_fmpz(r, r, C1, prec);
    for (i = 0; i < d; i++)
        if (S->lag[i] == -1) arb_mul(V + i, Acc + i, r, prec); else arb_set(V + i, Acc + i);
    arb_set_fmpz(t, c.dn); arb_mul_2exp_si(t, t, -B); arb_div(t, t, U0, prec);
    arb_neg(t, t); arb_exp(t, t, prec); arb_mul(E, E, t, prec);
    _arb_vec_clear(X0, d + ng); _arb_vec_clear(Acc, d);
    arb_clear(F); arb_clear(r); arb_clear(t);
    fmpz_clear(c.C); fmpz_clear(c.D); fmpz_clear(c.dn); fmpz_clear(c.dd);
}

void dual_state(arb_ptr V, const moment_sys_t * S, const arb_t c, slong wp)
{
    arb_t E; fmpz_t C, C1; slong e = 64, B, Bfin = wp + 128;
    arb_init(E); fmpz_init(C); fmpz_init(C1);
    arf_get_fmpz_fixed_si(C, arb_midref(c), -e);
    S->init(V, E, C, e, wp, S);
    for (;;)
    {
        int last;
        B = 4 * e;
        last = (B >= Bfin);
        if (last) B = FLINT_MAX(Bfin, e + 1);
        arf_get_fmpz_fixed_si(C1, arb_midref(c), -B);
        taylor_step(V, E, S, C, e, C1, B, wp);
        fmpz_swap(C, C1);
        e = B;
        if (last) break;
    }
    arb_clear(E); fmpz_clear(C); fmpz_clear(C1);
}

void moment_sys_clear(moment_sys_t * S)
{
    _arb_vec_clear(S->kappa, S->ng);
    arb_clear(S->f0scale);
}

slong dual_init_common(arb_t c, arb_t E, arb_t base, int half, const fmpz_t C, slong e, slong wp, double guard)
{
    arb_t y; double cd; slong W;
    arb_init(y);
    arb_set_fmpz(c, C); arb_mul_2exp_si(c, c, -e);
    cd = arf_get_d(arb_midref(c), ARF_RND_NEAR);
    W = wp + (slong) (1.4426950408889634 * cd / U0_D + guard) + 64;
    arb_mul_fmpz(y, c, U0_DEN, ARF_PREC_EXACT); arb_div_fmpz(y, y, U0_NUM, W);
    arb_neg(E, y); arb_exp(E, E, wp + 64);
    gamma_upper_exact(base, half, y, wp + 64);
    if (half) { arb_rsqrt(y, c, wp + 64); arb_mul(base, base, y, wp + 64); }
    arb_clear(y);
    return W;
}

slong dual_term_prec(slong m, slong prec)
{
    double cd = 9.8696044010893586 * (double) m * m;
    return prec - (slong) (1.4426950408889634 * cd / U0_D) + 64;
}

slong dual_term_count(slong prec)
{
    return (slong) (sqrt((prec + 64) * 0.69314718 * U0_D) / 3.14159265) + 2;
}

slong k_term_count(slong prec)
{
    return (slong) sqrt((prec + 64) * 0.69314718 / U0_D + 2) + 2;
}

/* ======================= thread pool ======================= */

typedef struct
{
    pthread_mutex_t mtx;
    slong next, n, prec;
    term_fn term;
    void * ctx;
    arb_t acc;
} pool_t;

static void * pool_worker(void * arg)
{
    pool_t * P = arg;
    arb_t r;
    arb_init(r);
    for (;;)
    {
        slong idx;
        pthread_mutex_lock(&P->mtx); idx = P->next++; pthread_mutex_unlock(&P->mtx);
        if (idx >= P->n) break;
        arb_zero(r);
        P->term(r, idx, P->prec, P->ctx);
        pthread_mutex_lock(&P->mtx); arb_add(P->acc, P->acc, r, P->prec + 64); pthread_mutex_unlock(&P->mtx);
    }
    arb_clear(r);
    flint_cleanup();
    return NULL;
}

void parallel_sum(arb_t res, slong n, term_fn term, void * ctx, slong prec, int nthreads, phase_time_t * t)
{
    pool_t P;
    pthread_t * th;
    double c0 = cpu_seconds(), w0 = wall_seconds();
    int i;
    if (nthreads < 1) nthreads = 1;
    pthread_mutex_init(&P.mtx, NULL);
    P.next = 0; P.n = n; P.prec = prec; P.term = term; P.ctx = ctx;
    arb_init(P.acc);
    th = flint_malloc(sizeof(pthread_t) * nthreads);
    for (i = 0; i < nthreads; i++) pthread_create(&th[i], NULL, pool_worker, &P);
    for (i = 0; i < nthreads; i++) pthread_join(th[i], NULL);
    flint_free(th);
    arb_swap(res, P.acc);
    arb_clear(P.acc);
    pthread_mutex_destroy(&P.mtx);
    if (t) { t->cpu = cpu_seconds() - c0; t->wall = wall_seconds() - w0; }
}

/* ======================= utilities ======================= */

double cpu_seconds(void)
{
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_utime.tv_sec + ru.ru_stime.tv_sec + 1e-6 * (ru.ru_utime.tv_usec + ru.ru_stime.tv_usec);
}

double wall_seconds(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

long peak_rss_kb(void)
{
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_maxrss;
}

double arb_log2_abs_approx(const arb_t x)
{
    if (arf_is_zero(arb_midref(x))) return -1e300;
    return fmpz_get_d(ARF_EXPREF(arb_midref(x)));
}
