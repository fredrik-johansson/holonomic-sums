/* Helpers for the reference methods (zeta-value expansions and Euler-Maclaurin summation). */
#include <math.h>
#include <stdlib.h>
#include <pthread.h>
#include <flint/bernoulli.h>
#include "constants.h"

typedef struct
{
    pthread_mutex_t mtx;
    slong next, n;
    block_fn fn;
    void * ctx;
} pfor_t;

static void * pfor_worker(void * arg)
{
    pfor_t * P = arg;
    for (;;)
    {
        slong b;
        pthread_mutex_lock(&P->mtx); b = P->next++; pthread_mutex_unlock(&P->mtx);
        if (b >= P->n) break;
        P->fn(b, P->ctx);
    }
    flint_cleanup();
    return NULL;
}

void parallel_for(slong nblocks, block_fn fn, void * ctx, int nthreads)
{
    pfor_t P;
    pthread_t * th;
    int i;
    if (nthreads < 1) nthreads = 1;
    pthread_mutex_init(&P.mtx, NULL);
    P.next = 0; P.n = nblocks; P.fn = fn; P.ctx = ctx;
    th = flint_malloc(sizeof(pthread_t) * nthreads);
    for (i = 0; i < nthreads; i++) pthread_create(&th[i], NULL, pfor_worker, &P);
    for (i = 0; i < nthreads; i++) pthread_join(th[i], NULL);
    flint_free(th);
    pthread_mutex_destroy(&P.mtx);
}

ulong em_cutoff(slong prec)
{
    const char * s = getenv("HOLSUM_EM_M");
    if (s != NULL) return strtoul(s, NULL, 10);
    return FLINT_MAX(16, prec / 4);
}

/* smallest even 2J with (2J)! / (2 pi M)^(2J) * M below 2^-(prec + 20) */
slong em_length(double M, slong prec)
{
    slong n;
    for (n = 2; ; n += 2)
    {
        double l = lgamma(n + 1.0) / log(2.0) - n * log2(2 * 3.141592653589793 * M) + log2(M);
        if (l < -prec - 20) return n;
        if (n > 4 * M * 3.15) { flint_printf("em_length: cutoff M too small\n"); flint_abort(); }
    }
}

void em_bernoulli_sum(arb_t res, arb_srcptr c, slong len, slong prec)
{
    bernoulli_rev_t iter;
    fmpz_t num, den;
    arb_t t;
    slong n = len - (len % 2);       /* largest even index with c[n - 1] available */
    fmpz_init(num); fmpz_init(den); arb_init(t);
    arb_zero(res);
    if (n >= 2)
    {
        bernoulli_rev_init(iter, n);
        for ( ; n >= 2; n -= 2)
        {
            bernoulli_rev_next(num, den, iter);       /* B_n */
            arb_set_fmpz(t, num);
            arb_div_fmpz(t, t, den, prec);
            arb_div_ui(t, t, n, prec);
            arb_addmul(res, t, c + n - 1, prec);
        }
        bernoulli_rev_clear(iter);
    }
    fmpz_clear(num); fmpz_clear(den); arb_clear(t);
}

/* log(Ma + t) = log(Ma) + sum_{i>=1} (-1)^(i-1) t^i / (i Ma^i) */
void series_log_shift(arb_ptr c, ulong Ma, slong len, slong prec)
{
    arb_t p, ip;
    slong i;
    arb_init(p); arb_init(ip);
    arb_log_ui(c + 0, Ma, prec);
    arb_one(p);
    arb_set_ui(ip, Ma); arb_inv(ip, ip, prec);
    for (i = 1; i < len; i++)
    {
        arb_mul(p, p, ip, prec);
        arb_div_si(c + i, p, (i % 2) ? i : -i, prec);
    }
    arb_clear(p); arb_clear(ip);
}

/* 1/(Ma + t) = sum_i (-1)^i t^i / Ma^(i+1) */
void series_inv_shift(arb_ptr c, ulong Ma, slong len, slong prec)
{
    arb_t ip;
    slong i;
    arb_init(ip);
    arb_set_ui(ip, Ma); arb_inv(ip, ip, prec);
    if (len > 0) arb_set(c + 0, ip);
    for (i = 1; i < len; i++)
    {
        arb_mul(c + i, c + i - 1, ip, prec);
        arb_neg(c + i, c + i);
    }
    arb_clear(ip);
}

/* zeta(start + i step), 0 <= i < num, step 1 or 2, start >= 2.
   FLINT's vector functions use the Borwein algorithm for all odd arguments below 0.3 prec; that is
   much slower than the Euler product once the argument exceeds about prec/16. Here the odd arguments
   below ZETA_BORWEIN_CUTOFF use one Borwein vector per call, all other values arb_zeta_ui
   (Bernoulli numbers for even arguments, the Euler product for large odd arguments). */
void zeta_vec_mixed(arb_ptr z, ulong start, ulong step, slong num, slong prec)
{
    ulong cutoff = 40 + prec / 16, n, first = 0, last = 0;
    slong i, nb = 0;
    for (i = 0; i < num; i++)
    {
        n = start + i * step;
        if (n % 2 == 1 && n >= 3 && n < cutoff)
        {
            if (nb == 0) first = n;
            last = n; nb++;
        }
        else
            arb_zeta_ui(z + i, n, prec);
    }
    if (nb > 0)
    {
        arb_ptr v = _arb_vec_init(nb);
        arb_zeta_ui_vec_borwein(v, first, nb, 2, prec);
        for (n = first; n <= last; n += 2)
            arb_swap(z + (n - start) / step, v + (n - first) / 2);
        _arb_vec_clear(v, nb);
    }
}

/* ---------------- Euler-Maclaurin corrections from a stream of Taylor coefficients ----------------
   The coefficients are generated in increasing order, the Bernoulli numbers (bernoulli_rev) in decreasing
   order. To keep memory bounded, the index range is cut into segments, processed from the top; for each
   segment the jet is regenerated from the start (cheap compared with the rest) and only the odd-indexed
   coefficients of that segment are kept. */
#ifndef EM_SEGMENT_BYTES
#define EM_SEGMENT_BYTES (256L << 20)
#endif

void em_bernoulli_stream(arb_t res, arb_t c0, const jet_stream_t * J, slong len, slong prec)
{
    slong nmax = len - (len % 2), seg, hi, lo, n, i;
    arb_ptr buf;
    arb_t c, t;
    fmpz_t num, den;
    int have_c0 = 0;
    arb_init(c); arb_init(t); fmpz_init(num); fmpz_init(den);
    arb_zero(res);
    seg = FLINT_MAX(64, EM_SEGMENT_BYTES / (prec / 8 + 64));       /* odd coefficients per segment */
    buf = _arb_vec_init(FLINT_MIN(seg, nmax / 2 + 1));
    for (hi = nmax; ; hi = lo)
    {
        bernoulli_rev_t iter;
        lo = FLINT_MAX(0, hi - 2 * seg);
        /* coefficients c_0 .. c_{hi-1}; keep c_{lo+1}, c_{lo+3}, ..., c_{hi-1} */
        J->restart(J->st);
        for (i = 0; i < hi || (i == 0 && !have_c0); i++)
        {
            J->next(c, J->st);
            if (i == 0 && !have_c0) { arb_set(c0, c); have_c0 = 1; }
            if (i > lo && (i % 2 == 1)) arb_swap(buf + (i - lo - 1) / 2, c);
        }
        if (hi >= 2)
        {
            bernoulli_rev_init(iter, hi);
            for (n = hi; n > lo; n -= 2)
            {
                bernoulli_rev_next(num, den, iter);       /* B_n */
                arb_set_fmpz(t, num);
                arb_div_fmpz(t, t, den, prec);
                arb_div_ui(t, t, n, prec);
                arb_addmul(res, t, buf + (n - 1 - lo - 1) / 2, prec);
            }
            bernoulli_rev_clear(iter);
        }
        if (lo == 0) break;
    }
    _arb_vec_clear(buf, FLINT_MIN(seg, nmax / 2 + 1));
    arb_clear(c); arb_clear(t); fmpz_clear(num); fmpz_clear(den);
}

/* ---------------- Taylor coefficients of a solution of p2 F'' + p1 F' + p0 F = 0 at x = M ---------------- */
void ode_jet_init(ode_jet_t * J, const fmpz_poly_t p2, const fmpz_poly_t p1, const fmpz_poly_t p0, ulong M,
                  const arb_t f0, const arb_t f1, slong prec)
{
    fmpz_t m;
    slong i;
    fmpz_init_set_ui(m, M);
    fmpz_poly_init(J->p[0]); fmpz_poly_init(J->p[1]); fmpz_poly_init(J->p[2]);
    fmpz_poly_taylor_shift(J->p[0], p0, m);
    fmpz_poly_taylor_shift(J->p[1], p1, m);
    fmpz_poly_taylor_shift(J->p[2], p2, m);
    if (fmpz_poly_degree(J->p[2]) >= ODE_JET_WIN - 3 || fmpz_poly_degree(J->p[1]) >= ODE_JET_WIN - 3
        || fmpz_poly_degree(J->p[0]) >= ODE_JET_WIN - 3 || fmpz_is_zero(J->p[2]->coeffs))
    {
        flint_printf("ode_jet_init: unsupported equation\n"); flint_abort();
    }
    arb_init(J->f0); arb_init(J->f1); arb_set(J->f0, f0); arb_set(J->f1, f1);
    for (i = 0; i < ODE_JET_WIN; i++) arb_init(J->w + i);
    arb_init(J->t); arb_init(J->u);
    J->prec = prec;
    J->n = 0;
    fmpz_clear(m);
}

void ode_jet_clear(ode_jet_t * J)
{
    slong i;
    fmpz_poly_clear(J->p[0]); fmpz_poly_clear(J->p[1]); fmpz_poly_clear(J->p[2]);
    arb_clear(J->f0); arb_clear(J->f1); arb_clear(J->t); arb_clear(J->u);
    for (i = 0; i < ODE_JET_WIN; i++) arb_clear(J->w + i);
}

void ode_jet_restart(void * st) { ((ode_jet_t *) st)->n = 0; }

/* coefficient of t^m of the equation:
   sum_k p2[k] (j+2)(j+1) c_{j+2} + p1[k] (j+1) c_{j+1} + p0[k] c_j = 0 with j = m - k, solved for c_{m+2} */
void ode_jet_next(arb_t c, void * st)
{
    ode_jet_t * J = st;
    slong n = J->n, m = n - 2, k, i, prec = J->prec;
    arb_ptr w = J->w;
#define W(j) (w + ((j) % ODE_JET_WIN))
    if (n == 0) arb_set(W(0), J->f0);
    else if (n == 1) arb_set(W(1), J->f1);
    else
    {
        arb_zero(J->t);
        for (i = 0; i < 3; i++)          /* i = order of the derivative */
        {
            const fmpz_poly_struct * p = J->p[i];
            for (k = (i == 2) ? 1 : 0; k < p->length; k++)
            {
                slong j = m - k;         /* the term involves c_{j+i} */
                if (j < 0 || fmpz_is_zero(p->coeffs + k)) continue;
                arb_mul_fmpz(J->u, W(j + i), p->coeffs + k, prec);
                if (i == 1) arb_mul_ui(J->u, J->u, j + 1, prec);
                if (i == 2) arb_mul_ui(J->u, J->u, (ulong) (j + 2) * (j + 1), prec);
                arb_add(J->t, J->t, J->u, prec);
            }
        }
        arb_div_fmpz(J->t, J->t, J->p[2]->coeffs, prec);
        arb_div_ui(J->t, J->t, (ulong) (m + 2) * (m + 1), prec);
        arb_neg(W(n), J->t);
    }
    arb_set(c, W(n));
    J->n++;
#undef W
}
