/* Interface implemented by each constant. */
#ifndef HOLSUM_CONSTANTS_H
#define HOLSUM_CONSTANTS_H

#include "engine.h"

typedef struct
{
    const char * name;        /* command-line name */
    const char * title;       /* one-line description */
    /* theta splitting: the value is finish(main + sum dual terms + sum k-terms) */
    void (*setup)(slong prec);                /* main term, dual systems; called once */
    void (*clear)(void);
    term_fn dual_term;                        /* idx = m - 1 */
    term_fn k_term;                           /* idx = k - k_first */
    slong k_first;
    void (*finish)(arb_t res, const arb_t lin, slong prec);   /* lin = main + dual + k */
    void (*main_term)(arb_t res);             /* after setup */
    /* reference methods (absolute accuracy about 2^-prec), or NULL */
    void (*ref_zeta)(arb_t res, slong prec, int threads);
    void (*ref_em)(arb_t res, slong prec, int threads);
    slong u0_exp;                             /* default split point u0 = 4^-u0_exp */
}
constant_t;

extern const constant_t CONST_A340440, CONST_A085361, CONST_KMINUS1, CONST_VORTEX, CONST_HL;

/* helpers shared by the reference methods (refs.c) */
typedef void (*block_fn)(slong block, void * ctx);
void parallel_for(slong nblocks, block_fn fn, void * ctx, int nthreads);
/* Euler-Maclaurin tail: sum_{j=1}^{J} B_{2j}/(2j) * c[2j-1], c = Taylor coefficients of F at M, len >= 2J */
void em_bernoulli_sum(arb_t res, arb_srcptr c, slong len, slong prec);
/* the same with c_0, c_1, ... generated on demand (bounded memory); also returns c0 = c_0 */
typedef struct { void (*restart)(void * st); void (*next)(arb_t c, void * st); void * st; } jet_stream_t;
void em_bernoulli_stream(arb_t res, arb_t c0, const jet_stream_t * J, slong len, slong prec);
/* Taylor coefficients at x = M of the solution of p2 F'' + p1 F' + p0 F = 0 (integer polynomials in x,
   degree < ODE_JET_WIN - 3, p2(M) != 0) with F(M) = f0, F'(M) = f1; use with ode_jet_restart/next */
#define ODE_JET_WIN 8
typedef struct { fmpz_poly_struct p[3][1]; arb_t f0, f1, t, u; arb_struct w[ODE_JET_WIN]; slong n, prec; } ode_jet_t;
void ode_jet_init(ode_jet_t * J, const fmpz_poly_t p2, const fmpz_poly_t p1, const fmpz_poly_t p0, ulong M,
                  const arb_t f0, const arb_t f1, slong prec);
void ode_jet_clear(ode_jet_t * J);
void ode_jet_restart(void * st);
void ode_jet_next(arb_t c, void * st);
/* number of Euler-Maclaurin corrections 2J for cutoff M and absolute accuracy 2^-prec (F^(m)(M) ~ m!/M^m) */
slong em_length(double M, slong prec);
/* coefficients of log(M + a + t) and 1/(M + a + t) as power series in t */
void series_log_shift(arb_ptr c, ulong Ma, slong len, slong prec);
void series_inv_shift(arb_ptr c, ulong Ma, slong len, slong prec);
/* EM cutoff used by the references: M = max(16, prec/4) unless overridden by HOLSUM_EM_M */
ulong em_cutoff(slong prec);
/* zeta(start + i step) for 0 <= i < num (step 1 or 2), choosing the fastest FLINT algorithm per value */
void zeta_vec_mixed(arb_ptr z, ulong start, ulong step, slong num, slong prec);

#endif
