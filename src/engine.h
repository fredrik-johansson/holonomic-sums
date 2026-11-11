/*
    Theta-splitting evaluation of sums of holonomic functions: shared engine.

    A sum S = sum_k f(1/k) with f(1/k) = int_0^oo e^{-k^2 u} h(u) du is split at u = u0 into
      - k-side terms   I_k = int_{u0}^oo e^{-k^2 u} h(u) du   (rational series, binary splitting),
      - dual terms     J_m = int_0^{u0} u^{-t} e^{-c/u} h(u) du,  c = pi^2 m^2  (holonomic in c, bit-burst),
      - a main term (power series at u0).
    This file provides the pieces common to all constants: binary splitting of linear recurrences,
    Gamma(1/2, y) and E1(y) at exact dyadic y, the bit-burst evaluation of a moment system in c,
    a thread pool, and timing/memory utilities.

    Demonstration code: ball arithmetic is used throughout, but series lengths are chosen by
    heuristic estimates, not proved bounds. Validate results by cross-checks (see README).
*/
#ifndef HOLSUM_ENGINE_H
#define HOLSUM_ENGINE_H

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>
#include <flint/fmpz_mat.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpq.h>
#include <flint/arb.h>
#include <flint/arb_mat.h>
#include <flint/arb_hypgeom.h>
#include <flint/arb_poly.h>
#include <pthread.h>

/* ---------------- split point u0 = un/ud = 4^-a ---------------- */
extern fmpz_t U0_NUM, U0_DEN;
extern arb_t U0, SQRT_U0;
extern double U0_D;
void engine_set_u0(slong a, slong prec);     /* u0 = 4^-a */
void engine_clear(void);

/* ---------------- binary splitting ----------------
   X_{n+1} = (M_n / q_n) X_n,  sums += (S_n / q_n) X_n   for a <= n < b.
   The leaf writes T = [M_n; S_n] ((d+s) x d, pre-zeroed) and q_n. */
typedef void (*bs_leaf_fn)(fmpz_mat_t T, fmpz_t q, slong n, const void * ctx);
typedef struct { slong d, s; bs_leaf_fn leaf; const void * ctx; } bs_t;
/* xend = M x0 / Q (may be NULL), sums = S x0 / Q (may be NULL) */
void bs_eval(arb_ptr xend, arb_ptr sums, arb_srcptr x0, slong a, slong b, const bs_t * B, slong prec);

/* ---------------- incomplete gamma at exact dyadic y > 0 ----------------
   G = Gamma(1/2, y) (half = 1) or E1(y) = Gamma(0, y) (half = 0), relative accuracy about wp */
void gamma_upper_exact(arb_t G, int half, const arb_t y, slong wp);

/* ---------------- bit-burst for a moment system ----------------
   State V_j (d components, component i = c^(j + o_i) Z^(i)_{t0 + j + s_i}) with
   V_{j+1} = A(j) V_j + F_j kappa, F_{j+1} = (c/u0) F_j, F_0 = E u0^(1 - t0), E = exp(-c/u0).
   amat writes 2 D A(l) as an integer matrix (c0 = C/D). Each state row gets at most one
   forcing constant (fsel[i], coefficient 1). init computes V and E at c0 = C/2^e. */
#define SYS_MAXD 8
typedef struct
{
    int d, ng;
    int fsel[SYS_MAXD];
    int lag[SYS_MAXD];        /* o_i in {0, -1} */
    void (*amat)(fmpz * A, slong l, const fmpz_t C, const fmpz_t D);
    void (*init)(arb_ptr V, arb_t E, const fmpz_t C, slong e, slong wp, const void * sys);
    arb_ptr kappa;            /* ng forcing constants */
    arb_t f0scale;            /* u0^(1 - t0) */
    double t0;
}
moment_sys_t;

void moment_sys_clear(moment_sys_t * S);
/* one Taylor stage c0 = C/2^e -> c1 = C1/2^B */
void taylor_step(arb_ptr V, arb_t E, const moment_sys_t * S, const fmpz_t C, slong e, const fmpz_t C1, slong B, slong wp);
/* V = state at c (relative precision about wp), from a 64-bit starting point and growth factor 4 */
void dual_state(arb_ptr V, const moment_sys_t * S, const arb_t c, slong wp);
/* c0 = C/2^e as a ball, E = exp(-c0/u0), base = c0^{-1/2} Gamma(1/2, c0/u0) (half) or E1(c0/u0);
   returns the working precision W = wp + 1.44 c0/u0 + guard */
slong dual_init_common(arb_t c, arb_t E, arb_t base, int half, const fmpz_t C, slong e, slong wp, double guard);

/* dual-term working precision for c = pi^2 m^2 (absolute 2^-prec), or < 64 if negligible */
slong dual_term_prec(slong m, slong prec);
/* number of dual and k-side terms for absolute precision 2^-prec */
slong dual_term_count(slong prec);
slong k_term_count(slong prec);

/* ---------------- parallel sums ---------------- */
typedef void (*term_fn)(arb_t res, slong idx, slong prec, void * ctx);
typedef struct { double cpu, wall; } phase_time_t;
/* res = sum_{0 <= i < n} term(i), computed by nthreads threads (dynamic scheduling, index order) */
void parallel_sum(arb_t res, slong n, term_fn term, void * ctx, slong prec, int nthreads, phase_time_t * t);

/* ---------------- utilities ---------------- */
double cpu_seconds(void);      /* process CPU time (all threads) */
double wall_seconds(void);
long peak_rss_kb(void);
/* log2 of x (double) for an arb */
double arb_log2_abs_approx(const arb_t x);

#endif
