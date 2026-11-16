/* Generic moment systems from theta-relations (see tsys.c). */
#ifndef HOLSUM_TSYS_H
#define HOLSUM_TSYS_H

#include <flint/fmpq_mat.h>
#include <flint/fmpq_vec.h>
#include "constants.h"

#define LOG2E 1.4426950408889634
#define KMAXO 96
#define KMAXR 8

typedef struct
{
    slong r;
    void (*leaf)(fmpz_mat_t M, fmpz_t q, slong n);      /* r x r, pre-zeroed */
    void (*init)(fmpq * g0);                            /* G_0 */
    void (*weight)(fmpq * w, int f, slong n);           /* length r, pre-zeroed */
}
coef_t;

typedef struct
{
    const coef_t * co;
    int part, logs;         /* logs: include al', be' */
    slong h;                /* td ab */
    slong td;               /* denominator of ab: 2 (or 0) or 4 */
    fmpz_t C, D;            /* c0 = C/D */
    slong nout;
    int of[KMAXO], od[KMAXO], ok[KMAXO];
}
kron_t;

typedef struct { int f, k, p, num; } tterm_t;
typedef struct { int f, o, s; } tcomp_t;
typedef struct
{
    int nf, den, nterms, ncomp, twot0, R2;
    const tterm_t * terms;
    const tcomp_t * comps;
    const int * islog;
    const coef_t * co;
    int tden;                     /* twot0 = tden t0; tden = 0 means 2, otherwise 2 or 4 */
    arb_ptr fu0;                  /* f(u0), computed in setup */
    slong oidx[SYS_MAXD][4];      /* Kronecker output index per component and kind (al, be, al', be') */
    kron_t K[2];                  /* the al-run and the be-run (C, D filled per call) */
}
tsys_t;

/* sums = S x0 / Q over [a, b) */
void kbs_eval(arb_ptr sums, arb_srcptr x0, slong a, slong b, const bs_t * B, slong prec);
/* G = Gamma(b, y), dG = d/db Gamma(b, y) for b = 1/2 (half) or b = 0, y = p/q > 0 */
void dgamma_upper(arb_t G, arb_t dG, int half, const fmpz_t p, const fmpz_t q, slong W);
void tsys_build(moment_sys_t * S, tsys_t * T, slong prec);
void tsys_clear(moment_sys_t * S, tsys_t * T);
slong kd_prec(double size_log2, slong prec);
slong kseries_terms(double cK, double x, slong prec);
slong fact_terms(double z, slong prec);
void pi2c(arb_t c, double mm, slong prec);

#endif
