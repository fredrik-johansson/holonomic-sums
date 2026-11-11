/* Continued fraction of x from a decimal file "I.ddddd": x in [lo, hi] = [d, d + 1]/10^D, D = number of
   fraction digits used. Prints the number of partial quotients shared by lo and hi (hence by x), writes them
   to a file, and the size of the last shared convergent. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <flint/fmpz.h>
#include <flint/fmpq.h>
#include <flint/fmpz_vec.h>
int main(int argc, char ** argv)
{
    const char * in = argv[1]; slong D = atol(argv[2]); const char * out = argv[3];
    FILE * f = fopen(in, "r"); char * buf = malloc(D + 64); size_t len;
    fmpz_t d, p10; fmpq_t lo, hi, rlo, rhi, cv; fmpz * clo, * chi; slong nlo, nhi, n, m, i;
    clock_t t0 = clock();
    len = fread(buf, 1, D + 63, f); buf[len] = 0; fclose(f);
    char * dot = strchr(buf, '.');
    /* integer part followed by D fraction digits */
    memmove(dot, dot + 1, D); dot[D] = 0;
    fmpz_init(d); fmpz_init(p10);
    fmpz_set_str(d, buf, 10);
    fmpz_ui_pow_ui(p10, 10, D);
    fmpq_init(lo); fmpq_init(hi); fmpq_init(rlo); fmpq_init(rhi); fmpq_init(cv);
    fmpq_set_fmpz_frac(lo, d, p10);
    fmpz_add_ui(d, d, 1); fmpq_set_fmpz_frac(hi, d, p10);
    fprintf(stderr, "parsed: %.1f s\n", (double) (clock() - t0) / CLOCKS_PER_SEC);
    n = FLINT_MAX(fmpq_cfrac_bound(lo), fmpq_cfrac_bound(hi));
    clo = _fmpz_vec_init(n); chi = _fmpz_vec_init(n);
    nlo = fmpq_get_cfrac(clo, rlo, lo, n);
    fprintf(stderr, "cfrac lo: %ld terms, %.1f s\n", nlo, (double) (clock() - t0) / CLOCKS_PER_SEC);
    nhi = fmpq_get_cfrac(chi, rhi, hi, n);
    fprintf(stderr, "cfrac hi: %ld terms, %.1f s\n", nhi, (double) (clock() - t0) / CLOCKS_PER_SEC);
    if (!fmpq_is_zero(rlo) || !fmpq_is_zero(rhi)) { fprintf(stderr, "increase n\n"); return 1; }
    for (m = 0; m < nlo && m < nhi && fmpz_equal(clo + m, chi + m); m++) ;
    /* clo[0..m-1] shared; both expansions continue beyond index m-1 */
    printf("shared terms a_0..a_%ld (%ld terms); lo has %ld, hi has %ld; next terms lo %s, hi %s\n",
        m - 1, m, nlo, nhi, fmpz_get_str(NULL, 10, clo + m), fmpz_get_str(NULL, 10, chi + m));
    f = fopen(out, "w");
    for (i = 0; i < m; i++) { fmpz_fprint(f, clo + i); fputc('\n', f); }
    fclose(f);
    /* last shared convergent p_{m-1}/q_{m-1} and the previous one */
    fmpq_set_cfrac(cv, clo, m);
    printf("q_%ld has %ld digits, p has %ld digits\n", m - 1, (slong) fmpz_sizeinbase(fmpq_denref(cv), 10), (slong) fmpz_sizeinbase(fmpq_numref(cv), 10));
    {
        char * s = fmpz_get_str(NULL, 10, fmpq_denref(cv));
        printf("q_%ld = %.30s...%s (log10 = %ld + log10(%.12s))\n", m - 1, s, s + strlen(s) - 20, (slong) strlen(s) - 1, s);
    }
    fmpq_set_cfrac(rlo, clo, m - 1);
    {
        char * s = fmpz_get_str(NULL, 10, fmpq_denref(rlo));
        printf("q_%ld = %.30s... (%ld digits)\n", m - 2, s, (slong) strlen(s));
    }
    /* check: lo < hi lie strictly between p/q and the mediant-type endpoint; print sign checks */
    {
        fmpq_t t; fmpq_init(t);
        fmpq_sub(t, lo, cv); printf("sign(lo - p/q) = %d, sign(hi - p/q) = %d\n", fmpq_sgn(t), (fmpq_sub(t, hi, cv), fmpq_sgn(t)));
    }
    fprintf(stderr, "done: %.1f s\n", (double) (clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
