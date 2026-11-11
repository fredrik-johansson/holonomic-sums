/* x_t = [a_0; ..., a_m, t]: check lo < x_10 < hi (in the right order) and print its denominator */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>
#include <flint/fmpq.h>
int main(int argc, char ** argv)
{
    slong D = atol(argv[2]), m = 0, i; FILE * f = fopen(argv[1], "r"); char * buf = malloc(D + 64); size_t len;
    fmpz_t d, p10; fmpq_t lo, hi, x; fmpz * c;
    len = fread(buf, 1, D + 63, f); buf[len] = 0; fclose(f);
    char * dot = strchr(buf, '.'); memmove(dot, dot + 1, D); dot[D] = 0;
    fmpz_init(d); fmpz_init(p10); fmpz_set_str(d, buf, 10); fmpz_ui_pow_ui(p10, 10, D);
    fmpq_init(lo); fmpq_init(hi); fmpq_init(x);
    fmpq_set_fmpz_frac(lo, d, p10); fmpz_add_ui(d, d, 1); fmpq_set_fmpz_frac(hi, d, p10);
    c = _fmpz_vec_init(10000000);
    f = fopen(argv[3], "r"); while (fmpz_fread(f, c + m) > 0) m++; fclose(f);
    for (i = 9; i <= 27; i++)
    {
        if (i > 11 && i < 25) continue;
        fmpz_set_ui(c + m, i); fmpq_set_cfrac(x, c, m + 1);
        printf("t = %ld: lo < x_t: %d, x_t < hi: %d", i, fmpq_cmp(lo, x) < 0, fmpq_cmp(x, hi) < 0);
        if (i == 10) { char * s = fmpz_get_str(NULL, 10, fmpq_denref(x)); printf(", denominator %.20s... (%ld digits)", s, (long) strlen(s)); }
        printf("\n");
    }
    return 0;
}
