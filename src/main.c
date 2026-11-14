/*
    holsum: compute sums of holonomic functions by theta splitting, or by a reference method.

    usage: holsum CONSTANT DIGITS [--method theta|zeta|em|direct] [--threads N] [--u0-exp A]
                  [--guard G] [--out FILE] [--part I/N --partial FILE] [--combine FILE,FILE,...]
           holsum --list

    --part I/N computes only the theta terms with index = I mod N (and the main term if I = 0) and writes their
    sum to the --partial file; --combine adds such partial sums and finishes the computation (long runs can be
    split over several processes or sessions this way).

    The value is computed to DIGITS + G decimal digits (G = 10 by default) and written to FILE with exactly
    DIGITS digits after the decimal point, truncated (rounded down). The truncation is checked against the
    error ball; if it is not certain, rounding_ok is 0 in the report.
    A one-line JSON report with timings, term counts and peak memory is printed to standard output.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "constants.h"

static const constant_t * CONSTANTS[] = { &CONST_A340440, &CONST_A085361, &CONST_KMINUS1, &CONST_VORTEX, &CONST_HL,
                                          &CONST_SOMOS, &CONST_EXPSQRT };
#define NUM_CONSTANTS (sizeof(CONSTANTS) / sizeof(CONSTANTS[0]))

static void usage(void)
{
    size_t i;
    fprintf(stderr, "usage: holsum CONSTANT DIGITS [--method theta|zeta|em|direct] [--threads N] [--u0-exp A] [--guard G] [--out FILE]\n");
    fprintf(stderr, "constants:\n");
    for (i = 0; i < NUM_CONSTANTS; i++)
        fprintf(stderr, "  %-18s %s\n", CONSTANTS[i]->name, CONSTANTS[i]->title);
}

/* theta splitting with per-term bookkeeping */
typedef struct { const constant_t * C; int dual; slong nonzero, part, nparts; pthread_mutex_t mtx; } wrap_ctx;

static void wrap_term(arb_t res, slong idx, slong prec, void * vctx)
{
    wrap_ctx * w = vctx;
    idx = w->part + idx * w->nparts;
    if (w->dual) w->C->dual_term(res, idx, prec, NULL); else w->C->k_term(res, idx, prec, NULL);
    if (getenv("HOLSUM_DEBUG") != NULL && !arb_is_zero(res))
        flint_fprintf(stderr, "%s term %wd: log2|t| ~ %.1f, log2 rad ~ %.1f\n", w->dual ? "dual" : "k", idx,
            arf_is_zero(arb_midref(res)) ? -1e9 : (double) arf_abs_bound_lt_2exp_si(arb_midref(res)),
            mag_is_zero(arb_radref(res)) ? -1e9 : (double) mag_get_d_log2_approx(arb_radref(res)));
    if (!arb_is_zero(res))
    {
        pthread_mutex_lock(&w->mtx); w->nonzero++; pthread_mutex_unlock(&w->mtx);
    }
}

/* the decimal string of x truncated to D digits after the point (x >= 0); NULL if not certain */
static char * truncated_decimal(const arb_t x, slong D, slong prec)
{
    fmpz_t p10, lo, hi, ip;
    arf_t b;
    arb_t y;
    char * s = NULL;
    fmpz_init(p10); fmpz_init(lo); fmpz_init(hi); fmpz_init(ip); arf_init(b); arb_init(y);
    if (arb_is_nonnegative(x))
    {
        fmpz_ui_pow_ui(p10, 10, D);
        arb_mul_fmpz(y, x, p10, prec + 64);
        arb_get_lbound_arf(b, y, prec + 64); arf_get_fmpz(lo, b, ARF_RND_FLOOR);
        arb_get_ubound_arf(b, y, prec + 64); arf_get_fmpz(hi, b, ARF_RND_FLOOR);
        if (fmpz_equal(lo, hi))
        {
            char * frac;
            size_t lf, i;
            fmpz_tdiv_qr(ip, hi, lo, p10);          /* integer part, fractional digits */
            frac = fmpz_get_str(NULL, 10, hi);
            lf = strlen(frac);
            {
                char * is = fmpz_get_str(NULL, 10, ip);
                size_t li = strlen(is);
                s = flint_malloc(li + 1 + D + 2);
                memcpy(s, is, li); s[li] = '.';
                for (i = 0; i < (size_t) D - lf; i++) s[li + 1 + i] = '0';
                memcpy(s + li + 1 + (D - lf), frac, lf);
                s[li + 1 + D] = '\0';
                flint_free(is);
            }
            flint_free(frac);
        }
    }
    fmpz_clear(p10); fmpz_clear(lo); fmpz_clear(hi); fmpz_clear(ip); arf_clear(b); arb_clear(y);
    return s;
}

int main(int argc, char ** argv)
{
    const constant_t * C = NULL;
    const char * method = "theta", * out = NULL, * partial = NULL, * combine = NULL;
    slong part = 0, nparts = 1;
    slong digits, guard = 10, prec, u0_exp = -1, i, nd = 0, nk = 0, nd_eff = 0, nk_eff = 0;
    int threads = 1;
    double c0, w0, setup_cpu = 0, setup_wall = 0;
    phase_time_t td = {0, 0}, tk = {0, 0};
    arb_t res, lin, t;
    char * str;

    if (argc >= 2 && !strcmp(argv[1], "--list")) { usage(); return 0; }
    if (argc < 3) { usage(); return 1; }
    for (i = 0; i < (slong) NUM_CONSTANTS; i++)
        if (!strcmp(argv[1], CONSTANTS[i]->name)) C = CONSTANTS[i];
    if (C == NULL) { fprintf(stderr, "unknown constant %s\n", argv[1]); usage(); return 1; }
    digits = atol(argv[2]);
    for (i = 3; i < argc; i++)
    {
        if (!strcmp(argv[i], "--method") && i + 1 < argc) method = argv[++i];
        else if (!strcmp(argv[i], "--threads") && i + 1 < argc) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--u0-exp") && i + 1 < argc) u0_exp = atol(argv[++i]);
        else if (!strcmp(argv[i], "--guard") && i + 1 < argc) guard = atol(argv[++i]);
        else if (!strcmp(argv[i], "--out") && i + 1 < argc) out = argv[++i];
        else if (!strcmp(argv[i], "--part") && i + 1 < argc)
        {
            if (sscanf(argv[++i], "%ld/%ld", &part, &nparts) != 2 || nparts < 1 || part < 0 || part >= nparts) { usage(); return 1; }
        }
        else if (!strcmp(argv[i], "--partial") && i + 1 < argc) partial = argv[++i];
        else if (!strcmp(argv[i], "--combine") && i + 1 < argc) combine = argv[++i];
        else { usage(); return 1; }
    }
    if (u0_exp < 0) u0_exp = C->u0_exp;
    prec = (slong) ceil((digits + guard) * 3.3219280948873623) + 16;
    engine_set_u0(u0_exp, prec);
    arb_init(res); arb_init(lin); arb_init(t);
    c0 = cpu_seconds(); w0 = wall_seconds();

    if (combine != NULL)
    {
        /* sum the partial results and finish */
        char * list = strdup(combine), * tok;
        arb_zero(lin);
        for (tok = strtok(list, ","); tok != NULL; tok = strtok(NULL, ","))
        {
            FILE * fp = fopen(tok, "r");
            char * buf; long len;
            if (fp == NULL) { fprintf(stderr, "cannot read %s\n", tok); return 1; }
            fseek(fp, 0, SEEK_END); len = ftell(fp); fseek(fp, 0, SEEK_SET);
            buf = malloc(len + 1);
            if (fread(buf, 1, len, fp) != (size_t) len) { fprintf(stderr, "read error\n"); return 1; }
            buf[len] = '\0'; fclose(fp);
            while (len > 0 && (buf[len - 1] == '\n' || buf[len - 1] == ' ')) buf[--len] = '\0';
            if (arb_load_str(t, buf)) { fprintf(stderr, "bad partial file %s\n", tok); return 1; }
            arb_add(lin, lin, t, prec + 64);
            free(buf);
        }
        free(list);
        C->finish(res, lin, prec);
        method = "theta-combined";
    }
    else if (!strcmp(method, "theta"))
    {
        wrap_ctx w;
        ENGINE_THREADS = threads;
        ENGINE_NEED_MAIN = (part == 0);
        C->setup(prec);
        setup_cpu = cpu_seconds() - c0; setup_wall = wall_seconds() - w0;
        nd = (C->dual_count != NULL) ? C->dual_count(prec) : dual_term_count(prec);
        nk = ((C->k_count != NULL) ? C->k_count(prec) : k_term_count(prec)) - (C->k_first - 1);
        w.C = C; w.nonzero = 0; w.part = part; w.nparts = nparts; pthread_mutex_init(&w.mtx, NULL);
        nd = (nd > part) ? (nd - part + nparts - 1) / nparts : 0;
        nk = (nk > part) ? (nk - part + nparts - 1) / nparts : 0;
        w.dual = 1; parallel_sum(t, nd, wrap_term, &w, prec, threads, &td); nd_eff = w.nonzero;
        arb_set(lin, t);
        w.nonzero = 0;
        w.dual = 0; parallel_sum(t, nk, wrap_term, &w, prec, threads, &tk); nk_eff = w.nonzero;
        arb_add(lin, lin, t, prec + 64);
        if (part == 0)
        {
            C->main_term(t);
            arb_add(lin, lin, t, prec + 64);
        }
        if (nparts == 1) C->finish(res, lin, prec);
        else
        {
            char * ds = arb_dump_str(lin);
            FILE * fp;
            if (partial == NULL) { fprintf(stderr, "--part needs --partial FILE\n"); return 1; }
            fp = fopen(partial, "w");
            if (fp == NULL) { fprintf(stderr, "cannot write %s\n", partial); return 1; }
            fprintf(fp, "%s\n", ds); fclose(fp); flint_free(ds);
            arb_set(res, lin);
        }
        pthread_mutex_destroy(&w.mtx);
        C->clear();
    }
    else if (!strcmp(method, "zeta") && C->ref_zeta != NULL)
        C->ref_zeta(res, prec, threads);
    else if (!strcmp(method, "em") && C->ref_em != NULL)
        C->ref_em(res, prec, threads);
    else if (!strcmp(method, "direct") && C->ref_direct != NULL)
        C->ref_direct(res, prec, threads);
    else { fprintf(stderr, "method %s not available for %s\n", method, C->name); return 1; }

    {
        double cpu = cpu_seconds() - c0, wall = wall_seconds() - w0;
        slong acc = arb_rel_accuracy_bits(res);
        int ok;
        str = (nparts == 1) ? truncated_decimal(res, digits, prec) : NULL;
        ok = (str != NULL);
        if (out != NULL && ok)
        {
            FILE * fp = fopen(out, "w");
            if (fp == NULL) { fprintf(stderr, "cannot write %s\n", out); return 1; }
            fprintf(fp, "%s\n", str);
            fclose(fp);
        }
        if (nparts > 1) printf("{\"part\": \"%ld/%ld\", \"partial\": \"%s\", ", part, nparts, partial); else printf("{");
        printf("\"constant\": \"%s\", \"method\": \"%s\", \"digits\": %ld, \"guard_digits\": %ld, \"prec_bits\": %ld, "
               "\"threads\": %d, \"u0\": \"1/%ld\", \"dual_terms\": %ld, \"k_terms\": %ld, "
               "\"setup_cpu\": %.3f, \"setup_wall\": %.3f, \"dual_cpu\": %.3f, \"dual_wall\": %.3f, "
               "\"k_cpu\": %.3f, \"k_wall\": %.3f, \"total_cpu\": %.3f, \"total_wall\": %.3f, "
               "\"peak_rss_kb\": %ld, \"accuracy_bits\": %ld, \"rounding_ok\": %d, \"head\": \"%.52s\", \"file\": \"%s\"}\n",
            C->name, method, digits, guard, prec, threads, (long) (1L << (2 * u0_exp)),
            nd_eff, nk_eff, setup_cpu, setup_wall, td.cpu, td.wall, tk.cpu, tk.wall, cpu, wall,
            peak_rss_kb(), acc, ok, ok ? str : "", (out != NULL && ok) ? out : "");
        fflush(stdout);
        if (str != NULL) flint_free(str);
        if (!ok && nparts == 1) fprintf(stderr, "holsum: the result is not accurate enough to truncate to %ld digits\n", digits);
    }
    arb_clear(res); arb_clear(lin); arb_clear(t);
    engine_clear();
    flint_cleanup_master();
    return 0;
}
