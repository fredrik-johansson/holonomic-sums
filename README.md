# holsum

Demonstration code for the paper *Computing infinite sums of holonomic functions*
(repository: <https://github.com/fredrik-johansson/holonomic-sums>).

The program computes constants of the form

$$S = \sum_{k \ge k_0} F(k)$$

where $F(k) = f(1/k)$ and $f$ is a holonomic function analytic at the origin (possibly with logarithmic
factors). It uses **theta splitting**, a generalization of Riemann's splitting of the zeta function that needs
$\widetilde O(p^{3/2})$ bit operations for $p$ bits, against roughly $p^2$ for the classical methods.
Two classical methods are included as references: the **zeta-value expansion** and **Euler–Maclaurin
summation**. The point of the code is to show that the method works and to measure how it scales; it is
generic and not heavily optimized. (The optimized implementation for Khinchin's constant, which belongs to
the same family, is separate and is not part of this repository; the three generic `khinchin_*` constants below
compare the three representations of Khinchin's constant in the paper with the same machinery.)

## Constants

| name | value | definition |
|---|---|---|
| `A340440` | 1.0231387264279392955… | $\sum_{k\ge2} \log k/(k^2-1) = -\sum_{i\ge1}\zeta'(2i)$ ([OEIS A340440](https://oeis.org/A340440)) |
| `A085361` | 0.7885305659115089610… | $\sum_{k\ge1} \log k/(k(k+1))$ ([A085361](https://oeis.org/A085361)); $e^{C-1}$ is the Alladi–Grinstead constant |
| `Kminus1` | 1.7454056624073468634… | Khinchin's harmonic mean $K_{-1} = \log 2 \big/ \sum_{k\ge1} k^{-1}\log\bigl(1 + 1/(k(k+2))\bigr)$ |
| `vortex` | 0.2688277250400421579… | $U(1)$: the extra speed, in units of $\Gamma/r$, of a ring in a row of coaxial vortex rings spaced one radius apart: $\lambda^{-3}\sum_{n\ge1} n^{-3}\, {}_2F_1(\tfrac32,\tfrac32;2;-4/(n\lambda)^2)$ at $\lambda = 1$ |
| `hardy_littlewood` | 1.4728282319561852962… | the Hardy–Littlewood function $H(x) = \sum_{k\ge1} \sin(x/k)/k$ at $x = 1$ |
| `somos` | 1.6616879496335941212… | Somos's quadratic recurrence constant $\sigma = \prod_{k\ge1} k^{1/2^k}$ ([A112302](https://oeis.org/A112302)), $\log\sigma = -\partial_s \mathrm{Li}_s(\tfrac12)\vert_{s=0}$ |
| `expsqrt` | 1.6704068179663397212… | the damped sum $\sum_{k\ge1} e^{-\sqrt k}$ |
| `khinchin_Z` | 2.6854520010653064453… | Khinchin's constant from $\log K = -Z'(0)$, $Z(s) = \sum_{k\ge1} \log_2\bigl(1 + 1/(k(k+2))\bigr) k^{-s}$ (the splitting differentiated in $s$) |
| `khinchin_log` | 2.6854520010653064453… | Khinchin's constant from $\log K \log 2 = -\sum_{k\ge2} \log(1 - 1/k)\log(1 + 1/k)$ |
| `khinchin_dilog` | 2.6854520010653064453… | Khinchin's constant from $\log K\log 2 = \log^2 2 + \mathrm{Li}_2(-\tfrac12) + \tfrac12\sum_{k\ge2}(-1)^k\mathrm{Li}_2(4/k^2)$ |
| `theodorus` | 1.8600250792211903071… | the constant of Theodorus $\sum_{k\ge1} 1/((k+1)\sqrt k)$ ([A226317](https://oeis.org/A226317)), a sum of an algebraic function: $\zeta_F(\tfrac12)$ with $F(k) = 1/(k+1)$ |

Two constants take a parameter from the environment: `HOLSUM_VORTEX_S=s` gives the vortex sum at
$\lambda = 2/s$ (default $s = 2$), and `HOLSUM_HL_X=x` gives $H(x)$ for an integer $x$ (default 1).

## Methods

**Theta splitting** (`--method theta`, the default). With a kernel $h$ such that $F(k) = \int_0^\infty h(u)
e^{-k^2u}\,du$ (up to elementary factors), the sum becomes $\int_0^\infty h(u)\Theta(u)\,du$ with
$\Theta(u) = \sum_k e^{-k^2 u}$. The integral is split at $u_0$. Above $u_0$ it is evaluated term by term in
$k$ (the *k-terms*: incomplete gamma functions times rational series, summed by binary splitting). Below
$u_0$, Jacobi's transformation $\Theta(u) \approx \tfrac12\sqrt{\pi/u} + \sqrt{\pi/u}\sum_m e^{-\pi^2m^2/u}$
gives a *main term* and the *dual terms*: moments $\int_0^{u_0} h(u)u^{-1/2}e^{-\pi^2m^2/u}\,du$, which
satisfy linear recurrences and differential equations in $c = \pi^2m^2$ and are evaluated with the bit-burst
algorithm. About $\sqrt{p}$ terms are needed on each side, each costing $\widetilde O(p)$. The split point is
$u_0 = 4^{-a}$ (option `--u0-exp a`); the defaults are $u_0 = 1/16$ for the three logarithmic sums and $u_0 = 1/4$
for the other two. Changing $u_0$ changes every term but not the sum, which makes it a good self-check.

The last two constants are values of *damped* functions (Section 4 of the paper), whose summands carry an
exponential factor that is not regular at infinity. For `somos` the factor $2^{-k}$ is a twist by a complex
characteristic: the theta function $\sum_k z^k e^{-k^2u}$ is transformed with dual points $\pi^2(n - \alpha)^2$,
$z = e^{2\pi i\alpha}$, which are complex; this is Crandall's formula for the polylogarithm, differentiated in $s$.
The $k$-terms are incomplete gamma functions $\Gamma(0, x)$ and $\Gamma(\tfrac12 + \epsilon, x)$ (to first order in
$\epsilon$), from Legendre's continued fraction or the lower series; the dual terms need $\Gamma(0, y)$ and
$\Gamma(\tfrac12, y)$ at complex $y$, by the bit-burst algorithm from a real starting point. For `expsqrt` the factor
$e^{-\sqrt k}$ goes into the kernel, which becomes an entire function of $u^{-1/4}$ in three classes; each $k$-term
needs three incomplete gamma functions and rational series, and each dual term the bit-burst evaluation of three moment
systems of dimension 8. The references are direct summation over prime powers for `somos`
($\log\sigma = \sum_p \log p \sum_{e\ge1} 1/(2^{p^e}-1)$, `--method direct`) and Euler–Maclaurin summation for
`expsqrt`. The default split points are $u_0 = 1$ and $u_0 = 1/16$. For the three Khinchin constants they are
$u_0 = 1/16$ (`khinchin_Z`, `khinchin_dilog`) and $u_0 = 1/64$ (`khinchin_log`), the best of $4^{-1}, \dots, 4^{-4}$ at
$10^4$ digits.

For `theodorus` the splitting is taken at $s = \tfrac12$, so the kernel involves $\Gamma(m + \tfrac14)$ and
$\Gamma(m + \tfrac34)$. Because $F$ is rational, the $k$-terms close: each is two incomplete gamma functions
$\Gamma(\tfrac14, k^2u_0)$, $\Gamma(\tfrac34, k^2u_0)$ and $e^{-k^2u_0}$. The two dual systems (dimensions 3 and 4)
have quarter-integer $t_0$ and starting values from $\Gamma(\tfrac14, y)$ and $\Gamma(\tfrac34, y)$. The reference is
Euler–Maclaurin summation; the default split point is $u_0 = 1/16$.

**Zeta-value expansion** (`--method zeta`). Expanding $f$ in its Taylor series,
$\sum_k f(1/k) = \sum_n a_n \zeta(n)$; the terms $k \le 31$ are taken out (summed in closed form) so that the
series converges geometrically, like $32^{-n}$. The zeta values are computed with FLINT, in blocks of
consecutive arguments, in parallel; for each value the fastest of FLINT's algorithms is used (Bernoulli
numbers for even arguments, the Borwein algorithm for small odd arguments, the Euler product for large odd
arguments). This needs $O(p)$ zeta values at $p$ bits and is quasi-quadratic or worse.

**Euler–Maclaurin summation** (`--method em`). Direct summation up to $M \approx p/4$, the integral of $F$
from $M$ to $\infty$ in closed form, and the Bernoulli corrections. The Taylor coefficients of $F$ at $M$ are
generated from a linear recurrence (from the differential equation of $F$, or from $F = L/q$ with $L$ a
combination of logarithms and $q$ a polynomial) and combined with the Bernoulli numbers from FLINT's reverse
Bernoulli iterator, in segments, so that the memory stays bounded.

**Error control.** All arithmetic is ball arithmetic (FLINT's `arb_t`), so rounding errors are bounded
rigorously, but the numbers of terms of the truncated series (k-terms, dual terms, the series inside each term,
the zeta-value series) are chosen heuristically from estimates of the terms, without proven tail bounds.
The results are validated by agreement between the methods, between different split points, and between
precisions.

## Building

The code needs [FLINT](https://flintlib.org) 3 (it was developed against 3.7.0-dev) and a C compiler.

```sh
git clone https://github.com/fredrik-johansson/holonomic-sums
cd holonomic-sums
make FLINT_DIR=/path/to/flint                  # a FLINT source tree built in place
make FLINT_PREFIX=/path/to/flint/installation  # or an installed FLINT (default /usr/local)
```

With `FLINT_DIR`, the library is taken from the top directory of the FLINT tree and the headers from its
`build/include`; the path to the library is recorded in the binary, so no `LD_LIBRARY_PATH` is needed. If FLINT is
installed in a standard location, `make` is enough. Additional paths (for example for GMP and MPFR) can be given with
`CPPFLAGS=-I...` and `LDFLAGS=-L...`. The build produces the single binary `holsum`.

The paper is in `paper/` (`zetaseries.tex`; the figure data `khcf_gm.dat` and the scripts behind the continued
fraction computations are in the same directory).

## Running

```
./holsum CONSTANT DIGITS [--method theta|zeta|em|direct] [--threads N] [--u0-exp A] [--guard G] [--out FILE]
         [--part I/N --partial FILE] [--combine FILE,FILE,...]
./holsum --list
```

The value is computed to `DIGITS + G` digits (`G = 10` by default) and the first `DIGITS` digits after the
decimal point, truncated (rounded down), are written to `FILE`. The program checks that the truncation is
determined by the computed ball; if not, nothing is written and `rounding_ok` is 0. A one-line JSON report is
printed to standard output:

```sh
$ ./holsum vortex 10000 --threads 8 --out vortex.txt
{"constant": "vortex", "method": "theta", "digits": 10000, "guard_digits": 10, "prec_bits": 33269,
 "threads": 8, "u0": "1/4", "dual_terms": 24, "k_terms": 303, "setup_cpu": 0.007, "setup_wall": 0.007,
 "dual_cpu": 5.729, "dual_wall": 5.619, "k_cpu": 5.615, "k_wall": 5.558, "total_cpu": 11.351,
 "total_wall": 11.184, "peak_rss_kb": 48016, "accuracy_bits": 33267, "rounding_ok": 1,
 "head": "0.26882772504004215799420784633078761581126503327691", "file": "vortex.txt"}
```

(line breaks added). `dual_terms` and `k_terms` count the nonzero terms on each side; `setup` is the main
term and the precomputation shared by the dual terms; times are CPU seconds (all threads) and wall-clock
seconds; `peak_rss_kb` is the peak resident memory of the process. For the reference methods only the total
times are reported. `HOLSUM_DEBUG=1` prints the magnitude and radius of every theta term to standard error.

Long theta computations can be split into pieces: `--part I/N --partial FILE` computes only the terms with index
$\equiv I \pmod N$ on both sides (and the main term for $I = 0$) and writes their sum, as an exact ball, to `FILE`;
`--combine FILE,FILE,...` adds the pieces and finishes the computation. The pieces can run in separate processes or
sessions.

### The benchmark script

`run.py` runs the whole matrix and checks it:

```sh
./run.py                      # 10^3, 10^4, 10^5, 10^6 digits, all constants, 8 threads
./run.py --digits 1000,10000 --threads 4
./run.py --constants vortex --max-zeta 1000000
```

It computes every constant at each size in turn, with theta splitting up to $10^6$ digits and the reference
methods up to $10^5$ digits, except Euler–Maclaurin for `vortex`, which stops at $10^4$ digits (change with
`--max-theta`, `--max-zeta`, `--max-em`, `--max-em-vortex`). Results go to `results/`:

* `results/digits/CONSTANT_METHOD_DIGITS.txt`: the digits;
* `results/runs.jsonl`: one JSON record per run, as above;
* `results/summary.md`, `results/summary.csv`: a table of all runs, with a cross-check column: every digit
  file is compared with every other file for the same constant (a truncation to fewer digits must be a prefix
  of a truncation to more digits).

Finished runs are skipped when the script is restarted, so a long run can be interrupted and resumed.

## Costs

CPU seconds (summed over threads) on a small virtual machine with 2 cores, 2 threads, theta splitting at the
default $u_0$; in parentheses the peak memory in MB where it exceeds 100 MB.

| constant | digits | k-terms | dual terms | theta | zeta | em |
|---|--:|--:|--:|--:|--:|--:|
| `A340440` | $10^4$ | 606 | 12 | 2.7 | 5.2 | 7.8 |
| | $10^5$ | 1918 | 38 | 147 | 1065 | 2434 (344) |
| | $3\cdot10^5$ | 3323 | 66 | 942 (232) | | |
| `A085361` | $10^4$ | 606 | 12 | 8.6 | 33 | 8.0 |
| | $3\cdot10^4$ | | | 60 | 736 | 136 (171) |
| | $10^5$ | 1918 | 38 | 489 | | |
| `Kminus1` | $10^4$ | 606 | 12 | 17 | 34 | 11 |
| | $10^5$ | 1918 | 38 | 892 (336) | | |
| | $3\cdot10^5$ | 3323 | 66 | 5645 (483) | | |
| `vortex` | $10^4$ | 303 | 24 | 11 | 56 | 66 |
| | $3\cdot10^4$ | | | 76 | 1324 (269) | 1430 (259) |
| | $10^5$ | 959 | 76 | 583 (121) | | |
| `hardy_littlewood` | $10^4$ | 303 | 24 | 6.0 | 1.2 | 9.3 |
| | $3\cdot10^4$ | | | 48 | 16 | 169 (172) |
| | $10^5$ | 959 | 76 | 407 | 285 | 3784 (345) |

For the two damped constants, CPU seconds with 8 threads on the machine of the paper (AMD Ryzen 7 PRO 5850U), as in
`results/summary.md`; `theta` as above, the reference is direct summation over prime powers for `somos` and
Euler–Maclaurin for `expsqrt`, and peak memory in MB in parentheses where it exceeds 100 MB:

| constant | digits | k-terms | dual terms | theta | reference |
|---|--:|--:|--:|--:|--:|
| `somos` | $10^4$ | 152 | 48 | 10.4 | 1.07 |
| | $10^5$ | 480 | 152 | 652 (148) | 142 (1188) |
| | $10^6$ | 1517 | 483 | 41423 (948) | |
| `expsqrt` | $10^4$ | 608 | 12 | 15.9 | 2.9 |
| | $10^5$ | 1920 | 38 | 1025 (400) | 1703 (321) |
| | $10^6$ | 6069 | 120 | 66975 (3201) | |

The theta splitting grows by a factor of 63–65 per decade for both, from $10^4$ to $10^5$ and from $10^5$ to $10^6$
digits. Direct summation for `somos` is quasi-quadratic but very cheap, so it is still ahead at $10^5$ digits.

All runs agree with each other to all digits, and the $10^5$-digit values agree with earlier runs of
separate programs. The cost of theta splitting grows by a factor of about 55 per decade at these sizes ($p^{3/2}$ times
logarithmic factors), the cost of the references by factors of several hundred. The zeta-value expansion of
$H(1)$ is the exception: its coefficients decay factorially and it only needs even zeta values, so it stays
cheap until well beyond $10^5$ digits. At $10^4$ digits Euler–Maclaurin is competitive for the logarithmic sums;
theta splitting is ahead of both references from a few times $10^4$ digits on. Extrapolating (a factor of about 7.5 from $3\cdot10^5$ to $10^6$ digits), theta splitting at $10^6$ digits
should take roughly 2 CPU hours for `A340440` and 12 for `Kminus1`, the other constants in between, with peak
memory of the order of 1–2 GB. The zeta-value expansions at $10^5$ digits take one to several CPU hours
(`vortex` the most), and Euler–Maclaurin at $10^5$ digits about an hour, except for `vortex`, whose direct
part evaluates one ${}_2F_1$ per term, so `run.py` stops it at $10^4$ digits.

## Files

* `src/engine.c`, `src/engine.h`: the generic theta-splitting engine: binary splitting of matrix
  recurrences, incomplete gamma functions at dyadic points, the bit-burst evaluation of the dual moment
  systems, term counts, a thread pool, timing.
* `src/logsums.c`: `A340440`, `A085361`, `Kminus1` (the theta splitting and both references).
* `src/vortex.c`: `vortex`.
* `src/hardy_littlewood.c`: `hardy_littlewood`.
* `src/somos.c`: `somos` (geometric factor, complex dual points).
* `src/expsqrt.c`: `expsqrt` (stretched-exponential kernel).
* `src/khinchin.c`: `khinchin_Z`, `khinchin_log`, `khinchin_dilog`. The dual moment systems are built generically
  from first-order $\vartheta$-relations between the kernel functions (a table per system), with starting values from
  one binary splitting of the kernel coefficients times the recurrence of $D_a$; `khinchin_Z` also needs moments with
  a weight $\log u$ and $\partial_b\Gamma(b, y)$ at $b = \tfrac12$ and $b = 0$. The reference method (`--method zeta`)
  is FLINT's `arb_const_khinchin`.
* `src/tsys.c`, `src/tsys.h`: the generic moment systems from $\vartheta$-relations used by `khinchin.c` and
  `theodorus.c` ($t_0$ a multiple of $\tfrac12$ or of $\tfrac14$), the Kronecker sums for the starting values, and
  $\partial_b\Gamma(b, y)$.
* `src/theodorus.c`: `theodorus`.
* `src/refs.c`: shared code for the reference methods.
* `src/main.c`: the command-line program.
* `run.py`: the benchmark script.

The formulas (kernels, moment systems, starting values) are derived in the paper, Section 6; each source file
starts with a summary.
