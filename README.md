# Computing infinite sums of holonomic functions

This is the repository of the paper *Computing infinite sums of holonomic functions* by Fredrik Johansson. It
contains:

* [`paper/zetaF.pdf`](paper/zetaF.pdf) (source `paper/zetaF.tex`): the paper;
* [`paper/analytic.pdf`](paper/analytic.pdf) (source `paper/analytic.tex`): a companion note, *Analytic properties of
  Dirichlet series of functions analytic at infinity* (growth, zeros and other analytic properties of the functions
  studied in the paper, which the algorithms do not need);
* [`lean/`](lean/): a Lean 4 / Mathlib formalization of much of the mathematics of the paper;
* [`src/`](src/), `Makefile`, `run.py`: `holsum`, a generic demonstration implementation of the algorithms;
* [`results/`](results/): computational results: the constants of the paper to $`10^6`$ digits, Khinchin's constant to
  $`10^7`$ digits, and the logs of all benchmark runs;
* `paper/checks/` (numerical checks of the splitting identities), `paper/tools/` (programs behind the statistics of the
  continued fraction of Khinchin's constant) and `paper/ahl/` (a preview build in journal style).

## The results

For a function $`F`$ that is *holonomic* (it satisfies a linear differential equation with polynomial
coefficients) and regular at infinity, the paper studies the zeta function

```math
\zeta_F(s) = \sum_{k=1}^{\infty} F(k)\, k^{-s}
```

together with its twisted, polylogarithmic, Lerch-type and damped (stretched-exponential) relatives. Values and
derivatives of these functions cover a very large class of sums and products: every sum
$`\sum_k A(k)`$ or $`\sum_k \log A(k)`$ with $`A`$ an algebraic function, sums of inverse trigonometric, hypergeometric
or elliptic functions of $`k`$, Dirichlet series and regularized values of divergent sums.

* **Theta splitting (Theorem A).** An exact approximate functional equation, generalizing Riemann's second proof of the
  functional equation of $`\zeta(s)`$, writes $`\zeta_F(s)`$ as two rapidly convergent sums (of *k-terms* decaying like
  $`e^{-k^2u_0}`$ and *dual terms* decaying like $`e^{-\pi^2m^2/u_0}`$) plus an explicit main term. When $`F`$ is
  holonomic, every term is a value of a holonomic function.
* **Complexity (Theorem B).** When the expansion of $`F`$ at infinity has algebraic coefficients, the values and
  derivatives of $`\zeta_F`$, $`L_F`$, $`\mathrm{Li}_F`$ and $`\Phi_F`$ at algebraic points can be computed to $`p`$ bits in
  $`p^{3/2+o(1)}`$ bit operations, against $`p^{2+o(1)}`$ for the classical methods (Euler–Maclaurin summation and
  expansions in zeta values). For most such numbers no subquadratic algorithm was known before. The algorithms are
  uniform in the parameters and give, for example, the Bernoulli, Euler and Fubini numbers in $`n^{3/2+o(1)}`$ bit
  operations and quasilinear memory.
* **Khinchin's constant.** Three subquadratic algorithms, from the derivative of the Khinchin zeta function, from the
  series $`\log K \log 2 = -\sum_{k\ge2}\log(1-1/k)\log(1+1/k)`$, and from a dilogarithm series of Bailey, Borwein and
  Crandall. An implementation of the last one in [FLINT](https://flintlib.org) computed $`K`$ to $`10^7`$ digits.
* **Other constants.** Worked examples from analysis, number theory, mathematical physics and probability (Section 7 of
  the paper), among them the constant of Theodorus, the Hardy–Littlewood function, Somos's quadratic recurrence
  constant, periodic arrays of vortex rings, the spectral zeta function of the sphere and a stretched-exponential sum
  related to the Landau levels of graphene, all computed to $`10^6`$ digits.

## Timings

All timings are from the paper (8 threads on an AMD Ryzen 7 PRO 5850U); CPU time is summed over the threads.

**Khinchin's constant** (optimized FLINT implementation; Table 10 of the paper):

| digits | zeta values: CPU | wall | theta splitting: CPU | wall | memory |
|--:|--:|--:|--:|--:|--:|
| $`10^5`$ | 18.7 s | 2.43 s | 88.3 s | 11.2 s | 223 MB |
| $`10^6`$ | 4 239 s | 544 s | 5 416 s | 679 s | 1.08 GB |
| $`2\cdot10^6`$ | 23 485 s | 3 372 s | 18 815 s | 2 355 s | 1.78 GB |
| $`10^7`$ | 1 852 090 s | 235 475 s | 327 183 s | 40 921 s | 10.5 GB |

At $`10^7`$ digits the theta splitting needs 5.7 times less CPU time and 5.8 times less wall time than the optimized
zeta-value expansion.

**The generic program `holsum`** (Tables 11 and 12 of the paper). Theta splitting at $`10^5`$ and $`10^6`$ digits, and
its speedup at $`10^5`$ digits over the faster of the two reference methods (zeta values, Euler–Maclaurin summation, or
the special method noted):

| constant | $`10^5`$: CPU | wall | $`10^6`$: CPU | wall | memory | speedup at $`10^5`$: CPU | wall |
|---|--:|--:|--:|--:|--:|--:|--:|
| $`\mathcal A = \sum_{k\ge2} \log k/(k^2-1)`$ | 137 s | 17.9 s | 8 435 s | 1 063 s | 1.43 GB | 7.7 | 7.5 |
| $`\mathcal C = \sum_{k\ge1} \log k/(k(k+1))`$ | 469 s | 59.7 s | 29 201 s | 3 662 s | 2.11 GB | 4.0 | 6.5 |
| $`K_{-1}`$ (Khinchin's harmonic mean) | 997 s | 127 s | 51 551 s | 6 458 s | 4.01 GB | 2.3 | 4.5 |
| Theodorus $`\mathcal T`$ | 476 s | 60.4 s | 27 804 s | 3 482 s | 1.65 GB | 0.38 | 1.9 |
| Hardy–Littlewood $`H(1)`$ | 419 s | 52.8 s | 28 465 s | 3 564 s | 2.44 GB | 0.73 | 0.74 |
| Somos $`\sigma`$ (vs. prime-power sum) | 652 s | 82.8 s | 41 423 s | 5 268 s | 948 MB | 0.22 | 0.23 |
| vortex rings $`U(1)`$ | 677 s | 85.6 s | 37 795 s | 4 736 s | 2.19 GB | 79 | 81 |
| $`\mathrm{Tr}\,\Delta^{-3/2}`$ on $`S^2`$ | 255 s | 32.7 s | 16 144 s | 2 021 s | 2.10 GB | 0.91 | 3.8 |
| $`S = \sum_{k\ge1} e^{-\sqrt k}`$ | 1 025 s | 129 s | 66 975 s | 8 379 s | 3.13 GB | 1.7 | 2.3 |

The theta splitting grows by a factor of 52–69 per decade (about $`p^{1.75}`$ to $`p^{1.85}`$), the reference methods by
factors of 130–1000; the exceptions at $`10^5`$ digits (speedup below 1) are cases where the classical method is
unusually cheap, and the crossovers are estimated in Section 7.10 of the paper. All methods agree to all digits.

## Formal verification

The directory [`lean/`](lean/) contains a Lean 4 / Mathlib formalization of much of the mathematics of the paper
(about 20,000 lines): Theorem 3.2 (theta splitting) for all $`s`$ and the meromorphic continuation of $`\zeta_F`$, the
twisted and geometric-factor splittings of Section 4, the Khinchin section (Section 6, including the error bounds of
the evaluation), and every estimate used in the complexity proofs (Appendix A.2). There are no `sorry`s and no added
axioms. Bit complexity itself is not formalized; Appendix A of the paper explains what is and is not covered and what
the formalization changed in the text. [`lean/README.md`](lean/README.md) maps the results of the paper to their Lean
names and explains how to build (`cd lean && lake exe cache get && lake build`; one file needs more than 7 GB of RAM).

## The demonstration program `holsum`

`holsum` is a generic implementation of the theta splitting in C with [FLINT](https://flintlib.org), together with the
two classical reference methods (the zeta-value expansion and Euler–Maclaurin summation). Its purpose is to show that
the method works and to measure how it scales; it is not heavily optimized. All arithmetic is ball arithmetic, so
rounding errors are bounded rigorously, but the numbers of terms of the truncated series are chosen heuristically
(without proven tail bounds); the results are validated by agreement between methods, split points and precisions.
The kernels, moment systems and starting values for each constant are derived in Section 7 of the paper, and each
source file starts with a summary.

| name | value | constant |
|---|---|---|
| `A340440` | 1.0231387264279392955… | $`\sum_{k\ge2} \log k/(k^2-1)`$ ([A340440](https://oeis.org/A340440)) |
| `A085361` | 0.7885305659115089610… | $`\sum_{k\ge1} \log k/(k(k+1))`$ ([A085361](https://oeis.org/A085361)), related to the Alladi–Grinstead constant |
| `Kminus1` | 1.7454056624073468634… | Khinchin's harmonic mean $`K_{-1}`$ |
| `theodorus` | 1.8600250792211903071… | the constant of Theodorus $`\sum_{k\ge1} 1/((k+1)\sqrt k)`$ ([A226317](https://oeis.org/A226317)) |
| `hardy_littlewood` | 1.4728282319561852962… | the Hardy–Littlewood function $`H(x) = \sum_{k\ge1} \sin(x/k)/k`$ at $`x = 1`$ |
| `somos` | 1.6616879496335941212… | Somos's quadratic recurrence constant $`\prod_{k\ge1} k^{1/2^k}`$ ([A112302](https://oeis.org/A112302)) |
| `vortex` | 0.2688277250400421579… | $`U(1)`$, the velocity induced in a row of coaxial vortex rings spaced one radius apart |
| `sphere` | 2.0705444763216059050… | $`\mathrm{Tr}\,\Delta^{-3/2} = \sum_{\ell\ge1}(2\ell+1)/(\ell(\ell+1))^{3/2}`$ on the unit sphere |
| `expsqrt` | 1.6704068179663397212… | the stretched-exponential sum $`\sum_{k\ge1} e^{-\sqrt k}`$ |
| `khinchin_Z`, `khinchin_log`, `khinchin_dilog` | 2.6854520010653064453… | Khinchin's constant from the three representations of the paper |

`HOLSUM_VORTEX_S=s` gives the vortex sum at $`\lambda = 2/s`$ (default $`s = 2`$) and `HOLSUM_HL_X=x` gives $`H(x)`$ for an
integer $`x`$ (default 1). The optimized implementation of Khinchin's constant used for the record (Section 6.6 of the paper)
is separate and not part of this repository; the generic `khinchin_*` constants compare the three representations with the same
machinery.

### Building

The code needs [FLINT](https://flintlib.org) 3 (it was developed against 3.7.0-dev) and a C compiler.

```sh
git clone https://github.com/fredrik-johansson/holonomic-sums
cd holonomic-sums
make FLINT_DIR=/path/to/flint                  # a FLINT source tree built in place
make FLINT_PREFIX=/path/to/flint/installation  # or an installed FLINT (default /usr/local)
```

With `FLINT_DIR`, the library is taken from the top directory of the FLINT tree and the headers from its
`build/include`, and the path to the library is recorded in the binary. Additional paths (for example for GMP and MPFR)
can be given with `CPPFLAGS=-I...` and `LDFLAGS=-L...`.

### Running

```
./holsum CONSTANT DIGITS [--method theta|zeta|em|direct] [--threads N] [--u0-exp A] [--guard G] [--out FILE]
         [--part I/N --partial FILE] [--combine FILE,FILE,...]
./holsum --list
```

The value is computed to `DIGITS + G` digits (`G = 10` by default), and the first `DIGITS` digits after the decimal
point, truncated, are written to `FILE` if the truncation is determined by the computed ball. A one-line JSON report
(term counts, CPU and wall times for each side, peak memory, the first digits) is printed to standard output. The split
point is $`u_0 = 4^{-a}`$ (`--u0-exp a`); changing it changes every term but not the sum, which makes it a good
self-check. Long theta computations can be split with `--part I/N --partial FILE` into pieces that run in separate
processes and are added with `--combine`.

`run.py` runs the benchmark matrix (theta splitting up to $`10^6`$ digits, the references up to $`10^5`$ digits),
checks that all digit files for a constant agree, and writes `results/digits/`, `results/runs.jsonl` and the tables
`results/summary.md` and `results/summary.csv`:

```sh
./run.py                                  # all constants, 10^3 to 10^6 digits, 8 threads
./run.py --digits 1000,10000 --threads 4  # quick check
```

Finished runs are skipped when the script is restarted. The file `results/digits/khinchin_10000000.txt` (Khinchin's
constant to $`10^7`$ digits, truncated) comes from the FLINT computation described in the paper, not from `run.py`.

### Source files

* `src/engine.c`, `src/engine.h`: the generic theta-splitting engine (binary splitting of matrix recurrences,
  incomplete gamma functions, the bit-burst evaluation of the dual moment systems, term counts, a thread pool).
* `src/tsys.c`, `src/tsys.h`: generic moment systems built from first-order $`\vartheta`$-relations.
* `src/logsums.c` (`A340440`, `A085361`, `Kminus1`), `src/theodorus.c`, `src/hardy_littlewood.c`, `src/somos.c`,
  `src/vortex.c`, `src/sphere.c`, `src/expsqrt.c`, `src/khinchin.c`: the constants.
* `src/refs.c`: shared code for the reference methods; `src/main.c`: the command-line program.
