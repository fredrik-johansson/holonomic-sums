# ZetaF — a Lean 4 / Mathlib formalization of *Computing infinite sums of holonomic functions*

This is a formalization of parts of `paper/zetaF.tex` (F. Johansson, November 2026 draft), built on Mathlib
(`master`, Lean `v4.37.0-rc1`).

* To build: run `lake exe cache get && lake build` in this directory (about 11,000 lines in 43 files).
* There is no `sorry`, `admit` or `axiom`. The main theorems depend only on `propext`,
  `Classical.choice` and `Quot.sound`.
* `ZetaF/Open.lean` records statements as named `Prop`s and says which of them are proved.

## What is formalized

| Paper | Lean | Status |
|---|---|---|
| θ-normal form `∑ x^j q_j(θ)`, condition (H) (§3.2) | `ThetaOp`, `ThetaOp.applySeq`, `ThetaOp.IsFuchsian` (`Holonomic/ThetaOperator.lean`) | done; `apply_eq_sum` shows that the coefficient formula is the action of `∑ X^j q_j(θ)` on power series |
| P-recursive sequences (§2.1) | `IsPRecursive`, `isPRecursive_of_annihilates` | done |
| Def. 2.1: analytic and regular at ∞, `𝓡`, `𝓡_Q̄` | `AnalyticAtInftyData`, `FrobeniusData`, `IsAnalyticSeq`, `RegClass`, `RegClassQbar` (`Regular.lean`) | definitions (see design notes) |
| Def. 2.2: `ζ_F`, `L_F`, `Li_F`, `Φ_F`, `Λ_F`, tails | `zetaF`, `twistedZetaF`, `polylogF`, `lerchF`, `dampedZetaF`, `zetaTail` | definitions; all except `lerchF` via Mathlib's `LSeries` |
| **Lemma 2.3** (reduction to the analytic case) | `zetaTail_eq_sum_iteratedDeriv` | proved for `Re(s+σ) > 1` |
| Theta transformation | `theta1_eq`, `theta1_le` (`Theta.lean`) | proved |
| **Theorem 3.2**, abstract form (any continuous kernel with `u^{-1/2}h ∈ L¹(0,u₀]`, `e^{-k₀²u}h ∈ L¹(u₀,∞)`) | `theta_split` (`Splitting/Abstract.lean`) | proved |
| Kernel `h_s`, Laplace representation (7) | `kernel`, `hasSum_laplace_kernel` (`Splitting/Kernel.lean`) | proved |
| **Theorem 3.2** for `Re s > 1` | `zetaTail_split` | proved |
| **Theorem 3.2 for all `s`**: `I_k`, `J_m` entire; `∑I_k`, `∑J_m` entire; `M` meromorphic with poles only at `1-n`; the identity | `kTermEntire`, `dualTermEntire`, `differentiable_sum_kTerm`, `differentiable_sum_dualTerm`, `differentiableOn_mainSeries`, `differentiableOn_splitRHS`, `zetaTail_eq_splitRHS`, `zetaTailContinuation` (`Continuation/`) | proved |
| The split point `u₀` is a free parameter (the paper's self-check) | `splitRHS_indep` | proved, by the identity theorem on `ℂ ∖ {1,0,-1,…}` |
| **Meromorphic continuation of `ζ_F` for `F ∈ 𝓡`** (Lemma 2.3 + Theorem 3.2): holomorphic on `ℂ ∖ {1-σ-n}` | `zetaF_continuation`, `regularRHS`, `regularDomain` (`Continuation/Regular.lean`) | proved |
| Twisted theta transformation (Remark 3.7): even `χ` (`δ = 0`) and odd `χ` (`δ = 1`, `c₁ = -iπ^{3/2}q^{-2}`) | `gaussSum`, `tsum_char_theta_half` (`Twisted/Theta.lean`); `tsum_mul_cexp_shifted_sq`, `tsum_char_theta_odd_half`, `gaussSum_neg_of_odd` (`Twisted/Odd.lean`) | proved; the odd case by differentiating the shifted theta identity in a complex shift |
| **Remark 3.7**, twisted splitting with the paper's `J^χ_n = Z_{1/2+δ}[h_{s+δ}](π²n²/q²)` and `M^χ`: even part (`Re s > 1`), odd part (`Re s > 2`), arbitrary periodic `χ` (`Re s > 2`) | `theta_split_char`, `zetaTail_split_char` (`Twisted/Split.lean`); `theta_split_char_odd`, `zetaTail_split_char_odd`, `zetaTail_split_periodic` (`Twisted/SplitOdd.lean`) | proved for `Re s` large; continued below |
| **Theorem 4.1(1) on `|z| = 1`**: `Li_F^{≥k₀}(s,z) = ∑(C_k I_k(s) + k S_k I_k(s+1)) + (√π/2)∑_{n∈ℤ}(J^{(0)}_s(c_n) - iπ(n-α)J^{(1)}_{s+1}(c_n)) - ½H(s) - ∑_{k<k₀}(…)`, `c_n = π²(n-α)²` | `tsum_geo_theta`, `tsum_geo_theta_odd`, `tsum_geoC_theta`, `tsum_geoS_theta` (`Polylog/Theta.lean`); `split_theta_lin` (`Polylog/Split.lean`); `polylogTail_split` (`Polylog/Geometric.lean`) | proved for real `α` and `Re s > 2`; the paper then continues in `α` to `|z| < 1` (not formalized) |
| **Theorem 4.1(1) on `|z| = 1`, `z ≠ 1`, for all `s`**: with `H` and `L_k` replaced by their termwise series, the right-hand side is entire and equals `Li_F^{≥k₀}(s,z)` for `Re s > 2` (the dual points `c_n` stay `≥ c₁ > 0`, so the `J`-sums converge locally uniformly) | `polylogTail_entire`, `differentiable_lSeries`, `hasSum_lSeries`, `dualJ_local_bound`, `dualJOdd_local_bound` (`Continuation/Geometric.lean`) | proved |
| **Theorem 4.1(1) inside the disc**: for `z = e^{2πiα}` with `0 < Im α < min(Re α, 1 - Re α)` (i.e. `e^{-2π min(α₁,1-α₁)} < |z| < 1`, where all `Re c_n > 0`) and `Re s > 2`, `Li_F^{≥k₀}(s,z)` equals the splitting with complex dual points `c_n = π²(n-α)²`. Proof as in the paper: both sides holomorphic in `α`, equal on `0 < α < 1`; the reflection step is replaced by a boundary-uniqueness theorem proved via Morera (Painlevé for a line) | `polylogTail_split_disk`, `differentiableOn_polylogRHSC`, `differentiableOn_dualSum`, `differentiable_kSumC`, `differentiableOn_geoJC`, `continuousOn_lhs`, `differentiableOn_lhs` (`Polylog/Disk.lean`); `differentiableOn_ball_of_line`, `eqOn_zero_of_boundary` (`Analysis/Boundary.lean`) | proved; the rest of the disc needs `J` for `Re c ≤ 0` (continuation of `D_a`), not formalized |
| **… and for all `s`**: on the same region, with `H` and `L_k` given by their termwise series, both sides are entire in `s` (the dual integrals `J^{(δ)}_s(c)` for complex `c`, `Re c > 0`, are series of entire functions, with all estimates reduced to `Re c` via `|e^{-c/u}| = e^{-Re c/u}`), so the identity holds for every `s ∈ ℂ` | `polylogTail_split_disk_all`, `differentiable_polylogRHSE`, `differentiable_lhs_disk`, `differentiable_dualSum_s`, `differentiable_kSumC_s`, `hasSum_dSeriesC`, `hasSum_dSeriesOddC`, `dualJC_local_bound`, `dualJOddC_local_bound`, `differentiable_lowerDualC` (`Polylog/DiskEntire.lean`) | proved |
| **Odd `χ`: the twisted `L`-tail is entire** (main term `-∑ c_k L_k(s+1)` through the `L_k` series) | `zetaTail_char_odd_entire`, `mainTermOdd_eq_sum` (`Continuation/Geometric.lean`) | proved |
| **Proposition 5.7**: `ζ_F^{≥k₀}(s) = ∑_n a_n ζ(s+n, k₀)` (Mathlib's `riemannZeta`), holomorphic on `ℂ ∖ {1,0,-1,…}`, simple poles at `1-n` with residue `a_n`; agrees with the continuation of Theorem 3.2 | `hurwitzTail`, `zetaTail_eq_tsum_hurwitz`, `differentiableOn_hurwitzSeries`, `hurwitzSeries_residue`, `hurwitzSeries_eq_splitRHS`, `splitRHS_residue` (`Continuation/Hurwitz.lean`) | proved (for `F` analytic at `∞`) |
| **Remark 3.7, "then by continuation"**: the right-hand side of the twisted splitting is holomorphic on `ℂ ∖ {1,0,-1,…}` for every periodic `χ` (weighted `k`-sums, dual sums with `λ = π²/q²` and weights `u^{-1/2}`, `u^{-3/2}`, and the main terms through `M_k(s)` and `H(s) = ∫₀^{u₀}h_s`); for even `χ` it is independent of `u₀` and has residue `a_n χ̂(0)/q` at `1-n` | `zetaTail_periodic_continuation`, `zetaTail_char_continuation`, `twistedEvenRHS_indep`, `twistedEvenRHS_residue`, `mainSeries_residue`, `hasSum_hSeries`, `hasSum_dSeriesOdd` (`Continuation/Twisted.lean`) | proved (odd part shown holomorphic on `ℂ ∖ {0,-1,…}` only, which suffices) |
| Series forms `I_k = ∑ a_n k^{-s-n} Q((s+n)/2, k²u₀)`, `M = ∑ a_n(…)`, `J_m = ∑ a_n D_{(s+n-1)/2}/Γ` | `hasSum_kTerm_gammaQ`, `hasSum_mainSeries`, `hasSum_dSeries` | proved (`I_k`, `J_m` for all `s`; `M` for `Re s > 1`, then by continuation) |
| **Lemma 3.1** (recurrence part): Γ-twist, (H) preserved, constant top θ-coefficient | `annihilatesEventually_gammaTwist`, `IsFuchsian.gammaTwist`, `gammaTwist_top_coeff` | proved |
| (11), `Z_t[u^j g] = Z_{t-j}[g]`, `C_t` recurrence, (14), `-∂_c Z_t = Z_{t+1}` | `dualMoment_ibp`, `dualMoment_mul_pow`, `dualMoment_one_rec`, `momentD_rec`, `hasDerivAt_dualMoment` | proved |
| **Proposition 3.6**: `c Y' = (B₀ + c B₁) Y` for `Y = (W_{t-i}, C_{t-i}, E, E·𝐆(u₀))` | `dualMoment_system_rec`, `dualB0`, `dualB1`, `dual_system` (`Holonomic/DualSystem.lean`) | proved for real `c > 0`, with `B₀`, `B₁` given explicitly |
| `Q(a+1,x) = Q(a,x) + x^a e^{-x}/Γ(a+1)` | `gammaQ_add_one` | proved for all `a ∈ ℂ` |
| Truncation, term counts (18), balancing `p log2/π ≤ KM`, `(K-1)(M-1) < p log2/π` | `Bounds/Truncation.lean` | proved |
| Binary-splitting cost (App. A.1): `≤ S` bits per level, cost `≤ d·M(S)`; **bit-burst cost sum**: steps with `n_j 2^j ≤ p` terms of `≤ 2^j + L` bits cost `≤ D·M(Jp + 2Lp)` in total | `treeCost_le`, `bitBurst_cost_le` (`Bounds/BinarySplitting.lean`) | proved (scalar cost model) |
| **App. A.5**: `P(a,y) = 1 - Q(a,y) = ∑_i y^{a+i}e^{-y}/Γ(a+i+1)` for all `a ∈ ℂ` (including `a ∈ ℤ_{≤0}`), and the tail from `N` is `≤ 2|t_N|` once `Re a + N + 1 ≥ 2y` | `hasSum_gammaPTerm`, `norm_tail_gammaPTerm_le` (`IncompleteGammaSeries.lean`) | proved |
| **(G1)** (App. A.9): `|1/Γ(x+iy)| ≤ e^{π|y|/2}/Γ(x)` for `x ≥ 1/2`, and `|Γ(x+iy)| ≤ Γ(x)`, via `|Γ(x)/Γ(x+iy)|² = ∏(1 + y²/(x+n)²)` and `cosh πy` at `x = 1/2` | `norm_inv_Gamma_le_G1`, `norm_Gamma_le_Gamma_re`, `tendsto_gProd`, `ratio_half` (`GammaG1.lean`) | proved |
| **(G2)**, explicit: `|w| ≤ T ⇒ |1/Γ(w)| ≤ e^{1+πT/2}(2T+2)^{⌈T⌉+1}`, via `1/Γ(w) = (w)_N/Γ(w+N)`, (G1) and `Γ ≥ 1/e` on `[1,∞)` | `norm_inv_Gamma_le_G2`, `inv_Gamma_eq_prod_mul`, `realGamma_ge_exp_neg_one` | proved |
| **(G3)**: `|Γ(w)| ≤ Γ(Re w + N) 2^N/min(δ,1)` if `Re w + N ≥ 1` and `|w+j| ≥ δ` for `j < N` (all factors of `(w)_N` but one are `≥ 1/2`) | `norm_Gamma_le_G3`, `prod_norm_add_nat_ge` | proved (Liouville's inequality for `δ` not formalized) |
| Bit-burst Taylor recurrence `c₀(l+1)Y_{l+1} = (B₀ + c₀B₁ - l)Y_l + B₁Y_{l-1}` ⇔ `cY' = (B₀ + cB₁)Y` (formal power series at `c₀`) | `taylor_rec_iff` (`Bounds/TaylorRec.lean`) | proved |
| **Proposition 4.2, termwise forms**: for the damped kernel `h_s = ∑_j c_j u^{a_j-1}`, `I_k = ∑_j c_j ∫_{u₀}^∞ e^{-k²u}u^{a_j-1}` for `0 < r < 2`, and `J_m = ∑_j c_j D_{a_j-1/2}(π²m²)` for `0 < r < 1`; growth bounds `|1/Γ(z)| ≤ Γ(1-Re z)e^{π|Im z|}/π` and `Γ(1+aj) ≤ (j!)^a` | `hasSum_kTerm_damped`, `hasSum_dualTerm_damped` (`Damped/Kernel.lean`); `norm_inv_Gamma_le_reflect`, `Gamma_one_add_mul_le`, `summable_pow_mul_Gamma_div_factorial`, `summable_pow_mul_Gamma_sq_div_factorial` (`Damped/GammaGrowth.lean`) | proved |
| **Proposition 4.2, the identity** `Λ(s;τ,r) = ∑_k I_k + √π∑_m J_m + M` (`0 < r < 1`, `M` as an integral) | `damped_split` (`Damped/Split.lean`) | proved, assuming the kernel representation `∫₀^∞ e^{-k²u}h_s = e^{-τk^r}k^{-s}` and integrability of `h_s` (finding 6) |
| **Bit-burst radius of convergence**: solutions of that recurrence satisfy `‖Y_l‖ ≤ C t^l` for every `t > 1/|c₀|`, so `∑ h^l Y_l` converges for `|h| < |c₀|` | `taylor_rec_growth`, `taylor_rec_summable` (`Bounds/TaylorRec.lean`) | proved |
| **Bit-burst error analysis**: truncation error of a Taylor stage `≤ C(t|h|)^L/(1-t|h|)`; global error of a chain of steps with Lipschitz constants `M_j` and local errors `ε_j` is `∏M_j·‖y₀-x₀‖ + ∑ε_j∏_{i>j}M_i` (`≤ M^n(‖y₀-x₀‖ + ∑ε_j)` uniformly, operator norms for linear steps); "every tail is at most twice its first term" once terms halve; the error from the evaluation point is `δ·max|J'|` | `taylor_rec_tail_le` (`Bounds/TaylorRec.lean`); `error_propagation`, `error_propagation_uniform`, `error_propagation_linear`, `tail_le_of_ratio`, `tail_le_two_mul`, `point_error_le` (`Bounds/ErrorProp.lean`) | proved |
| Γ bounds: monotone ratio, uniform (G1)-type bound on `{Re w ≥ 1, |Im w| ≤ Y}`, `y^x ≤ e^y Γ(x+1)` | `GammaBounds.lean`, `GammaUniform.lean` | proved |

## Design notes

* **Holonomy is defined on coefficient sequences.** Operators are polynomials in `x` with coefficients in
  `K[θ]`, which is the form condition (H) is stated in.
* **Regular class.** `FrobeniusData` takes the expansion (3) as data and requires each `f_{σ,j}` to
  satisfy (H). This is the form Appendix A.2 reduces to; Mathlib has no Frobenius theory.
* **`1/Γ` is Mathlib's `(Gamma ·)⁻¹`,** which is `0` at the poles, so it is the entire function `1/Γ`.
  Identities such as `(x)_n/Γ(x+n) = 1/Γ(x)` then hold with no case distinctions.
* **Continuation via Mellin transforms.** Each term of the series for `I_k`, `J_m` and `M` is `a_n/Γ(w)`
  times a Mellin transform of an indicator function, and is entire by
  `mellin_differentiableAt_of_isBigO_rpow`. The series converge locally uniformly because, after
  integration, the factor `Γ(Re w)` cancels against `1/Γ(w)` (bounded uniformly on compact sets by
  `gammaRatio_bounded`), and because `u₀^x/Γ(x+1) ≤ e^{u₀/λ}λ^x`.

## Findings about the paper (1, 2, 4 and 5 fixed in `paper/zetaF.tex` on this branch)

1. **Lemma 3.1 claimed `b ∈ 𝕂(s)[u]^ℓ`, which is false as stated.** `b` involves the initial
   coefficients `β_m/Γ(m+σ₀)`. It is now stated as `b ∈ ℂ[u]^ℓ`, plus the precise normalization
   (multiply by `Γ(σ₀+m₂)`, assuming `a_n ∈ 𝕂`) under which `b ∈ 𝕂(s)[u]^ℓ`, with a proof paragraph.
2. **Theorem 4.1(1), "for all `s ∈ ℂ`".** `H(w)` and `L_k(w)` were defined by integrals that diverge for
   `Re w ≤ -n₀`. The text now defines them for all `w` by their entire termwise series, as for `M` in
   Theorem 3.2.
3. **Still open (not a flaw):** the first paragraph of the proof of Lemma 3.1 (`A₀`, `A₁` satisfy (H), via Fuchs's
   criterion for an LCLM). It is correct, but it is the one step resting on a cited theorem
   (`EvenPartFuchsian`, `OddPartFuchsian`).
4. **Section 4.1, analyticity of `D_a`.** "`D_a` is `c^aΓ(-a)` minus an entire function" fails for
   `a ∈ ℤ_{≥0}`, where `Γ(-a)` has a pole; there `D_a(c) = -(-c)^a/a! · log(c/u₀) +` entire.
   This case occurs in `J^{(δ)}_w` for integer `w`. The conclusion (analytic on `ℂ ∖ (-∞, 0]`) is
   unaffected; the sentence now treats both cases.

5. **Propositions 4.2–4.3 and Claim C: the series for the damped dual terms diverge for `r > 1`.** The `j`-th
   term of `J_m = ∑_j c_j D_{a_j-1/2}(π²m²)` is of size `(τ(πm)^{-r})^j Γ(rj/2)²/j!`, i.e. `(j!)^{r-1}` times a
   geometric factor: the series converges for `r < 1`, for `r = 1` only when `τ < 2πm`, and diverges for every `m`
   when `1 < r < 2` (numerically, for `r = 3/2`, `τ = 1`, `m = 1`, the terms reach `10^{232}` at `j = 800`). The proof's
   termwise integration of the dual terms ("`e^{-c/u}` kills the powers of `u`") is therefore valid only in that
   range, and the bit-burst starting values of Claim C diverge for `1 < r < 2`. The splitting identity itself is
   unaffected (with `J_m` the integral). The text now defines `J_m` by the integral, states when the series
   converges (also for `q = 1` in Proposition 4.3), restricts Claim C and its sketch to `0 < r ≤ 1`, and lists
   `1 < r < 2` as an open problem. Formalized: `hasSum_dualTerm_damped` (`r < 1`).
6. **Proposition 4.2, the kernel representation.** That the damped kernel (a Wright function) is the inverse
   Laplace transform of `e^{-τ y^{r/2}} y^{-s/2}`, and is exponentially small at `0`, is justified only briefly
   (via a Mellin transform computed "in a strip"). It is classical, but its proof needs Mellin–Barnes or Hankel
   contour arguments; `damped_split` takes it as a hypothesis.

## Roadmap (not done)

* Theorem 4.1(1) on the rest of the disc (`J^{(δ)}_w(c)` for `Re c ≤ 0`, via `D_a` on the slit plane).
* The damped splittings: the kernel representation for Proposition 4.2 (Wright functions), the main term
  `M` via complete Mellin integrals, and Proposition 4.3. `split_theta_lin` and the `Continuation/` files are the templates.
* `EvenPartFuchsian`, `OddPartFuchsian` (Fuchs's criterion).
