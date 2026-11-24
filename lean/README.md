# ZetaF — a Lean 4 / Mathlib formalization of *Computing infinite sums of holonomic functions*

This is a formalization of parts of `paper/zetaF.tex` (F. Johansson, November 2026 draft), built on Mathlib
(`master`, Lean `v4.37.0-rc1`).

* To build: run `lake exe cache get && lake build` in this directory (about 6,700 lines in 32 files).
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
| **Remark 3.7**, twisted splitting with the paper's `J^χ_n = Z_{1/2+δ}[h_{s+δ}](π²n²/q²)` and `M^χ`: even part (`Re s > 1`), odd part (`Re s > 2`), arbitrary periodic `χ` (`Re s > 2`) | `theta_split_char`, `zetaTail_split_char` (`Twisted/Split.lean`); `theta_split_char_odd`, `zetaTail_split_char_odd`, `zetaTail_split_periodic` (`Twisted/SplitOdd.lean`) | proved for `Re s` large (the continuation is not done) |
| **Theorem 4.1(1) on `|z| = 1`**: `Li_F^{≥k₀}(s,z) = ∑(C_k I_k(s) + k S_k I_k(s+1)) + (√π/2)∑_{n∈ℤ}(J^{(0)}_s(c_n) - iπ(n-α)J^{(1)}_{s+1}(c_n)) - ½H(s) - ∑_{k<k₀}(…)`, `c_n = π²(n-α)²` | `tsum_geo_theta`, `tsum_geo_theta_odd`, `tsum_geoC_theta`, `tsum_geoS_theta` (`Polylog/Theta.lean`); `split_theta_lin` (`Polylog/Split.lean`); `polylogTail_split` (`Polylog/Geometric.lean`) | proved for real `α` and `Re s > 2`; the paper then continues in `α` to `|z| < 1` (not formalized) |
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

## Findings about the paper (1, 2 and 4 fixed in `paper/zetaF.tex` on this branch)

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

## Roadmap (not done)

* The continuation of the twisted and geometric splittings to all `s`, and of the geometric one in
  `α` to `|z| < 1` (needs `J^{(δ)}_w` on the slit plane and a boundary-uniqueness argument);
  the damped splittings (Propositions 4.2–4.3, which need the inverse Laplace transform of
  `e^{-τx^r}x^{-s}`). `split_theta_lin` and the `Continuation/` files are the templates.
* (G3); the analytic content of the bit-burst step (Taylor recurrence, radius of convergence).
* `EvenPartFuchsian`, `OddPartFuchsian` (Fuchs's criterion).
