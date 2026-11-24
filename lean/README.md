# ZetaF — a Lean 4 / Mathlib formalization of *Computing infinite sums of holonomic functions*

This is a formalization of parts of `paper/zetaF.tex` (F. Johansson, November 2026 draft), built on Mathlib
(`master`, Lean `v4.37.0-rc1`).

* To build: run `lake exe cache get && lake build` in this directory (about 3,700 lines in 21 files).
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
| Kernel `h_s`, Laplace representation (3.3) | `kernel`, `hasSum_laplace_kernel` (`Splitting/Kernel.lean`) | proved |
| **Theorem 3.2** for `Re s > 1` | `zetaTail_split` | proved |
| **Theorem 3.2 for all `s`**: `I_k`, `J_m` entire; `∑I_k`, `∑J_m` entire; `M` meromorphic with poles only at `1-n`; the identity | `kTermEntire`, `dualTermEntire`, `differentiable_sum_kTerm`, `differentiable_sum_dualTerm`, `differentiableOn_mainSeries`, `differentiableOn_splitRHS`, `zetaTail_eq_splitRHS`, `zetaTailContinuation` (`Continuation/`) | proved |
| The split point `u₀` is a free parameter (the paper's self-check) | `splitRHS_indep` | proved, by the identity theorem on `ℂ ∖ {1,0,-1,…}` |
| Series forms `I_k = ∑ a_n k^{-s-n} Q((s+n)/2, k²u₀)`, `M = ∑ a_n(…)`, `J_m = ∑ a_n D_{(s+n-1)/2}/Γ` | `hasSum_kTerm_gammaQ`, `hasSum_mainSeries`, `hasSum_dSeries` | proved (`I_k`, `J_m` for all `s`; `M` for `Re s > 1`, then by continuation) |
| **Lemma 3.1** (recurrence part): Γ-twist, (H) preserved, constant top θ-coefficient | `annihilatesEventually_gammaTwist`, `IsFuchsian.gammaTwist`, `gammaTwist_top_coeff` | proved |
| (3.5), `Z_t[u^j g] = Z_{t-j}[g]`, `C_t` recurrence, (3.7), `-∂_c Z_t = Z_{t+1}` | `dualMoment_ibp`, `dualMoment_mul_pow`, `dualMoment_one_rec`, `momentD_rec`, `hasDerivAt_dualMoment` | proved |
| **Proposition 3.3**, row recurrence | `dualMoment_system_rec` | proved (the matrices `B₀, B₁` are not assembled) |
| `Q(a+1,x) = Q(a,x) + x^a e^{-x}/Γ(a+1)` | `gammaQ_add_one` | proved for all `a ∈ ℂ` |
| Truncation (A.1), balancing `p log2/π ≤ KM`, `(K-1)(M-1) < p log2/π` | `Bounds/Truncation.lean` | proved |
| Binary-splitting cost (A.1): `≤ S` bits per level, cost `≤ d·M(S)` | `Bounds/BinarySplitting.lean` | proved (scalar version) |
| Γ bounds: monotone ratio, uniform (G1)-type bound on `{Re w ≥ 1, |Im w| ≤ Y}`, `y^x ≤ e^y Γ(x+1)` | `GammaBounds.lean`, `GammaUniform.lean` | proved |

## Design notes

* **Holonomy is defined on coefficient sequences.** Operators are polynomials in `x` with coefficients in
  `K[θ]`, which is the form condition (H) is stated in.
* **Regular class.** `FrobeniusData` takes the expansion (2.1) as data and requires each `f_{σ,j}` to
  satisfy (H). This is the form Appendix A.2 reduces to; Mathlib has no Frobenius theory.
* **`1/Γ` is Mathlib's `(Gamma ·)⁻¹`,** which is `0` at the poles, so it is the entire function `1/Γ`.
  Identities such as `(x)_n/Γ(x+n) = 1/Γ(x)` then hold with no case distinctions.
* **Continuation via Mellin transforms.** Each term of the series for `I_k`, `J_m` and `M` is `a_n/Γ(w)`
  times a Mellin transform of an indicator function, and is entire by
  `mellin_differentiableAt_of_isBigO_rpow`. The series converge locally uniformly because, after
  integration, the factor `Γ(Re w)` cancels against `1/Γ(w)` (bounded uniformly on compact sets by
  `gammaRatio_bounded`), and because `u₀^x/Γ(x+1) ≤ e^{u₀/λ}λ^x`.

## Findings about the paper (both fixed in `paper/zetaF.tex` on this branch)

1. **Lemma 3.1 claimed `b ∈ 𝕂(s)[u]^ℓ`, which is false as stated.** `b` involves the initial
   coefficients `β_m/Γ(m+σ₀)`. It is now stated as `b ∈ ℂ[u]^ℓ`, plus the precise normalization
   (multiply by `Γ(σ₀+m₂)`, assuming `a_n ∈ 𝕂`) under which `b ∈ 𝕂(s)[u]^ℓ`, with a proof paragraph.
2. **Theorem 4.1(1), "for all `s ∈ ℂ`".** `H(w)` and `L_k(w)` were defined by integrals that diverge for
   `Re w ≤ -n₀`. The text now defines them for all `w` by their entire termwise series, as for `M` in
   Theorem 3.2.
3. **Still open:** the first paragraph of the proof of Lemma 3.1 (`A₀`, `A₁` satisfy (H), via Fuchs's
   criterion for an LCLM). It is correct, but it is the one step resting on a cited theorem
   (`EvenPartFuchsian`, `OddPartFuchsian`).

## Roadmap (not done)

* Lemma 2.3 for all `s`; the twisted, polylogarithm and damped splittings (Remark 3.6, Theorem 4.1,
  Propositions 4.2–4.3). `theta_split` and the `Continuation/` files are the templates.
* Assembling `B₀`, `B₁` of Proposition 3.3; the bit-burst cost sum.
* The sharp form of (G1) (Euler product for `|Γ(x)/Γ(x+iy)|²`), and (G2)–(G3).
* `EvenPartFuchsian`, `OddPartFuchsian` (Fuchs's criterion).
