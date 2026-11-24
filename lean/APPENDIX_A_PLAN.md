# Appendix A ("Proofs of the complexity bounds"): refactoring plan

Paper: `paper/zetaF.tex`, Appendix A. Line numbers refer to the version of `zetaF.tex` *before* the commit that added
this file (that commit also applied the one-sentence fixes for issues 1, 2, 5, 7 and 10 of §6, shifting later lines).
Lean: `lean/` (this directory).
* `plan/AppAStatements.lean`: all proposed statements below, with `sorry` bodies (a proposal, not part of the
  library; it typechecks with `lake env lean`).
* L1 is proved: `ZetaF/Bounds/TaylorStep.lean` (`taylor_step_bound`, `taylor_step_tail`).
* The numerical checks quoted in §6 were run with mpmath.

**Status (update).** Proved in `ZetaF/`: L1 (`Bounds/TaylorStep.lean`), L2 (`AppA/ProductTree.lean`), L3
(`AppA/Regularity.lean`), L4 (`AppA/KernelBounds.lean`, untwisted), L5 (`AppA/GammaSums.lean`; the tail bound L5′
needs an extra factor `4^y`, see the README), L6 (`AppA/StartValues.lean`), L7 (`AppA/BernoulliExact.lean`),
L8 (`AppA/Liouville.lean`), L9 (`AppA/LogMoments.lean`), L11 (`AppA/KTermDouble.lean`). Not done: L10 (the text now
rescales the `C`, `E` block instead), L12. A draft of the restructured appendix built on these is
`paper/appendixA_new.tex`.

---

## 0. Summary

1. **Most of the appendix is said twice.** A.1–A.8 analyse each piece for fixed data. A.9 then goes through every piece again
   (truncation, k-terms, incomplete gamma, dual terms, main term, jets) to make the same four quantities
   uniform: (a) number of pieces, (b) series lengths, (c) coefficient bit sizes, (d) magnitudes (l. 3921–3928).
   Theorem `thm:complexity` is the special case of Theorem `thm:uniform` with fixed data (everything 2^{O(p)} becomes
   O(1), and heights are O(1)). So **one proof of `thm:uniform` that cites uniform formal estimates** can replace
   A.3–A.9. The main text already has the fixed-data overview (l. 1437–1460, Table `tab:pieces`).
2. **What carries the technical load is pure mathematics:** Γ-bounds, kernel bounds, term and tail bounds for the
   hypergeometric-type series, the starting-value cancellation, the stability of the Taylor steps, the arithmetic of
   B_n. All of these can be stated and proved in Lean without a machine model. About half of them are already
   formalized (G1–G3, the incomplete-gamma series and its tail, truncation, the Taylor recurrence, error propagation,
   the product-tree size bound and the bit-burst cost sum).
3. **What stays narrative** is a short cost-model interface (§4): (M) regularity of 𝖬, (K) number-field arithmetic, (BS)
   binary splitting, (A) approximate arithmetic, (E) elementary constants. On top of it there is one "certificate"
   lemma: a series with N terms, b-bit recurrence coefficients, tail ≤ 2^{-p} and partial products ≤ 2^G costs
   O(𝖬(Nb) log N + 𝖬(p+G)). After that, each piece only needs its certificate (N, b, G), and that is the pure
   mathematics.
4. **The best ratio of text removed to effort is L1 (Taylor step), now proved.** For the Taylor recurrence of
   cY' = (B₀+cB₁)Y it gives ‖hˡY_l‖ ≤ (2θ)ˡ‖Y₀‖ for *all* solutions, as soon as
   |h|‖B₀+c₀B₁‖ ≤ θ|c₀|, |h|‖B₁‖ ≤ θ and |h| ≤ θ|c₀|. This one lemma replaces the a-priori bound / Cauchy-estimate /
   Gronwall / "other solutions grow like e^{O(√c)}" arguments in A.1, A.6, A.9 and A.11, and it repairs two of the
   issues below (§6, issues 3 and 4).
5. **Issues found** (§6), most important first:
   * In the uniform proof, the matrix B₀ contains the normalized inhomogeneity b of Lemma `lem:kernelhol`. Its
     entries are polynomials in s of degree O(S), not bounded degree, and they have Θ(p) bits when Re s₀ ≪ 0. This
     breaks claim (c) at l. 3994–3996. Checked numerically. There is an easy fix.
   * A.4 breaks down at s₀ ∈ {−2, −4, …} (odd part: {−3, −5, …}).
   * Several guard-bit and a-priori-bound claims are not justified: A.6 l. 3872–3874, A.11 l. 4139/4147 (a disk that
     leaves Re c > 0).
   * E₁ needs Euler's γ, which is not mentioned.
   * The recurrence for the main-term P-values loses precision.
   * Some small constant and wording slips.

---

## 1. Inventory: what is formalized, and how it matches the paper

| Paper | Lean | Match / mismatch |
|---|---|---|
| A.1 binary splitting: levels have O(p log p) bits, cost O(𝖬(p log p) log p) | `BinarySplitting.sum_size_level_le`, `treeCost_le`, `treeCost_le_of_size_le`, `superadditive_of_div_mono` | Leaves are **natural numbers** under a commutative product (`Nat.size`). The paper multiplies **matrices over O_K**, whose entry sizes add up to + log D per product. → L2. The final division and rounding are not modelled. Regularity `𝖬(n log n) = O(𝖬(n) log n)` is not used anywhere. → L3. |
| A.1 bit-burst cost sum | `bitBurst_cost_le` | Assumes 2^{d_j} terms with n_j 2^j ≤ p and ≤ 2^j + L bits. This matches A.1, and A.9 (b_i = 2^i b₀) after reindexing. Better than the paper: it does not need the paper's split into two kinds of steps. |
| A.1 Taylor recurrence, radius, tail | `taylor_rec_iff`, `taylor_rec_growth`, `taylor_rec_summable`, `taylor_rec_tail_le` | The constant C in the growth/tail bound is **inexplicit**, so it cannot be used for precision bookkeeping. → L1 (explicit, proved). |
| A.1/A.9 error of a chain of steps; "tail ≤ twice its first term" | `error_propagation`, `error_propagation_uniform`, `error_propagation_linear`, `tail_le_of_ratio`, `tail_le_two_mul`, `point_error_le` | Matches. Also covers the rounded running product of the blocked binary splitting (A.9 Memory). |
| A.2 Lemma `lem:reduction` | `zetaTail_eq_sum_iteratedDeriv` | Proved for Re(s+σ) > 1 only. Continuation is narrative. The monodromy argument (l. 3780–3789: f_{σ,j} satisfies (H)) is **assumed** as data in `FrobeniusData`. |
| A.3 tail bounds and counts (eq:counts) | `norm_tsum_kTerm_tail_le`, `norm_tsum_dualTerm_tail_le`, `kCount`, `mCount`, `exp_kCount_le`, `exp_mCount_le`, `kCount_mul_mCount_ge/lt` | Abstract kernel with constants C_far, C_near. **C_near = ∫₀^{u₀} u^{-1/2}\|h\| is finite only when Re s + n₀ > 1**, so the dual bound is vacuous in the continuation region. The paper absorbs the singularity with e^{-π²m²/u} ≤ e^{-π²(m²−1)/u₀}e^{-π²/u}. Also no q (twist), no uniformity in s, and "≈" is not quantified. → L4, L12. |
| A.4 series for I_k | `hasSum_kTerm_gammaQ`, `gammaQ_add_one`, `gammaQ_add_nat` | The reorganized form (eq:Ik) is **not** formalized. → L11. Checked numerically to 1e-42 (§6). |
| A.5 P(a,y) series for all a; tail ≤ 2\|t_N\| once Re a+N+1 ≥ 2y; P = 1 at a ∈ ℤ_{≤0}; Γ = γ + Γ(·,N) | `hasSum_gammaPTerm`, `norm_tail_gammaPTerm_le`, `gammaQ_neg_nat`, `Gamma_eq_lower_add_upper`, `norm_lowerGamma_le` | Exact match. **Missing:** the bound on the largest term / the magnitude G, the uniform version, and the bound on the upper tail Γ(w,N). → L5. |
| A.6 (eq:ibp), Z_t[uʲg] = Z_{t−j}[g], −∂_c Z_t = Z_{t+1}, (eq:Drec), Proposition `prop:dual` | `dualMoment_ibp`, `dualMoment_mul_pow`, `hasDerivAt_dualMoment`, `momentD_rec` (complex a), `dual_system`, `dualB0`, `dualB1` | For real c > 0 only; A.11 needs complex c (continuation: narrative). The starting-value estimates are formalized only for the Khinchin case (`Khinchin/StartVals.lean`: real a ∈ ½+ℤ, explicit α_n). → L6. |
| A.6 normalization by Γ(σ₀+m₂) | `lemma31_recurrence`, `gammaTwist_*` | The recurrence side is formalized. The b-normalization is not, and see issue 1. |
| A.8 log-moment recurrence | none | Display l. 3894–3897 checked numerically (§6). → L9. |
| A.9 (G1), (G2), (G3) | `norm_inv_Gamma_le_G1`, `norm_Gamma_le_Gamma_re`, `norm_inv_Gamma_le_G2` (explicit e^{1+πT/2}(2T+2)^{⌈T⌉+1}), `norm_Gamma_le_G3` (explicit, with δ) | Matches. The δ ≥ p^{-O(1)} from Liouville's inequality is not formalized. → L8. "Γ ≥ 0.88 on (0,∞)" is not formalized, but `realGamma_ge_exp_neg_one` gives Γ ≥ 1/e on (0,∞) at once (Γ(x) = Γ(x+1)/x ≥ Γ(x+1) for x < 1), which is all the proof needs. |
| A.9 heights | Mathlib `Height.mulHeight₁` (**relative**, not normalized by degree), `mulHeight₁_mul_le`, `mulHeight₁_add_le`, `mulHeight₁_inv`, `natDenominator_le_mulHeight₁`, `NumberField.prod_abs_eq_one` | Enough for Liouville (L8). The paper's H is absolute: H_paper = (mulHeight₁)^{1/[K:ℚ]}. |
| A.10 B_n(b/N) = −nN^{1−n}L(1−n, 1_{b+Nℤ}) | `bernoulli_eq_LFunction(_val)` | n ≥ 2 and 1 ≤ b ≤ N (the paper uses n ≥ 1, which is trivial to add). The denominator and size bounds are not formalized, but Mathlib has `Bernoulli.vonStaudt_clausen`, `primorial_le_four_pow`, `hasSum_zeta_nat`. → L7. |
| A.12 growth of the damped series | `norm_inv_Gamma_le_reflect`, `summable_pow_mul_Gamma(_sq)_div_factorial`, `hasSum_dualTerm_damped` | Matches the convergence statements (r < 1). |

---

## 2. Paragraph-by-paragraph classification

(a) = already formalized; (b) = pure mathematics, formalizable (lemma ids refer to §3); (c) = algorithmic/model content that stays narrative.

| Lines | Paragraph | Content | Class | Formal content / action |
|---|---|---|---|---|
| 3737–3749 | intro | disclaimer | – | rewrite (§5) |
| 3754–3757 | A.1 BS setup | recurrence ↔ product of [[A,0],[B,q]] (checked: correct with X̃_n = Q_nX_n, s̃_n = Q_{n+1}s_n) | (c), algebra (b) | narrative; the matrix identity is trivial |
| 3757–3759 | A.1 BS cost | levels O(p log p) bits; regularity ⇒ O(𝖬(p) log²p) | (a)+(b) | `treeCost_le` (scalar). → **L2** (matrices/monoid) + **L3** (regularity algebra) |
| 3759–3762 | A.1 BS scope | list of series it applies to | (c) | keep one sentence |
| 3764–3766 | A.1 BB recurrence, radius | Taylor recurrence, convergence for \|c−c₀\| < \|c₀\| | (a) | `taylor_rec_iff`, `taylor_rec_summable` |
| 3766–3771 | A.1 BB steps and cost | O(p/2^j) terms of O(2^j + log p) bits; cost sum | (a)+(c) | `bitBurst_cost_le`; the choice of c_j is narrative |
| 3772–3773 | A.1 BB constants | "depend on … a priori bound 2^{O(p)} on \|Y\|" | (b) | replace by **L1** (no a-priori disk bound needed); issue 13 |
| 3776–3780 | A.2 reduction | Lemma `lem:reduction`, twists, parity | (a)/(c) | `zetaTail_eq_sum_iteratedDeriv`, twisted splittings; narrative |
| 3780–3789 | A.2 monodromy | f_{σ,j} satisfies (H) | (b) but needs ODE monodromy and Fuchs's criterion (not in Mathlib) | **move to main text** as a lemma after Definition `def:regular` (it is a property of 𝓡_Q̄, not of the cost). Lean takes it as `FrobeniusData` (cf. `FuchsianAddClosed`) |
| 3790–3793 | A.2 WLOG χ = 1, u₀ = r² | | (c) | keep 2 lines; note s ↦ s+δ for odd χ (issue 18) |
| 3795–3802 | A.3 truncation | (eq:counts) | (a) partly | `Truncation.lean`; uniform and all-s version **L4 + L12**. Move (eq:counts) to the main text (it is cited at l. 1467) |
| 3805–3817 | A.4 eq:Ik | the double-series form of I_k | (b) | **L11** (identity); keep the display, since it is the algorithm |
| 3818–3821 | A.4 recurrences | factor out 1/Γ(s/2+1); P-recursive | (c) + issue 2 | use the j₁-device of A.9 (l. 3977–3981) here too |
| 3821–3822 | A.4 term bound | terms ≤ \|a_n\|κ^{-n/2}e^x; O(p) terms | (b) | **L5** (inner sums) + GeomBounded ⇒ N = O(p) |
| 3822–3825 | A.4 other values | A₀(1/κ), k^{-s}, Q needed to 2^{-p}\|k^s\| | (c) | narrative (1 sentence) |
| 3828–3832 | A.5 series | P(a,y) series for all a | (a) | `hasSum_gammaPTerm`, `gammaQ_neg_nat` |
| 3833–3835 | A.5 counts/guard bits | grow to i≈y, then geometric | (a)+(b) | `norm_tail_gammaPTerm_le`; max term → **L5′** |
| 3835–3838 | A.5 1/Γ(a) | Γ = γ(a,N) + Γ(a,N) | (a)+(b) | `Gamma_eq_lower_add_upper`; upper-tail bound → **L5″**; E₁ needs γ (issue 5) |
| 3838–3841 | A.5 jets, Re a ≤ 0 | | (c) | narrative |
| 3844–3850 | A.6 system | J_m as a component of Y; two blocks | (a) | `dual_system` (real c) |
| 3850–3855 | A.6 normalization | Γ(σ₀+m₂), Ẽ = Eu₀^{1−t}; B₀,B₁ polynomial in s | (c) + issue 1 | add the b-free augmentation (**L10**) |
| 3857–3862 | A.6 startvals | (eq:startvals), (eq:Drec), D_a = α_aD_{a*} + β_aE | (a)+(b) | `momentD_rec`; **L6** (α_a explicit, β exists) |
| 3864–3869 | A.6 cancellation | Σ\|g_jα\| ≤ e^{2R√c₀}c₀^{O(1)} | (b) | **L6** (Σ xⁿ/(n!)² ≤ e^{2√x} + coefficient bounds). Checked numerically: ratio 1.6e15 vs e^{2R√c₀} = 2.4e16 |
| 3871–3875 | A.6 cost of a dual term | error amplification, a-priori bound | (b) + issue 3 | **L1** + choose c₀ within relative distance p^{-A} as in A.9 |
| 3878–3883 | A.7 main term | series in n; P-values by recurrence; pole term | (b)+(c) + issue 6 | term bounds from **L4/L5**; the P-part rewritten as a positive double series |
| 3886–3893 | A.8 jets | computing over K[ε]/(ε^{j+1}) | (c) | narrative (keep, ~6 lines) |
| 3894–3897 | A.8 log-moments | IBP with (log u)^i | (b) | **L9** (numerically verified) |
| 3898–3900 | A.8 base values | ∂_a^i D_a via (eq:Drec) | (c) | narrative |
| 3902–3907 | proof of thm:complexity | assembly | (c) | becomes "special case of thm:uniform" (1 sentence) |
| 3910–3916 | A.9 heights | bit size, conjugates, Liouville | (b) | Mathlib heights + **L8** |
| 3918–3929 | A.9 frame (a)–(d) | | (c) | keep, as the definition of a "certificate" (§4) |
| 3931–3947 | (G1)–(G3) | | (a) | cite `norm_inv_Gamma_le_G1`, `norm_inv_Gamma_le_G2`, `norm_Gamma_le_G3` + L8; **delete the proofs** |
| 3949–3959 | A.9 reduction | λ_i, χ indicators, y_i(k) for k < k₀ | (c) (+ small (b)) | keep, shorter |
| 3961–3975 | A.9 truncation | kernel bounds near/far; I_k, J_m bounds; Cauchy in s | (b) | **L4** (whole paragraph replaced by a citation) |
| 3977–3985 | A.9 k-terms | j₁ device; Σx^j/\|Γ\| ≤ 2^{O(p)}x^Se^x | (b)+(c) | **L5**; keep the j₁ device (algorithmic, 2 lines) |
| 3987–3992 | A.9 incomplete gamma | uniform series; 1/Γ(w) | (b) | **L5′, L5″**; issue 7 |
| 3994–4006 | A.9 dual terms: system, ρ = cp^{-A}, Gronwall, steps | | (b)+(c) + issue 1 | **L1** replaces Gronwall + Cauchy; **L10** fixes the b entries |
| 4006–4018 | A.9 starting values | base exponents, α going up/down, Liouville | (b)+(c) | **L6** + L8; the choice of a* is narrative |
| 4020–4023 | A.9 main term and jets | | (b) | L4-type term bound; units in K[ε] (trivial algebra) |
| 4027–4037 | A.9 memory | blocking, depth-first | (c) (+ small (b)) | keep (shortened); error of the running product: `error_propagation_linear`; issue 9 |
| 4039–4042 | A.9 large \|s₀\| | P = ⌈p log₂p⌉ | (b) trivial | keep (4 lines) |
| 4045–4068 | last statement of thm:uniform | complex c_n, Gaussian rational starting points | (c)+(b) | merge with A.11; **L1** |
| 4070–4078 | remarks | | – | keep |
| 4081–4097 | Cor. bernoulli | reduction to L_1; denominators; size; exactness | (a)+(b) | `bernoulli_eq_LFunction` + **L7** |
| 4099–4111 | Cor. egf, values | partial fractions in eᵗ; Li_{−n−l} | (b) (Mathlib: `expZeta`/Hurwitz) | low priority; narrative |
| 4112–4119 | Cor. egf, denominators | Hurwitz-series ring d^{−n}O_K | (b) | low priority (O_K bookkeeping) |
| 4122–4151 | A.11 thm:geometric(2) | | (c)+(b) + issue 4 | merge with the uniform case; **L1** |
| 4153–4186 | A.12 stretched | sketch | (c)/(b) | keep as a sketch; issue 12 |

---

## 3. Proposed formal lemmas (Lean 4 / Mathlib)

All statements are in `plan/AppAStatements.lean` (namespace `ZetaF.AppA`), and that file
typechecks against the current project. Matrix norms are `∑ i, ∑ j, ‖B i j‖` as in `TaylorRec.lean`, and vectors carry
the sup norm. The Lean line counts are estimates.

### L1. Taylor step, explicit (**PROVED**, `ZetaF/Bounds/TaylorStep.lean`)
```lean
theorem taylor_step_bound {D : ℕ} {c₀ h : ℂ} (B₀ B₁ : Matrix (Fin D) (Fin D) ℂ)
    (Y : ℕ → Fin D → ℂ)
    (hrec : ∀ n i, c₀ * (n + 1) * Y (n + 1) i =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * Y n j - n * Y n i +
        ∑ j, B₁ i j * (if n = 0 then 0 else Y (n - 1) j))
    (hc₀ : c₀ ≠ 0) {θ : ℝ}
    (h0 : ‖h‖ * (∑ i, ∑ j, ‖B₀ i j + c₀ * B₁ i j‖) ≤ θ * ‖c₀‖)
    (h1 : ‖h‖ * (∑ i, ∑ j, ‖B₁ i j‖) ≤ θ) (h2 : ‖h‖ ≤ θ * ‖c₀‖) (l : ℕ) :
    ‖h ^ l • Y l‖ ≤ (2 * θ) ^ l * ‖Y 0‖
```
* **Proof idea.** Scaling the recurrence gives ‖w_{n+1}‖ ≤ θ‖w_n‖ + θ²‖w_{n−1}‖/(n+1), with w_n = hⁿY_n. Then
  induction. This is a majorant argument and needs no analyticity. Numerically checked on 300 random systems, with
  ratio ≤ 1 (`taylor.py`).
* **Corollaries (~60 lines, routine).**
  * `taylor_step_tail` (**proved**): for θ < ½ the tail after L terms is ≤ (2θ)^L‖Y₀‖/(1−2θ).
  * Transition-map norm ≤ 1/(1−2θ).
  * With `error_propagation_linear`, a chain with Σθ_j ≤ ¼ amplifies errors by ≤ e.
* **What it replaces.**
  * The a-priori-bound and constants sentence in A.1 (l. 3772–3773).
  * "Cost of a dual term" (l. 3871–3875).
  * The Gronwall and Cauchy-estimate sentences of A.9 (l. 4000–4006).
  * The disk bound in A.11 (l. 4147).
  * l. 4063–4064.
* **How it applies in A.9's regime.** Take |c − c₀| ≤ ρ/2 with ρ = cp^{-A}, A = A₀+2, c = O(p). Then
  θ = O(p^{-1}) for the first stage (so even O(p/log p) terms suffice), and θ_i ≤ p^A2^{-b_i} ≤ 2^{-b_i/2} for the
  later stages.
* **Remaining narrative fact.** The convergent Taylor series of the system at c_j continues the solution along the
  segment. This is uniqueness for linear analytic ODEs; taylor_rec_iff gives the formal side.

### L2. Product trees over a monoid with quasi-subadditive size (~150 + 40 lines)
```lean
def nodeL {α} [Monoid α] (x : ℕ → α) (j i : ℕ) : α := ((List.range' (i * 2 ^ j) (2 ^ j)).map x).prod
def treeCostL {α} [Monoid α] (size : α → ℕ) (M : ℕ → ℕ) (x : ℕ → α) (d : ℕ) : ℕ :=
  ∑ j ∈ range d, ∑ i ∈ range (2 ^ (d - 1 - j)), M (size (nodeL x j (2*i)) + size (nodeL x j (2*i+1)))
theorem treeCostL_le {α} [Monoid α] (size : α → ℕ) (κ : ℕ)
    (hsize : ∀ a b, size (a * b) ≤ size a + size b + κ)
    {M : ℕ → ℕ} (hmono : Monotone M) (hsup : ∀ a b, M a + M b ≤ M (a + b)) (x : ℕ → α) (d : ℕ) :
    treeCostL size M x d ≤ d * M (∑ k ∈ range (2 ^ d), size (x k) + κ * 2 ^ d)
def matSize {D} (A : Matrix (Fin D) (Fin D) ℤ) : ℕ := univ.sup fun ij => Nat.size (A ij.1 ij.2).natAbs
theorem matSize_mul_le {D} (A B : Matrix (Fin D) (Fin D) ℤ) :
    matSize (A * B) ≤ matSize A + matSize B + Nat.size D
```
* **Proof.** Copy `sum_size_level_le`/`treeCost_le` with ordered `List.prod` (`List.prod_append` replaces
  `prod_Ico_consecutive`).
* **Number fields.** Take α = matrices over ℤ in coordinates on an integral basis. The multiplication table has fixed
  height, so κ = O(1).
* **What it replaces.** The "by the regularity of 𝖬" step of A.1 for the matrices the paper actually multiplies.

### L3. Regularity algebra for 𝖬 (~80 lines)
```lean
theorem regular_cost {M : ℕ → ℕ} (hdiv : ∀ a b, 0 < a → a ≤ b → M a * b ≤ M b * a)
    {C : ℕ} (hreg : ∀ n ≥ 4, M (n * Nat.log 2 n) ≤ C * M n * Nat.log 2 n) (A : ℕ) :
    ∃ C' : ℕ, ∀ p ≥ 4, (Nat.log 2 p + 1) * M (A * p * (Nat.log 2 p + 1)) ≤ C' * M p * (Nat.log 2 p) ^ 2
```
* **Key step.** With g(n) = 𝖬(n)/n nondecreasing and 2n ≤ n log₂n, we get g(2n) ≤ g(n log n) ≤ Cg(n), so
  𝖬(An) = O(𝖬(n)). The paper uses this implicitly everywhere (it is not literally among the two stated conditions,
  l. 1390–1391, but it follows from them).
* **What it replaces.** All "by the regularity of 𝖬" and "𝖬(p log p) = O(𝖬(p) log p)" steps, e.g. l. 3759, 4042, 4094.

### L4. Uniform kernel and truncation bounds (~350–450 lines)
```lean
theorem norm_kernel_le_far {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ u : ℝ, u₀ ≤ u →
      ‖kernel a s u‖ ≤ Real.exp (A * S * Real.log S) * (1 + u) ^ 2 * Real.exp (R ^ 2 * u)
theorem norm_kernel_le_near … ∀ u, 0 < u → u ≤ u₀ →
      ‖kernel a s u‖ ≤ Real.exp (A * S * Real.log S) * u ^ (-(S / 2) - 1)
theorem norm_kTerm_le_uniform … {k₀ : ℕ} (hk₀ : R < k₀) : ∃ A, ∀ S ≥ 2, ∀ s, ‖s‖ ≤ S → ∀ k ≥ k₀,
      ‖kTerm (kernel a s) u₀ k‖ ≤ Real.exp (A * S * Real.log S) * Real.exp (-(((k:ℝ)^2 - R^2) * u₀))
theorem norm_dualTerm_le_uniform … ∀ m ≥ 1,
      ‖dualTerm (kernel a s) u₀ m‖ ≤ Real.exp (A * S * Real.log S) * Real.exp (-(π^2 * m^2 / (2 * u₀)))
```
* **Proof.** Split n at ⌈2S⌉ and use (G2) (`norm_inv_Gamma_le_G2`) below and (G1) above. A lemma
  Σ_m y^m/Γ(m+σ) ≤ C(1+y)e^y for σ ∈ [½, 3/2] is needed; it is not in Mathlib, but follows from
  `rpow_le_exp_mul_Gamma` or log-convexity (`Real.convexOn_log_Gamma`). Then integrate, using
  max_u u^{-A}e^{-b/u} = (A/(eb))^A. Twisted variant: replace π² by π²/q².
* **What it replaces.** A.3 and A.9 "Truncation" (l. 3961–3975). With S ↦ S+1 and Cauchy's estimate it also bounds the
  Laurent/Taylor coefficients (l. 3974–3975).
* **Mismatch it fixes.** The current `norm_tsum_dualTerm_tail_le` is vacuous for Re s ≤ 1−n₀.

### L5. Sums of x^j/Γ(σ+j+1): k-term inner sums and incomplete gamma (~200 lines)
```lean
theorem sum_pow_mul_norm_inv_Gamma_le :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ σ : ℂ, ‖σ‖ ≤ S → ∀ x : ℝ, 0 ≤ x →
      Summable (fun j : ℕ => x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖) ∧
      ∑' j, x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ ≤ Real.exp (A * S * Real.log S) * (1 + x) ^ S * Real.exp x
-- L5′ (uniform tail; strengthens norm_tail_gammaPTerm_le with an explicit first-term bound)
theorem norm_gammaPTerm_tail_uniform :
    ∃ A : ℝ, ∀ S ≥ 2, ∀ a : ℂ, ‖a‖ ≤ S → ∀ y > 0, ∀ N : ℕ, 2 * y + 2 * S ≤ N →
      ‖∑' i, gammaPTerm a y (i + N)‖ ≤ Real.exp (A * S * Real.log S) * (1 + y) ^ S * (1/2) ^ N
-- L5″: ‖upperGamma w N‖ ≤ 2 N^{Re w - 1} e^{-N} for Re w ≤ N/2 + 1  (gives the 1/Γ(w) paragraph)
```
* **What it replaces.** A.4 l. 3821–3822, A.5 l. 3833–3835, A.9 l. 3981–3983 and l. 3987–3992. Fixed data is S = O(1).

### L6. Starting values (~200–300 lines; generalizes `Khinchin/StartVals.lean`)
```lean
noncomputable def alphaD (a : ℂ) (c : ℝ) (n : ℕ) : ℂ := (-(c : ℂ)) ^ n / ∏ i ∈ range n, (a + 1 + i)
theorem momentD_add_nat_eq {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (a : ℂ) (ha : ∀ i : ℕ, a + 1 + i ≠ 0) :
    ∃ β : ℕ → ℂ, ∀ n : ℕ, momentD u₀ c (a + n) = alphaD a c n * momentD u₀ c a + β n * (rexp (-(c / u₀)) : ℂ)
theorem sum_pow_div_factorial_sq_le {x : ℝ} (hx : 0 ≤ x) :
    ∑' n : ℕ, x ^ n / ((n.factorial : ℝ) ^ 2) ≤ Real.exp (2 * √x)
-- plus: Σ_j ‖g_j‖‖alphaD a* c₀ j‖ ≤ e^{A S log S}·e^{2R√c₀}·(1+c₀)^{A S}, from |g_j| ≤ C R^{2j}/|Γ(j+σ₀)| and (G1)–(G3)
```
* **What it replaces.** A.6 l. 3864–3869 and A.9 l. 4006–4015 (except the choice of a*, which is algorithmic).
* **Uses** `momentD_rec` (already for complex a).

### L7. Exact recovery of B_n(x) (~150 lines; Mathlib: `Bernoulli.vonStaudt_clausen`, `primorial_le_four_pow`, `hasSum_zeta_nat`)
```lean
theorem den_bernoulli_eval (n b f : ℕ) (hf : 0 < f) :
    ∃ z : ℤ, ((f : ℚ) ^ n * (primorial (n + 1) : ℚ)) * (Polynomial.bernoulli n).eval ((b : ℚ) / f) = z
theorem abs_bernoulli_eval_le (n : ℕ) {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(((Polynomial.bernoulli n).eval x : ℚ) : ℝ)| ≤ 4 * Real.exp 1 * n.factorial
theorem rat_eq_of_approx {q : ℚ} {D : ℕ} (hD : 0 < D) (hq : ∃ z : ℤ, (D : ℚ) * q = z)
    {y : ℝ} (hy : |y - q| < 1 / (2 * D)) : q = (round ((D : ℝ) * y) : ℚ) / D
```
* **What it replaces.** Together with `bernoulli_eq_LFunction`, the whole arithmetic of the proof of Corollary
  `cor:bernoulli` (l. 4082–4091). What is left is "apply Theorem `thm:uniform` with p = n log₂n + O(n)".
* **Analogue for egf** (Hurwitz-series ring d^{-n}O_K, l. 4112–4118): possible (~300 lines over O_K, ~120 over ℚ);
  low priority.

### L8. Liouville's inequality in Mathlib's height normalization (~50–100 lines)
```lean
theorem inv_mulHeight₁_le_place {K} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    (v : NumberField.InfinitePlace K) : 1 / Height.mulHeight₁ x ≤ v x
```
* **Proof.** If v(x) < 1, the product formula (`NumberField.prod_abs_eq_one`) gives
  v(x)^{m_v} = ∏_{w≠v}w(x)^{-m_w} ≥ 1/mulHeight₁(x), and m_v ≥ 1.
* **What it gives.** The δ of `norm_Gamma_le_G3`, and the small divisors |s₀+σ+n|, |a*+n| ≥ p^{-O(1)}
  (with `mulHeight₁_add_le`).

### L9. Log-moments (A.8) (~80 lines, a copy of `dualMoment_ibp`)
```lean
noncomputable def dualMomentLog (u₀ c : ℝ) (t : ℂ) (i : ℕ) (g : ℝ → ℂ) : ℂ :=
  dualMoment u₀ c t fun u => (Real.log u : ℂ) ^ i * g u
theorem dualMomentLog_ibp … :
    c * dualMomentLog u₀ c (t + 1) (i + 1) g =
      E * u₀ ^ (1 - t) * (log u₀) ^ (i + 1) * g u₀ - (1 - t) * dualMomentLog u₀ c t (i + 1) g
      - dualMomentLog u₀ c t (i + 1) (fun u => u * g' u) - (i + 1) * dualMomentLog u₀ c t i g
```

### L10. b-free form of the dual system (fixes issue 1) (~150 lines on top of `DualSystem.lean`)
* **Statement.** Augment Y by the products b_{i,k}C_{t−i′}(c) and b_{i,k}E(c) (for every coordinate (i,k) of b and
  every C-index i′). The augmented vector satisfies cŶ′ = (B̂₀ + cB̂₁)Ŷ, and the entries of B̂₀ and B̂₁ do not involve b:
  they are polynomials in s of bounded degree, with fixed coefficients.
* **Proof.** The C-block and E satisfy b-independent equations, and in the W-rows Σ_i b_iC_{t−i} becomes a sum of
  components with coefficient 1.
* **Alternative for the paper text.** By linearity, run the bit-burst with unit inhomogeneities and combine the results
  with the Θ(p)-bit numbers b_{i,k} at the end.

### L11. The double-series form (eq:Ik) (~150 lines)
* **Statement.** From `hasSum_kTerm_gammaQ` and `gammaQ_add_nat`, by splitting n by parity and Fubini, with
  A₀(1/κ), A₁(1/κ) as `tsum`s:
  I_k(s) = k^{-s}(Q(s/2,x)A₀(1/κ) + Q((s+1)/2,x)A₁(1/κ)/k) + e^{-x}u₀^{s/2}Σ_m a_{2m}κ^{-m}Σ_{j<m}x^j/Γ(s/2+j+1) + (odd part).
* **Status.** Numerically verified to 3e-42.

### L12. Truncation counts with constants and period q (~60 lines)
* **Statement.** kCount (p + ⌈log₂(C/(1−e^{-u₀}))⌉) makes the k-tail ≤ 2^{-p}; similarly for the dual side, with π²/q².
* **Proof.** Combine L4 with `exp_kCount_le` and `exp_mCount_le`.
* **What it replaces.** The "≈" in (eq:counts) and the "reach 2^{-O(p)}" wording (l. 3974).

Not proposed: Gronwall (L1 makes it unnecessary; Mathlib has `norm_le_gronwallBound_of_norm_deriv_right_le` if
wanted), the depth-first stack bound of the memory paragraph (formalizable, ~80 lines, but low value), and the monodromy
lemma of A.2 (needs ODE theory absent from Mathlib).

---

## 4. The cost-model interface (stays narrative, stated as assumptions)

State once, at the start of the new A.1:

* **(M)** 𝖬(n)/n is nondecreasing and 𝖬(n log n) = O(𝖬(n) log n). Consequences (L3): 𝖬 is superadditive,
  𝖬(An) = O_A(𝖬(n)), and (log N)𝖬(N log N) = O(𝖬(N) log²N). Multiplying a- and b-bit integers costs 𝖬(a+b), in space
  O(a+b) (FFT-type algorithms; needed only for the memory bound).
* **(K)** A fixed number field K is represented by integer coordinates on an integral basis plus a denominator. A
  field operation costs O(1) integer operations, and sizes are quasi-subadditive (`matSize_mul_le`, L2). A K-element
  of height H has O(log H) bits (Mathlib: `natDenominator_le_mulHeight₁` and coordinate bounds).
* **(BS) Binary splitting [HP98].** The ordered product of N matrices of fixed dimension over O_K, with b-bit entries,
  is computed by a balanced tree in O(Σ over tree nodes of 𝖬(node sizes)). The combinatorial bound
  O(𝖬(N(b+O(1))) log N) is L2. Depth-first evaluation needs O(Nb) bits, or O(p + b) with blocking.
* **(A) Approximate arithmetic.** Reals and complexes are carried as dyadic approximations with absolute error bounds.
  One operation at precision q costs O(𝖬(q)). Error propagation through linear steps is `error_propagation_linear`.
* **(E) Elementary constants.** π, Euler's γ, exp and log at points with O(log p) bits (or rational points with
  |x| ≤ p^{O(1)}) cost O(𝖬(p)log²p) each. These are classical consequences of (BS) for hypergeometric series.

**Lemma A.1 (certified series).** Suppose the series has terms t_n = λ(T_{n−1}⋯T₀v), with T_n over O_K, and:
(i) N terms are summed; (ii) the entries of T_n have ≤ b bits for n < N; (iii) the tail after N is ≤ 2^{-p};
(iv) all normalized partial products are ≤ 2^G. Normalized partial products means the entries of
(q₀⋯q_{n−1})^{-1}T_{n−1}⋯T₀, i.e. a *fundamental matrix* of the recurrence, not only the wanted solution (issue 9).
Then Σt_n is computed with error 2^{-p+1} in O(𝖬(Nb) log N + 𝖬(p+G)) bit operations. With blocking, the space is
O(p + G + b) bits whenever Nb = O(p log p).
*(Proof: narrative from (BS), (A) and `error_propagation_linear`; ~6 lines.)*

**Lemma A.2 (bit-burst).** Assume:
* cY′ = (B₀ + cB₁)Y, with entries of B₀ and B₁ having O(log p) bits and ‖B₀‖ + ‖B₁‖ ≤ p^{A₀};
* c₀ ≠ 0 has O(log p) bits, and |c − c₀| ≤ |c|p^{-A₀−2}/2;
* c is computable to precision q in O(𝖬(q)log²q);
* ‖Y(c₀)‖ ≤ 2^G.

Then Y(c) is computed with error ≤ 2^{-p}‖Y(c₀)‖ (given Y(c₀) to error 2^{-p-3}‖Y(c₀)‖) in O(𝖬(p + G)log²p).
*(Proof: L1 for each stage (θ₀ = O(1/p), θ_i ≤ 2^{-b_i/2}); `error_propagation_linear` with ∏(1−2θ_i)^{-1} ≤ e;
`bitBurst_cost_le` for the cost; Lemma A.1 for each stage.)*

With these two lemmas the per-piece work is **only** a certificate (N, b, G), and every certificate entry is a formal
lemma:

| piece (number) | N | b | G | source |
|---|---|---|---|---|
| number of k- and dual terms: O(√p) | – | – | – | L4 + L12 |
| I_k double sums (eq:Ik) after the j₁ device, O(√p) | O(p) | O(log p) | O(p) | L11, L4, L5 |
| A₀(1/κ), A₁(1/κ), O(√p) | O(p) | O(log p) | O(1) | GeomBounded |
| P(a,y), Q(a,y), y = k²u₀ = O(p), O(√p) | O(p) | O(log p) | O(p) | `hasSum_gammaPTerm`, L5′ |
| 1/Γ(w), O(1) values (+ γ if a class is integral) | O(p) | O(log p) | O(p) | `Gamma_eq_lower_add_upper`, L5″, G1, (E) |
| starting values Y(c₀), O(√p) | O(p) | O(log p) | O(p) | L6, L8 |
| base values D_{a*}(c₀), O(√p) | O(p) | O(log p) | O(p) | L5′, G3 + L8 |
| bit-burst stages, O(√p)·O(log p) | O(p/b_i) | O(b_i) | amplification ≤ e | L1, `bitBurst_cost_le` |
| main term M | O(p) | O(log p) | O(p) | L4-type term bound |
| k^{-s}, log k, O(√p) | – | – | O(p) | (E), \|k^{-s₀}\| ≤ k^S = 2^{O(p)} |

---

## 5. Proposed new structure of Appendix A, and narrative outline

Target: A.1–A.9 shrink from ~325 .tex lines to ~150–170, with no chains of inequalities left in the text; every
estimate is a citation to a named lemma with its Lean name. A.10–A.12 shrink modestly.

**A.0 (intro, replaces l. 3739–3749).** "This appendix proves Theorem `thm:uniform`, of which Theorem
`thm:complexity` is the special case of fixed data, together with Corollaries `cor:bernoulli`/`cor:egf` and
Theorem `thm:geometric`(2). We separate (i) a cost model, stated as assumptions (A.1); (ii) analytic estimates, all
formalized in Lean (A.2, with names); (iii) the description of the algorithm, the choice of parameters and the
assembly (A.3–A.5)." Drop "LLM-generated and unedited"; say instead which parts are machine-checked.

**A.1 Cost model (~25 lines).** (M), (K), (BS), (A), (E) and Lemmas A.1 and A.2 as in §4.
* **Delete:** the binary-splitting cost argument (l. 3757–3759) and the bit-burst cost and constants argument
  (l. 3766–3773).
* **Replace with:** L2, L3, `bitBurst_cost_le` and L1.
* **Keep:** the matrix form [[A,0],[B,q]] and the bit-burst recurrence (one display each).

**A.2 Analytic estimates (~35 lines: statements only, no proofs).**
* Lemma A.3 (Γ): (G1)–(G3) and Γ ≥ 1/e → `norm_inv_Gamma_le_G1`, `norm_Gamma_le_Gamma_re`, `norm_inv_Gamma_le_G2`,
  `norm_Gamma_le_G3`, L8. This deletes l. 3931–3947 except the statements.
* Lemma A.4 (kernel; uniform in |s| ≤ S): L4. This deletes A.3 (l. 3795–3802; move (eq:counts) to §5 of the main
  text) and l. 3961–3975.
* Lemma A.5 (series in x^j/Γ(σ+j+1)): L5, L5′, L5″. This deletes l. 3821–3822, 3833–3835, 3981–3983 and 3987–3992.
* Lemma A.6 (starting values): L6. This deletes l. 3864–3869 and 4010–4015.
* Lemma A.7 (Taylor step): L1 (proved). This deletes l. 3871–3875 and 4000–4006.
* Lemma A.8 (identities): (eq:Ik) L11, log-moments L9, the dual system `dual_system` + L10.

**A.3 The algorithm (~45 lines; genuinely algorithmic, stays narrative).** One paragraph per piece, describing *what*
is computed, not *how much it costs*:
1. **Reduction.** Lemma `lem:reduction`, Remark `rem:twist`, χ as indicators, y_i(k) for k < k₀ by analytic
   continuation (l. 3949–3959, condensed). Move the monodromy argument (l. 3780–3789) to the main text as a lemma
   about 𝓡_Q̄.
2. **k-terms.**
   * (eq:Ik), with 1/Γ(s/2+j₁+1) factored out, j₁ the least index with Re(s/2+j₁+1) ≥ ½. This is the A.9 device, now
     used for fixed s as well, which fixes issue 2.
   * Incomplete gamma values from the P-series. For the integral class, E₁(y) = −γ − log y + Ein(y) (issue 5).
3. **Dual terms.**
   * The normalization (Γ(σ₀+m₂), Ẽ), plus the b-free augmentation L10 (issue 1).
   * The starting point c₀ ≤ c with |c−c₀| ≤ cp^{-A}/2 in all cases, i.e. A.9's choice also for fixed data, which
     removes A.6's unproved growth claim.
   * Base exponents a*, going up and down via (eq:Drec).
4. **Main term.**
   * The series in n.
   * The P-part for k < k₀ written as e^{-x}u₀^{s/2}Σ_n a_nu₀^{n/2}Σ_i x^i/Γ((s+n)/2+i+1). This removes k^{-n}
     (issue 6, cf. Remark `rem:practical`(5)).
   * The explicit pole term.
5. **Jets.** K[ε]/(ε^{j+1}), units, and the factors 1/Γ(σ₀+ε), u₀^{ε/2}, k^{-ε} (A.8 minus the display, which goes
   to A.2).

**A.4 Proof of Theorem `thm:uniform` (~30 lines).**
* "By A.3 the result is a combination of the pieces with O(p)-bit coefficients; by Lemma A.4 there are O(√p) of them.
  The table (§4) gives a certificate for each, by Lemmas A.3–A.8; Lemmas A.1–A.2 give O(𝖬(p)log²p) per piece."
* Then memory (l. 4027–4037), shortened to ~8 lines and with the fundamental-matrix remark (issue 9), and large |s₀|
  (l. 4039–4042, unchanged).
* Then: "Theorem `thm:complexity` is the case of fixed data." This deletes the proof at l. 3902–3907 and A.4–A.8 as
  separate cost analyses.

**A.5 Geometric factors (~25 lines).** Merge A.11 (l. 4122–4151) with "Proof of the last statement"
(l. 4045–4068). These two currently repeat each other.
* Complex dual points c_n.
* Gaussian-rational starting points within relative distance p^{-A}, and L1. This removes the ¾-disk (issue 4).
* The O(1) values of n with Re c_n < 1, via the D_a series.
* The k-side weights C_k, S_k.

**A.6 Sequences (~30 lines).**
* Corollary `cor:bernoulli`: `bernoulli_eq_LFunction` + L7. Five lines of text remain.
* Corollary `cor:egf`: unchanged (optionally the ℚ case of the denominator lemma).

**A.7 Stretched exponentials (sketch).** Keep. Add the two caveats of issue 12.

What disappears entirely: A.3–A.8 as stand-alone fixed-data analyses (~110 lines); the proofs of (G1)–(G3) (~15); the
truncation, k-term, incomplete-gamma and dual-term estimate paragraphs of A.9 (~60); the duplicated geometric
paragraph (~15). What is new: the cost-model block (~25), the lemma list (~35) and the certificate table (~15).

---

## 6. Issues found (line numbers in zetaF.tex)

### 1. (Gap: invalidates claim (c) as written) l. 3994–3996, also l. 3853–3854
* **Claim.** "After the normalization … the entries of B₀ and B₁ … are polynomials in s of bounded degree with fixed
  coefficients … therefore have O(log p) bits."
* **Problem.** B₀ contains the inhomogeneity b of Lemma `lem:kernelhol` (it multiplies the C_{t−i}-columns in the
  W-rows of Proposition `prop:dual`). After multiplying by Γ(σ₀+m₂), its entries are Γ(σ₀+m₂)/Γ(σ₀+m−r)·(…) =
  (σ₀+m−r)_{m₂−m+r}·(…). These are polynomials of degree m₂ − m + r = O(S) (m₂ is the least integer with
  Re(σ₀+m₂) ≥ ½, so m₂ ≈ −Re s₀/2). For s₀ with large negative real part they have Θ(S log S) = Θ(p) bits.
* **Numerical check.** f = 1/(1−x), where ϑG = (1−σ₀+u)G + 1/Γ(σ₀−1); this ODE was verified to 6e-39. For
  s₀ = −2N+½ (H(s₀) ≈ 4N):

  | s₀ | log₂\|b\| | S log₂S |
  |---|---|---|
  | −19.5 | 22 | 95 |
  | −199.5 | 528 | 1542 |
  | −1999.5 | 8535 | 21950 |
  | −19999.5 | 118466 | 285778 |

  So log₂|b| ≈ 0.4·S log₂S. In the regime |s₀| ≍ cp/log p, B₀ has Θ(p)-bit entries. The Taylor recurrence of
  Lemma A.1 then has Nb = Θ(p²), and binary splitting is no longer quasilinear.
* **Fix.** L10 (make B₀ independent of b by adding the products b_{i,k}C, b_{i,k}E as components), or linearity in b.
  Either is one sentence in the text. (In A.6, for fixed s, there is no problem.)

### 2. (Gap) l. 3818–3820 (and l. 3887–3889)
* **Problem.** "After factoring out 1/Γ(s/2+1) and 1/Γ((s+1)/2+1) the inner sums satisfy first-order recurrences."
  If s₀/2 + j + 1 = 0 for some j ≥ 0 (s₀ ∈ {−2,−4,…}), the factor is 0. The recurrence t_{j+1}(s/2+j+1) = xt_j then
  propagates 0, and over K[ε] it divides by a non-unit. The same holds for the odd part at s₀ ∈ {−3,−5,…}.
* **Fix.** Use the j₁-device of l. 3977–3981 already for fixed s.

### 3. (Unjustified claim) l. 3871–3874
* **Claims.** "the other solutions … grow at most like e^{O(√c)} along the path, which costs O(√p) guard bits", and
  "|Y(c)| ≤ Ce^{O(1)} on |c−c₀| ≤ ¾c₀".
* **Problem.** No argument is given for either. With |c−c₀| ≤ 2^{-8}c and c = O(p), Gronwall only gives e^{O(c)} =
  2^{O(p)}. That is still enough for the theorem, but the claim as stated is unproved.
* **Fix.** Use A.9's starting point (relative distance p^{-A}) for fixed data as well, and L1. The amplification is
  then O(1), with no disk bound.

### 4. (Unjustified claim) l. 4139 and 4147, Theorem `thm:geometric`(2)
* **Problem.** With |c_n − c′_n| ≤ |c′_n|/4, the disk |c − c′_n| ≤ ¾|c′_n|, on which "|Y| ≤ 2^{O(p)}" is asserted,
  leaves Re c > 0 as soon as |arg c′_n| > arccos(¾) ≈ 41°. This happens for the O(1) values of n with
  |n−α₁| ≲ α₂. Example: z = e^{2πi(0.5+0.3i)}, n = 0 gives arg c₀ = 62°. For c_n on the cut the disk crosses the cut.
* **Why the bound is unproved.** There the moment integrals diverge. The bound has to come from the analytic
  continuation. It is true (finitely many fixed points), but it is not argued.
* **Fix.** As in 3 (L1, short first step). Only ‖Y(c′_n)‖ is then needed, and the series of `thm:geometric` bounds it.

### 5. (Omission) l. 3836–3838, 4008, 4015
* **Problem.** For the integral class of exponents the base value is D₀ = E₁(c₀/u₀). E₁ is not covered by
  "Γ(a) = γ(a,N) + Γ(a,N)" (Γ has a pole at 0). One needs E₁(y) = −γ − log y + Ein(y), hence Euler's γ (Brent–McMillan,
  O(𝖬(p)log²p)), computed once.
* **Fix.** State it. The jets at this class need the Laurent expansion of Γ(−ε/2), which is fine.

### 6. (Numerical instability not addressed) l. 3879–3881
* **Problem.** The values k^{-s-n}P((s+n)/2, k²u₀) (k < k₀, possibly k < R) obtained by the recurrence in n from
  P(s/2,x) amplify the error of the initial value by up to (R/k)^N. This is harmless, since N = O(p/log p) and the
  O(p) guard bits absorb it, but it is not mentioned.
* **Fix (cleaner).** Use P(a,x) = x^ae^{-x}Σ_i x^i/Γ(a+i+1). The P-part becomes
  e^{-x}u₀^{s/2}Σ_n a_n u₀^{n/2}Σ_i x^i/Γ((s+n)/2+i+1), in which k^{-n} has cancelled. Cf. Remark
  `rem:practical`(5), which states the floating-point version of this caveat.

### 7. (Wrong inference, harmless) l. 3992
* **Problem.** "|Γ(w)| ≥ 0.88e^{-πS/2} by (G1)" does not follow from |w| ≤ 3S. (G1) gives
  |Γ(w)| ≥ Γ(Re w)e^{-π|Im w|/2} ≥ 0.88e^{-3πS/2}. Numerically: |Γ(½+29i)| = 4.1e-20 < 0.88e^{-5π} = 1.3e-7 (S = 10).
  The stated bound is true for the w actually used (|Im w| ≤ S/2).
* **Fix.** Write e^{-3πS/2}, or note |Im w| ≤ S/2.

### 8. (Cosmetic) l. 3939
* **Note.** "Γ ≥ 0.88 on (0,∞)" is correct (the minimum is 0.88560 at 1.46163). But Γ ≥ 1/e, which is formalized
  (`realGamma_ge_exp_neg_one` plus Γ(x) = Γ(x+1)/x), suffices.
* **Suggestion.** Use 1/e, to match the Lean proof.

### 9. (Gap in the memory argument) l. 4035–4036
* **Problem.** "The entries of the normalized partial products are the partial sums and terms of the series." This is
  true only for first-order (scalar) recurrences. For matrix recurrences the partial products are a fundamental
  matrix, which contains *all* solutions of the recurrence. So (d) must bound all solutions, not only the wanted one.
* **Why the conclusion survives.** In the cases at hand it holds. For the Taylor stages, L1 bounds all solutions. For
  the a_n-recurrence, all solutions have geometric growth because the operator satisfies (H). The Γ-twists are
  first-order.
* **Fix.** Add this to Lemma A.1 (iv), as in §4.

### 10. (Twist constant) l. 3972–3973, 3997
* **Problem.** With a fixed indicator χ of period q the dual points are π²n²/q². "Re c′ ≥ π²/2" should be ≥ π²/(2q²),
  and b = π²m²/2 ≥ 1 should be b = π²m²/(2q²). The bound max u^{-A}e^{-b/u} = (A/(eb))^A remains 2^{O(p)}.

### 11. (Wording) l. 3974
* **Problem.** "O(√p) terms on each side reach 2^{-O(p)}". What is meant: the tails are ≤ 2^{-p′} with p′ = p + O(p).
  The O(√p) count depends on that O(p) (L12 makes it explicit).

### 12. (Sketch-level gaps) A.12, l. 4168–4175
* **The closure argument.**
  * Proposition `prop:dual`'s closure uses A ∈ K[u]: multiplication by u^i *lowers* the moment index.
  * For the damped kernel the ϑ-system is polynomial in w = u^{-r/2}, so multiplication *raises* the index by r/2.
  * The IBP relation must then be solved for the highest index. That needs an invertibility/degree condition (it
    compares d·r₁ with 2r₂).
  * The resulting system can have a higher-order pole at c = 0, so it is not of the form cY′ = (B₀+cB₁)Y, and A.1's
    bit-burst lemma does not literally apply. It still has c = 0 as its only finite singularity, which suffices for
    bit-burst at c ≫ 0.
* **The phrase "(take c₀ > τ²)" for r = 1.** The starting point must be close to c = π²m², so for m ≤ τ/π one has to
  start farther out and continue along the real axis. Worth one sentence.

### 13. (Imprecise) l. 3772–3773
* **Problem.** "constants depend on … an a priori bound 2^{O(p)} for |Y|". A 2^{O(p)} bound affects the precision
  (O(p) guard bits), not a constant. Error propagation needs a bound on the *transition matrices*, which is a property
  of the system, not of |Y|.
* **Fix.** L1 provides it.

### 14. (Minor) l. 3796–3800
* **Problem.** The counts are derived from value bounds. For Laurent coefficients one needs the bounds on a disk
  |s−s₀| ≤ 1 (Cauchy). This is said only in A.9 (l. 3974–3975).

### 15. (Clarity) l. 4091
* **Problem.** "p = n log₂n + O(n) bits of L₁(…) determine B_n(x)". Only absolute error < f′^{n−1}/(2nD_n) = e^{-O(n)}
  is needed. p = n log₂n + O(n) is chosen to make |s₀| ≤ cp/log p hold. (Using the second case of `thm:uniform` with
  p = O(n) gives the same bound.)

### 16. (Clarity) l. 3790
* **Problem.** "the odd case only changes u^{-1/2} into u^{-3/2}". By Remark `rem:twist` it also replaces h_s by
  h_{s+δ} and introduces the weights k^δ.

### 17. (Mismatch with Lean) A.3 versus `Truncation.lean`
* **Problem.** The formal dual tail bound needs ∫₀^{u₀}u^{-1/2}|h| < ∞, i.e. Re s + n₀ > 1. It does not cover the
  values of s that the algorithm uses after continuation. L4 closes this.

### 18. (Mismatch with Lean) A.10 versus `bernoulli_eq_LFunction`
* **Problem.** The Lean result is stated for n ≥ 2 and 1 ≤ b ≤ N; the paper uses n ≥ 1. The case n = 1 is trivial to
  add.

### Checks that passed
* (eq:Ik): |lhs − rhs| = 2.9e-42 (a_n = 2^{-n}, s = 0.3+0.7i, k = 2, u₀ = ¼).
* A.8 log-moment recurrence: 5.6e-45.
* A.6 cancellation estimate: the max term is 1.6e15 × the result, against e^{2R√c₀} = 2.4e16 (R = 2, c₀ = 9π²,
  u₀ = ¼).
* The binary-splitting matrix [[A,0],[B,q]] with the indexing of l. 3754.
* (G1)–(G3) as formalized.
* The large-|s₀| parameter change (l. 4041).
* von Staudt–Clausen and the size bound in A.10.
* The Hurwitz-series denominator argument in A.10 (N/Q(1) ∈ O_K).
* The c_{j+2r₂}/c_j ratio in A.12.
* Max u^{-A}e^{-b/u} ≤ A^A for b ≥ 1.

---

## 7. Priorities (text removed per unit of formalization effort)

| rank | lemma | effort (Lean lines) | paper text removed or repaired | notes |
|---|---|---|---|---|
| 1 | **L1 Taylor step** | **done** (128) + ~60 for corollaries | l. 3772–3773, 3871–3875, 4000–4006, 4063–4064, 4147; fixes issues 3, 4, 13 | already proved; corollaries routine |
| 2 | **L4 kernel / truncation, uniform** | 350–450 | A.3 (8 lines), l. 3961–3975 (15), Cauchy remarks; closes issue 17 | uses G1/G2 and the majorant machinery of `Splitting/Kernel.lean` |
| 3 | **L5 (+L5′, L5″) x^j/Γ sums, uniform gamma tail** | ~200 | l. 3821–3822, 3833–3835, 3981–3983, 3987–3992 (~15 lines) | short given G1/G2 and `norm_tail_gammaPTerm_le` |
| 4 | **L3 regularity + L2 matrix product tree** | ~80 + ~190 | l. 3757–3759, all "by regularity" steps; makes Lemma A.1 citable | elementary; L3 alone (~80) gives most of the benefit |
| 5 | **L6 starting values** | 200–300 | l. 3864–3869, 4006–4015 (~15 lines) | generalizes `Khinchin/StartVals.lean`; `momentD_rec` is already complex |
| 6 | **L7 Bernoulli exactness** | ~150 | l. 4087–4091 (5 lines); makes Corollary `cor:bernoulli` formal modulo `thm:uniform` | Mathlib has von Staudt–Clausen, primorial, ζ(2k) |
| 7 | L8 Liouville | 50–100 | the δ's in G3 and all "≥ p^{-O(1)} by Liouville" (l. 3945–3946, 4009, 4021) | product formula in Mathlib |
| 8 | L10 b-free dual system | ~150 | repairs issue 1 (formal certificate for claim (c)) | text fix first; Lean optional |
| 9 | L11 (eq:Ik), L9 log-moments, L12 counts | 150 + 80 + 60 | formal checks of displays; removes "≈" | low text gain, high confidence gain |
| 10 | egf denominators, memory stack bound, large-\|s₀\| algebra | 120–300 each | a few lines each | low |

**Suggested order:** L1 corollaries → L3 → L5 → L4 → L6 → L7 → L8. In parallel, apply the text fixes for issues 1, 2, 5
and 6 (each one or two sentences), and restructure to "prove `thm:uniform` once", which by itself removes ~110 lines
of duplicated fixed-data analysis.
