/-
# Lemma 3.1 (`lem:kernelhol`), coefficient level

If `β` satisfies an (H)-recurrence `∑_{j=0}^r Q_j(m-j) β_{m-j} = 0` (for large `m`), then
`γ_m = β_m / Γ(m + σ₀)` satisfies `∑_j Q̃_j(m-j) γ_{m-j} = 0` with
`Q̃_j(n) = Q_j(n) (n + j - r + σ₀)_{r-j}`, i.e. `Q̃_j(m-j) = Q_j(m-j) (m - r + σ₀)_{r-j}`.

Moreover `deg Q̃_j ≤ deg Q_j + r - j`, `deg Q̃_0 = deg Q_0 + r` and `Q̃_0` has the same leading
coefficient as `Q_0`; hence the coefficient of `θ^{d+r}` in `∑_j u^j Q̃_j(θ)` is a nonzero constant,
which is what gives the first-order system (10) polynomial coefficients.

We use Mathlib's convention `1/Γ = (Gamma ·)⁻¹`, which is `0` at the poles, so no case distinction is
needed: the identity `(x)_n / Γ(x + n) = 1/Γ(x)` holds for all `x`.
-/
import ZetaF.Holonomic.ThetaOperator

open Polynomial Finset Filter Complex

namespace ZetaF

/-- `y / Γ(y + 1) = 1 / Γ(y)` for all `y` (with `1/Γ = 0` at the poles). -/
lemma mul_inv_Gamma_add_one (y : ℂ) : y * (Gamma (y + 1))⁻¹ = (Gamma y)⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Complex.Gamma_zero]
  · rw [Complex.Gamma_add_one y hy, mul_inv, ← mul_assoc, mul_inv_cancel₀ hy, one_mul]

/-- `(x)_n / Γ(x + n) = 1/Γ(x)` for all `x ∈ ℂ`. -/
lemma prod_mul_inv_Gamma_add (x : ℂ) (n : ℕ) :
    (∏ i ∈ range n, (x + i)) * (Gamma (x + n))⁻¹ = (Gamma x)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, mul_assoc, ← ih]
    congr 1
    have := mul_inv_Gamma_add_one (x + n)
    push_cast
    rw [← add_assoc, this]

/-- The Pochhammer factor `P_j(X) = (X + j - r + σ₀)_{r-j} = ∏_{i < r-j} (X + j - r + σ₀ + i)`. -/
noncomputable def pochFactor (r j : ℕ) (σ₀ : ℂ) : ℂ[X] :=
  ∏ i ∈ range (r - j), (X + C ((j : ℂ) - r + σ₀ + i))

lemma eval_pochFactor (r j : ℕ) (σ₀ z : ℂ) :
    (pochFactor r j σ₀).eval z = ∏ i ∈ range (r - j), (z + ((j : ℂ) - r + σ₀) + i) := by
  simp [pochFactor, eval_prod, add_assoc]

lemma monic_pochFactor (r j : ℕ) (σ₀ : ℂ) : (pochFactor r j σ₀).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_add_C _

lemma natDegree_pochFactor (r j : ℕ) (σ₀ : ℂ) : (pochFactor r j σ₀).natDegree = r - j := by
  rw [pochFactor, natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]

namespace ThetaOp

/-- The twisted operator `∑_{j ≤ r} x^j Q_j(θ) P_j(θ)`, `r = deg_x L`. -/
noncomputable def gammaTwist (L : ThetaOp ℂ) (σ₀ : ℂ) : ThetaOp ℂ :=
  ∑ j ∈ range (L.natDegree + 1), monomial j (L.coeff j * pochFactor L.natDegree j σ₀)

lemma coeff_gammaTwist (L : ThetaOp ℂ) (σ₀ : ℂ) (j : ℕ) :
    (L.gammaTwist σ₀).coeff j = L.coeff j * pochFactor L.natDegree j σ₀ := by
  rw [gammaTwist, finsetSum_coeff]
  by_cases hj : j ≤ L.natDegree
  · rw [sum_eq_single j]
    · simp
    · intro b _ hb; simp [coeff_monomial, hb]
    · intro h; simp at h; omega
  · rw [sum_eq_zero, show L.coeff j = 0 from coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    intro b hb; simp only [mem_range] at hb
    rw [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (by omega)]

/-- **Lemma 3.1 (recurrence part).** If `L` annihilates `β` (eventually) then the Gamma twist of
`L` annihilates `γ_m = β_m / Γ(m + σ₀)` (eventually). -/
theorem annihilatesEventually_gammaTwist {L : ThetaOp ℂ} {β : ℕ → ℂ} (σ₀ : ℂ)
    (hL : L.AnnihilatesEventually β) :
    (L.gammaTwist σ₀).AnnihilatesEventually fun m => β m * (Gamma (m + σ₀))⁻¹ := by
  set r := L.natDegree
  obtain ⟨N, hN⟩ := eventually_atTop.1 hL
  refine eventually_atTop.2 ⟨max N r, fun m hm => ?_⟩
  have key : ∀ j ∈ range (m + 1), ((L.gammaTwist σ₀).coeff j).eval ((m - j : ℕ) : ℂ) *
      (β (m - j) * (Gamma ((m - j : ℕ) + σ₀))⁻¹) =
      (Gamma ((m : ℂ) - r + σ₀))⁻¹ * ((L.coeff j).eval ((m - j : ℕ) : ℂ) * β (m - j)) := by
    intro j hj
    simp only [mem_range] at hj
    rw [coeff_gammaTwist, eval_mul, eval_pochFactor]
    by_cases hjr : j ≤ r
    · have h := prod_mul_inv_Gamma_add ((m : ℂ) - r + σ₀) (r - j)
      have e1 : ((m : ℂ) - r + σ₀) + ((r - j : ℕ) : ℂ) = ((m - j : ℕ) : ℂ) + σ₀ := by
        push_cast [Nat.cast_sub hjr, Nat.cast_sub (show j ≤ m by omega)]; ring
      rw [e1] at h
      have e2 : ∀ i : ℕ, ((m - j : ℕ) : ℂ) + ((j : ℂ) - r + σ₀) + i = (m : ℂ) - r + σ₀ + i := by
        intro i; push_cast [Nat.cast_sub (show j ≤ m by omega)]; ring
      rw [prod_congr rfl fun i _ => e2 i, ← h]; ring
    · rw [show L.coeff j = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  unfold applySeq
  rw [sum_congr rfl key, ← mul_sum]
  have := hN m (le_of_max_le_left hm)
  unfold applySeq at this
  rw [this, mul_zero]

/-- Degree bounds for the twisted operator: `deg Q̃_j ≤ deg Q_j + (r - j)`. -/
lemma natDegree_coeff_gammaTwist_le (L : ThetaOp ℂ) (σ₀ : ℂ) (j : ℕ) :
    ((L.gammaTwist σ₀).coeff j).natDegree ≤ (L.coeff j).natDegree + (L.natDegree - j) := by
  rw [coeff_gammaTwist]
  exact (natDegree_mul_le).trans (by rw [natDegree_pochFactor])

/-- `deg Q̃_0 = deg Q_0 + r`, with the same leading coefficient. -/
lemma natDegree_coeff_zero_gammaTwist (L : ThetaOp ℂ) (σ₀ : ℂ) (h0 : L.coeff 0 ≠ 0) :
    ((L.gammaTwist σ₀).coeff 0).natDegree = (L.coeff 0).natDegree + L.natDegree ∧
    ((L.gammaTwist σ₀).coeff 0).leadingCoeff = (L.coeff 0).leadingCoeff := by
  rw [coeff_gammaTwist]
  have hm := monic_pochFactor L.natDegree 0 σ₀
  refine ⟨?_, ?_⟩
  · rw [natDegree_mul h0 hm.ne_zero, natDegree_pochFactor, Nat.sub_zero]
  · rw [leadingCoeff_mul, hm.leadingCoeff, mul_one]

/-- **(H) is preserved, in the strong form needed for (10).**  If `L` satisfies (H) with
`d = deg Q_0`, then for `1 ≤ j` the coefficient of `θ^{d+r}` in `Q̃_j` vanishes, while in `Q̃_0` it is
the leading coefficient of `Q_0` (nonzero).  Hence in `∑_j u^j Q̃_j(θ)` the top coefficient of `θ` is
a nonzero constant. -/
theorem gammaTwist_top_coeff {L : ThetaOp ℂ} (hL : L.IsFuchsian) (σ₀ : ℂ) :
    ((L.gammaTwist σ₀).coeff 0).coeff ((L.coeff 0).natDegree + L.natDegree) =
        (L.coeff 0).leadingCoeff ∧
    ∀ j, 1 ≤ j → ((L.gammaTwist σ₀).coeff j).coeff ((L.coeff 0).natDegree + L.natDegree) = 0 := by
  obtain ⟨h0, hdeg⟩ := hL
  obtain ⟨hd, hlc⟩ := natDegree_coeff_zero_gammaTwist L σ₀ h0
  refine ⟨by rw [← hd, coeff_natDegree, hlc], fun j hj => ?_⟩
  by_cases hjr : j ≤ L.natDegree
  · apply coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt (natDegree_coeff_gammaTwist_le L σ₀ j) ?_
    have := hdeg j
    have hr : 1 ≤ L.natDegree := le_trans hj hjr
    omega
  · rw [coeff_gammaTwist, show L.coeff j = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- The Gamma twist of an (H)-operator satisfies (H). -/
theorem IsFuchsian.gammaTwist {L : ThetaOp ℂ} (hL : L.IsFuchsian) (σ₀ : ℂ) :
    (L.gammaTwist σ₀).IsFuchsian := by
  obtain ⟨h0, hdeg⟩ := hL
  obtain ⟨hd, -⟩ := natDegree_coeff_zero_gammaTwist L σ₀ h0
  refine ⟨?_, fun j => ?_⟩
  · rw [coeff_gammaTwist]; exact mul_ne_zero h0 (monic_pochFactor _ _ _).ne_zero
  · rw [hd]
    exact (natDegree_coeff_gammaTwist_le L σ₀ j).trans (by have := hdeg j; omega)

end ThetaOp

end ZetaF
