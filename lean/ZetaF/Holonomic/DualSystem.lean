/-
# Proposition 3.6: the first-order system `c Y' = (B₀ + c B₁) Y` for the dual moments

Let `𝐆 = (G_q)_{q < ℓ}` satisfy `θ 𝐆 = A(u) 𝐆 + b(u)` with `A = ∑_{i ≤ d} A_i u^i`,
`b = ∑_{i ≤ e} b_i u^i`.  The vector `Y(c)` is formed by
`W_{t-i} = Z_{t-i}[𝐆](c)` (`i ≤ d`), `C_{t-i}(c) = Z_{t-i}[1](c)` (`i ≤ e`), `E(c) = e^{-c/u₀}`
and `E(c) G_q(u₀)`.  We write down `B₀`, `B₁` explicitly; their entries are `1 - t`, the entries of
the `A_i` and `b_i`, `-u₀^{1-t}`, `-1` and `-1/u₀`, so they do not depend on `c`.
-/
import ZetaF.Holonomic.DualMoments

open MeasureTheory Set Filter Finset Matrix
open scoped Real

namespace ZetaF

/-- Index set of the vector `Y`: `W`-block, `C`-block, `E`, `E·𝐆(u₀)`. -/
abbrev DualIdx (ℓ d e : ℕ) := (Fin (d + 1) × Fin ℓ) ⊕ (Fin (e + 1) ⊕ (Unit ⊕ Fin ℓ))

variable {ℓ d e : ℕ}

/-- The vector `Y(c)` of Proposition 3.6. -/
noncomputable def dualY (u₀ : ℝ) (t : ℂ) (G : Fin ℓ → ℝ → ℂ) (c : ℝ) : DualIdx ℓ d e → ℂ
  | .inl (i, q) => dualMoment u₀ c (t - (i : ℕ)) (G q)
  | .inr (.inl i) => dualMoment u₀ c (t - (i : ℕ)) (fun _ => 1)
  | .inr (.inr (.inl _)) => (Real.exp (-(c / u₀)) : ℂ)
  | .inr (.inr (.inr q)) => (Real.exp (-(c / u₀)) : ℂ) * G q u₀

/-- The constant matrix `B₀`. -/
noncomputable def dualB0 (u₀ : ℝ) (t : ℂ) (A : Fin (d + 1) → Matrix (Fin ℓ) (Fin ℓ) ℂ)
    (b : Fin (e + 1) → Fin ℓ → ℂ) : Matrix (DualIdx ℓ d e) (DualIdx ℓ d e) ℂ :=
  fun r col => match r, col with
  | .inl (i, q), .inl (i', p) =>
      if (i : ℕ) = 0 then (if i' = i ∧ p = q then 1 - t else 0) + A i' q p else 0
  | .inl (i, q), .inr (.inl i') => if (i : ℕ) = 0 then b i' q else 0
  | .inl (i, q), .inr (.inr (.inr p)) => if (i : ℕ) = 0 ∧ p = q then -(u₀ : ℂ) ^ (1 - t) else 0
  | .inr (.inl i), .inr (.inl i') => if (i : ℕ) = 0 ∧ i' = i then 1 - t else 0
  | .inr (.inl i), .inr (.inr (.inl _)) => if (i : ℕ) = 0 then -(u₀ : ℂ) ^ (1 - t) else 0
  | _, _ => 0

/-- The constant matrix `B₁`. -/
noncomputable def dualB1 (u₀ : ℝ) : Matrix (DualIdx ℓ d e) (DualIdx ℓ d e) ℂ :=
  fun r col => match r, col with
  | .inl (i, q), .inl (i', p) => if (i : ℕ) = i' + 1 ∧ p = q then -1 else 0
  | .inr (.inl i), .inr (.inl i') => if (i : ℕ) = i' + 1 then -1 else 0
  | .inr (.inr (.inl _)), .inr (.inr (.inl _)) => -(u₀ : ℂ)⁻¹
  | .inr (.inr (.inr q)), .inr (.inr (.inr p)) => if p = q then -(u₀ : ℂ)⁻¹ else 0
  | _, _ => 0

lemma hasDerivAt_expDiv {u₀ : ℝ} (c : ℝ) :
    HasDerivAt (fun x : ℝ => (Real.exp (-(x / u₀)) : ℂ)) (-(u₀ : ℂ)⁻¹ * (Real.exp (-(c / u₀)) : ℂ))
      c := by
  have h1 : HasDerivAt (fun x : ℝ => -(x / u₀)) (-(1 / u₀)) c := by
    have := (hasDerivAt_id c).const_mul (-(1 / u₀))
    rw [mul_one] at this
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp; ring)
  refine h1.exp.ofReal_comp.congr_deriv ?_
  push_cast; ring

/-- Sum of a "shift by one" row against a vector indexed by `Fin (n + 1)`. -/
lemma sum_ite_shift {n : ℕ} (i : Fin (n + 1)) (hi : (i : ℕ) ≠ 0) (x : Fin (n + 1) → ℂ) :
    ∑ i' : Fin (n + 1), (if (i : ℕ) = i' + 1 then x i' else 0) = x ⟨(i : ℕ) - 1, by omega⟩ := by
  rw [Finset.sum_eq_single ⟨(i : ℕ) - 1, by omega⟩]
  · split_ifs with h
    · rfl
    · exact absurd (show (i : ℕ) = (i : ℕ) - 1 + 1 by omega) h
  · intro j _ hj
    split_ifs with h
    · exfalso; apply hj; ext; simp only; omega
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

lemma sum_sum_ite_and {m n : ℕ} (i₀ : Fin m) (q : Fin n) (f : Fin m → Fin n → ℂ) :
    ∑ x : Fin m, ∑ y : Fin n, (if x = i₀ ∧ y = q then f x y else 0) = f i₀ q := by
  simp_rw [ite_and]
  simp [Finset.sum_ite_eq']

/-- **Proposition 3.6.**  For `c > 0`, `c Y'(c) = (B₀ + c B₁) Y(c)`. -/
theorem dual_system {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (t : ℂ)
    (A : Fin (d + 1) → Matrix (Fin ℓ) (Fin ℓ) ℂ) (b : Fin (e + 1) → Fin ℓ → ℂ)
    {G G' : Fin ℓ → ℝ → ℂ} (hG : ∀ q, ∀ u ∈ Icc 0 u₀, HasDerivAt (G q) (G' q u) u)
    (hG' : ∀ q, ContinuousOn (G' q) (Icc 0 u₀))
    (hsys : ∀ q, ∀ u ∈ Icc 0 u₀, (u : ℂ) * G' q u =
      ∑ i : Fin (d + 1), ∑ p : Fin ℓ, A i q p * ((u : ℂ) ^ (i : ℕ) * G p u) +
        ∑ i : Fin (e + 1), b i q * (u : ℂ) ^ (i : ℕ))
    (r : DualIdx ℓ d e) :
    HasDerivAt (fun x => dualY (d := d) (e := e) u₀ t G x r)
      ((c : ℂ)⁻¹ * ((dualB0 u₀ t A b + (c : ℂ) • dualB1 u₀) *ᵥ dualY u₀ t G c) r) c := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hGc : ∀ p, ContinuousOn (G p) (Icc 0 u₀) := fun p u hu =>
    (hG p u hu).continuousAt.continuousWithinAt
  rw [add_mulVec, smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases r with ⟨i, q⟩ | i | ⟨⟩ | q
  · -- `W`-block
    have hd := hasDerivAt_dualMoment hc hu₀ (t - (i : ℕ)) (hGc q)
    show HasDerivAt (fun x => dualMoment u₀ x (t - (i : ℕ)) (G q)) _ c
    by_cases hi : (i : ℕ) = 0
    · have hrec := dualMoment_system_rec hc hu₀ t A b hG hG' hsys q
      have h1 : (dualB1 u₀ *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inl (i, q)) = 0 := by
        simp [mulVec, dotProduct, dualB1, Fintype.sum_sum_type, hi]
      have hi0 : i = 0 := Fin.ext hi
      subst hi0
      have h0 : (dualB0 u₀ t A b *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inl (0, q)) =
          -(c * dualMoment u₀ c (t + 1) (G q)) := by
        rw [hrec]
        simp only [mulVec, dotProduct, dualB0, Fintype.sum_sum_type, Fintype.sum_prod_type,
          hi, ite_true, true_and, dualY, add_mul, Finset.sum_add_distrib,
          zero_mul, Finset.sum_const_zero, ite_mul]
        rw [sum_sum_ite_and (0 : Fin (d + 1)) q (fun x y => (1 - t) * dualMoment u₀ c (t - (x : ℕ)) (G y))]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        simp
        ring
      rw [h0, h1, mul_zero, add_zero]
      convert hd using 1
      simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
      field_simp
    · have hi' : i ≠ 0 := fun h => hi (by simp [h])
      have h0 : (dualB0 u₀ t A b *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inl (i, q)) = 0 := by
        simp [mulVec, dotProduct, dualB0, Fintype.sum_sum_type, hi']
      have h1 : (dualB1 u₀ *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inl (i, q)) =
          -dualMoment u₀ c (t - (((i : ℕ) - 1 : ℕ) : ℂ)) (G q) := by
        simp only [mulVec, dotProduct, dualB1, Fintype.sum_sum_type, Fintype.sum_prod_type,
          zero_mul, Finset.sum_const_zero, add_zero, ite_and, ite_mul, Finset.sum_ite_irrel,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [sum_ite_shift i hi (fun i' => -1 * dualY (d := d) (e := e) u₀ t G c (.inl (i', q)))]
        simp [dualY]
      rw [h0, h1, zero_add]
      convert hd using 1
      have hcast : (((i : ℕ) - 1 : ℕ) : ℂ) = ((i : ℕ) : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast, show t - (((i : ℕ) : ℂ) - 1) = t - ((i : ℕ) : ℂ) + 1 by ring]
      field_simp
  · -- `C`-block
    have hd := hasDerivAt_dualMoment hc hu₀ (t - (i : ℕ)) (continuousOn_const (c := (1 : ℂ)))
    show HasDerivAt (fun x => dualMoment u₀ x (t - (i : ℕ)) (fun _ => 1)) _ c
    by_cases hi : (i : ℕ) = 0
    · have hrec := dualMoment_one_rec hc hu₀ t
      have h1 : (dualB1 u₀ *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inr (.inl i)) = 0 := by
        simp [mulVec, dotProduct, dualB1, Fintype.sum_sum_type, hi]
      have hi0 : i = 0 := Fin.ext hi
      subst hi0
      have h0 : (dualB0 u₀ t A b *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inr (.inl 0)) =
          -(c * dualMoment u₀ c (t + 1) (fun _ => 1)) := by
        rw [hrec]
        simp [mulVec, dotProduct, dualB0, Fintype.sum_sum_type, dualY]
        ring
      rw [h0, h1, mul_zero, add_zero]
      convert hd using 1
      simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
      field_simp
    · have hi' : i ≠ 0 := fun h => hi (by simp [h])
      have h0 : (dualB0 u₀ t A b *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inr (.inl i)) = 0 := by
        simp [mulVec, dotProduct, dualB0, Fintype.sum_sum_type, hi']
      have h1 : (dualB1 u₀ *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inr (.inl i)) =
          -dualMoment u₀ c (t - (((i : ℕ) - 1 : ℕ) : ℂ)) (fun _ => 1) := by
        simp only [mulVec, dotProduct, dualB1, Fintype.sum_sum_type,
          zero_mul, Finset.sum_const_zero, add_zero, zero_add, ite_mul]
        rw [sum_ite_shift i hi (fun i' => -1 * dualY (d := d) (e := e) u₀ t G c (.inr (.inl i')))]
        simp [dualY]
      rw [h0, h1, zero_add]
      convert hd using 1
      have hcast : (((i : ℕ) - 1 : ℕ) : ℂ) = ((i : ℕ) : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast, show t - (((i : ℕ) : ℂ) - 1) = t - ((i : ℕ) : ℂ) + 1 by ring]
      field_simp
  · -- `E`
    show HasDerivAt (fun x : ℝ => (Real.exp (-(x / u₀)) : ℂ)) _ c
    have h0 : (dualB0 u₀ t A b *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inr (.inr (.inl ()))) = 0 := by
      simp [mulVec, dotProduct, dualB0]
    have h1 : (dualB1 u₀ *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inr (.inr (.inl ()))) =
        -(u₀ : ℂ)⁻¹ * (Real.exp (-(c / u₀)) : ℂ) := by
      simp [mulVec, dotProduct, dualB1, Fintype.sum_sum_type, dualY]
    rw [h0, h1, zero_add]
    convert hasDerivAt_expDiv (u₀ := u₀) c using 1
    field_simp
  · -- `E 𝐆(u₀)`
    show HasDerivAt (fun x : ℝ => (Real.exp (-(x / u₀)) : ℂ) * G q u₀) _ c
    have h0 : (dualB0 u₀ t A b *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inr (.inr (.inr q))) = 0 := by
      simp [mulVec, dotProduct, dualB0]
    have h1 : (dualB1 u₀ *ᵥ dualY (d := d) (e := e) u₀ t G c) (.inr (.inr (.inr q))) =
        -(u₀ : ℂ)⁻¹ * ((Real.exp (-(c / u₀)) : ℂ) * G q u₀) := by
      simp [mulVec, dotProduct, dualB1, Fintype.sum_sum_type, dualY]
    rw [h0, h1, zero_add]
    convert (hasDerivAt_expDiv (u₀ := u₀) c).mul_const (G q u₀) using 1
    field_simp

end ZetaF
