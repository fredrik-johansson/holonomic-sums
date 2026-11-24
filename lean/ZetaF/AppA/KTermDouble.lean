/-
Copyright (c) 2026. Released under Apache 2.0 license.

# The double-series form (eq:Ik) of the `k`-terms (Appendix A, lemma L11)

From the series `I_k(s) = ∑_n a_n k^{-s-n} Q((s+n)/2, k²u₀)` of Theorem 3.2 (`hasSum_kTerm_gammaQ`), splitting by
the parity of `n` and using `Q(σ + m, x) = Q(σ, x) + e^{-x} ∑_{j<m} x^{σ+j}/Γ(σ+j+1)` (`gammaQ_add_nat`): with
`κ = k²`, `x = κ u₀`, `σ = s/2`, `τ = (s+1)/2`, `A₀(y) = ∑ a_{2m} y^m`, `A₁(y) = ∑ a_{2m+1} y^m`,

`I_k(s) = k^{-s} (Q(σ, x) A₀(1/κ) + Q(τ, x) A₁(1/κ)/k)
        + e^{-x} u₀^σ ∑_m a_{2m} κ^{-m} ∑_{j<m} x^j/Γ(σ+j+1)
        + e^{-x} u₀^τ ∑_m a_{2m+1} κ^{-m} ∑_{j<m} x^j/Γ(τ+j+1)`

(`kTerm_double_series`), all series absolutely convergent for `k > R`. This is the form in which Appendix A
sums the `k`-terms by binary splitting.
-/
import ZetaF.Continuation.Theorem
import ZetaF.IncompleteGammaSeries

open Complex Finset
open scoped Topology

namespace ZetaF.AppA

/-- `∑_j x^j |1/Γ(σ + j + 1)|` converges. -/
lemma summable_pow_mul_norm_inv_Gamma (σ : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun j : ℕ => x ^ j * ‖(Gamma (σ + j + 1))⁻¹‖ := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (-σ.re)
  set w := σ + N₀ + 1 with hw
  have hw0 : 0 < w.re := by simp [hw]; linarith
  refine (summable_nat_add_iff N₀).1 ?_
  have hs := (summable_pow_div_Gamma_add (y := w.re) (q := x) hw0 hx).mul_left
    (x ^ N₀ * gammaRatio w)
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs
  have h1 : σ + ((j + N₀ : ℕ) : ℂ) + 1 = w + j := by rw [hw]; push_cast; ring
  rw [h1, pow_add]
  have h2 := norm_inv_Gamma_add_nat_le hw0 j
  have hp : 0 ≤ x ^ j * x ^ N₀ := by positivity
  calc x ^ j * x ^ N₀ * ‖(Gamma (w + j))⁻¹‖ ≤ x ^ j * x ^ N₀ * (gammaRatio w / Real.Gamma (w.re + j)) :=
        mul_le_mul_of_nonneg_left h2 hp
    _ = _ := by ring

/-- The power identity `k^{-(2w+2m)} x^{w+i} = u₀^w κ^{-m} x^i` for `x = k² u₀`, `κ = k²`. -/
lemma cpow_identity {k u₀ : ℝ} (hk : 0 < k) (hu₀ : 0 < u₀) (w : ℂ) (m i : ℕ) :
    (k : ℂ) ^ (-(2 * w + 2 * m)) * ((k ^ 2 * u₀ : ℝ) : ℂ) ^ (w + i) =
      (u₀ : ℂ) ^ w * (((k ^ 2 : ℝ) : ℂ)⁻¹) ^ m * ((k ^ 2 * u₀ : ℝ) : ℂ) ^ i := by
  have hk' : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk.ne'
  have hx : ((k ^ 2 * u₀ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
  rw [cpow_add _ _ hx, cpow_natCast, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) hu₀.le]
  have hsq : ((k ^ 2 : ℝ) : ℂ) ^ w = (k : ℂ) ^ (2 * w) := by
    have := sq_cpow_neg hk (-w); simpa using this
  rw [hsq]
  have hpow : (k : ℂ) ^ (-(2 * w + 2 * m)) * (k : ℂ) ^ (2 * w) = (((k ^ 2 : ℝ) : ℂ)⁻¹) ^ m := by
    rw [← cpow_add _ _ hk', show -(2 * w + 2 * (m : ℂ)) + 2 * w = -((2 * m : ℕ) : ℂ) by push_cast; ring,
      cpow_neg, cpow_natCast, inv_pow]
    push_cast; ring
  rw [← hpow]; ring

section

variable {a : ℕ → ℂ} {R : ℝ} (ha : GeomBounded a R) (hR : 0 ≤ R) {k : ℕ} (hk : R < k)
  {u₀ : ℝ} (hu₀ : 0 < u₀) (s : ℂ)

include ha hR hk hu₀ in
/-- The parity part: for `w = σ` (`ε = 0`) or `w = τ` (`ε = 1`), with `2w = s + ε`,
`∑_m a_{2m+ε} k^{-(s+2m+ε)} Q(w+m, x) = k^{-(s+ε)} Q(w, x) A_ε(1/κ) + e^{-x} u₀^w ∑_m a_{2m+ε} κ^{-m} ∑_{j<m} x^j/Γ(w+j+1)`. -/
lemma hasSum_parity_part (ε : ℕ) (w : ℂ) (hw : 2 * w = s + ε) :
    HasSum (fun m : ℕ => a (2 * m + ε) * (k : ℂ) ^ (-(s + ((2 * m + ε : ℕ) : ℂ))) *
        gammaQ (w + m) ((k : ℝ) ^ 2 * u₀))
      ((k : ℂ) ^ (-(s + ε)) * gammaQ w ((k : ℝ) ^ 2 * u₀) *
          ∑' m : ℕ, a (2 * m + ε) * ((((k : ℝ) ^ 2 : ℝ) : ℂ)⁻¹) ^ m +
        (Real.exp (-((k : ℝ) ^ 2 * u₀)) : ℂ) * (u₀ : ℂ) ^ w *
          ∑' m : ℕ, a (2 * m + ε) * ((((k : ℝ) ^ 2 : ℝ) : ℂ)⁻¹) ^ m *
            ∑ j ∈ range m, (((k : ℝ) ^ 2 * u₀ : ℝ) : ℂ) ^ j * (Gamma (w + j + 1))⁻¹) := by
  obtain ⟨C, hC⟩ := ha
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt hR hk
  set x : ℝ := (k : ℝ) ^ 2 * u₀ with hxdef
  have hx : 0 < x := by positivity
  set κi : ℂ := ((((k : ℝ) ^ 2 : ℝ) : ℂ)⁻¹)
  have hκi : ‖κi‖ = ((k : ℝ) ^ 2)⁻¹ := by
    simp only [κi, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)]
  set ρ : ℝ := (R / k) ^ 2
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    simp only [ρ]; rw [div_pow]; exact (div_lt_one (by positivity)).2 (by nlinarith)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) ((hC 0).trans (by simp))
  -- the bound `‖a_{2m+ε} κ^{-m}‖ ≤ C R^ε ρ^m`
  have hbound : ∀ m : ℕ, ‖a (2 * m + ε) * κi ^ m‖ ≤ C * R ^ ε * ρ ^ m := by
    intro m
    rw [norm_mul, norm_pow, hκi]
    have h1 := hC (2 * m + ε)
    have e : C * R ^ (2 * m + ε) * (((k : ℝ) ^ 2)⁻¹) ^ m = C * R ^ ε * ρ ^ m := by
      simp only [ρ]; ring
    rw [← e]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hgeo : Summable fun m : ℕ => C * R ^ ε * ρ ^ m :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hA : Summable fun m : ℕ => a (2 * m + ε) * κi ^ m := Summable.of_norm_bounded hgeo hbound
  -- the inner sums are uniformly bounded
  set Mx := ∑' j : ℕ, x ^ j * ‖(Gamma (w + j + 1))⁻¹‖
  have hMs := summable_pow_mul_norm_inv_Gamma w hx.le
  have hinner : ∀ m : ℕ, ‖∑ j ∈ range m, ((x : ℝ) : ℂ) ^ j * (Gamma (w + j + 1))⁻¹‖ ≤ Mx := by
    intro m
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ range m, ‖((x : ℝ) : ℂ) ^ j * (Gamma (w + j + 1))⁻¹‖
        = ∑ j ∈ range m, x ^ j * ‖(Gamma (w + j + 1))⁻¹‖ := by
          refine sum_congr rfl fun j _ => ?_
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le]
      _ ≤ Mx := hMs.sum_le_tsum _ (fun j _ => by positivity)
  have hB : Summable fun m : ℕ => a (2 * m + ε) * κi ^ m *
      ∑ j ∈ range m, ((x : ℝ) : ℂ) ^ j * (Gamma (w + j + 1))⁻¹ := by
    refine Summable.of_norm_bounded (hgeo.mul_right Mx) fun m => ?_
    rw [norm_mul]
    exact mul_le_mul (hbound m) (hinner m) (norm_nonneg _) (by positivity)
  -- the termwise identity
  have hterm : ∀ m : ℕ, a (2 * m + ε) * (k : ℂ) ^ (-(s + ((2 * m + ε : ℕ) : ℂ))) * gammaQ (w + m) x =
      (k : ℂ) ^ (-(s + ε)) * gammaQ w x * (a (2 * m + ε) * κi ^ m) +
        (Real.exp (-x) : ℂ) * (u₀ : ℂ) ^ w *
          (a (2 * m + ε) * κi ^ m * ∑ j ∈ range m, ((x : ℝ) : ℂ) ^ j * (Gamma (w + j + 1))⁻¹) := by
    intro m
    rw [gammaQ_add_nat w hx m, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    have hk' : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk0.ne' |> fun h => by exact_mod_cast h
    have hsplit : (k : ℂ) ^ (-(s + ((2 * m + ε : ℕ) : ℂ))) = (k : ℂ) ^ (-(s + ε)) * κi ^ m := by
      rw [show -(s + ((2 * m + ε : ℕ) : ℂ)) = -(s + ε) + -((2 * m : ℕ) : ℂ) by push_cast; ring,
        cpow_add _ _ hk', cpow_neg (k : ℂ) ((2 * m : ℕ) : ℂ), cpow_natCast]
      simp only [κi]; push_cast; rw [inv_pow, ← pow_mul]
    congr 1
    · rw [hsplit]; ring
    · refine sum_congr rfl fun j _ => ?_
      unfold gammaPTerm
      have hid := cpow_identity hk0 hu₀ w m j
      rw [show 2 * w + 2 * (m : ℂ) = s + ((2 * m + ε : ℕ) : ℂ) by rw [hw]; push_cast; ring] at hid
      have : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; rfl
      rw [this] at hid
      calc a (2 * m + ε) * (k : ℂ) ^ (-(s + ((2 * m + ε : ℕ) : ℂ))) *
            ((x : ℂ) ^ (w + j) * (Real.exp (-x) : ℂ) * (Gamma (w + j + 1))⁻¹)
          = a (2 * m + ε) * ((k : ℂ) ^ (-(s + ((2 * m + ε : ℕ) : ℂ))) * (x : ℂ) ^ (w + j)) *
              (Real.exp (-x) : ℂ) * (Gamma (w + j + 1))⁻¹ := by ring
        _ = _ := by rw [hxdef, hid]; simp only [κi]; push_cast; ring
  simp_rw [hterm]
  exact ((hA.hasSum.mul_left _)).add (hB.hasSum.mul_left _)

include ha hR hk hu₀ in
/-- **(eq:Ik)**: the double-series form of the `k`-term `I_k(s)`, for every `s ∈ ℂ` and `k > R`. -/
theorem kTerm_double_series :
    kTerm (kernel a s) u₀ k =
      ((k : ℂ) ^ (-s) * gammaQ (s / 2) ((k : ℝ) ^ 2 * u₀) *
          ∑' m : ℕ, a (2 * m) * ((((k : ℝ) ^ 2 : ℝ) : ℂ)⁻¹) ^ m +
        (Real.exp (-((k : ℝ) ^ 2 * u₀)) : ℂ) * (u₀ : ℂ) ^ (s / 2) *
          ∑' m : ℕ, a (2 * m) * ((((k : ℝ) ^ 2 : ℝ) : ℂ)⁻¹) ^ m *
            ∑ j ∈ range m, (((k : ℝ) ^ 2 * u₀ : ℝ) : ℂ) ^ j * (Gamma (s / 2 + j + 1))⁻¹) +
      ((k : ℂ) ^ (-(s + 1)) * gammaQ ((s + 1) / 2) ((k : ℝ) ^ 2 * u₀) *
          ∑' m : ℕ, a (2 * m + 1) * ((((k : ℝ) ^ 2 : ℝ) : ℂ)⁻¹) ^ m +
        (Real.exp (-((k : ℝ) ^ 2 * u₀)) : ℂ) * (u₀ : ℂ) ^ ((s + 1) / 2) *
          ∑' m : ℕ, a (2 * m + 1) * ((((k : ℝ) ^ 2 : ℝ) : ℂ)⁻¹) ^ m *
            ∑ j ∈ range m, (((k : ℝ) ^ 2 * u₀ : ℝ) : ℂ) ^ j * (Gamma ((s + 1) / 2 + j + 1))⁻¹) := by
  have hS := hasSum_kTerm_gammaQ ha hR hk hu₀ s
  have he := hasSum_parity_part ha hR hk hu₀ s 0 (s / 2) (by push_cast; ring)
  have ho := hasSum_parity_part ha hR hk hu₀ s 1 ((s + 1) / 2) (by push_cast; ring)
  set f : ℕ → ℂ := fun n => a n * (k : ℂ) ^ (-(s + n)) * gammaQ ((s + n) / 2) ((k : ℝ) ^ 2 * u₀)
  have hfe : (fun m : ℕ => a (2 * m + 0) * (k : ℂ) ^ (-(s + ((2 * m + 0 : ℕ) : ℂ))) *
      gammaQ (s / 2 + m) ((k : ℝ) ^ 2 * u₀)) = fun m => f (2 * m) := by
    ext m; simp only [f, Nat.add_zero]; congr 2; push_cast; ring
  have hfo : (fun m : ℕ => a (2 * m + 1) * (k : ℂ) ^ (-(s + ((2 * m + 1 : ℕ) : ℂ))) *
      gammaQ ((s + 1) / 2 + m) ((k : ℝ) ^ 2 * u₀)) = fun m => f (2 * m + 1) := by
    ext m; simp only [f]; congr 2; push_cast; ring
  rw [hfe] at he
  rw [hfo] at ho
  refine hS.unique ?_
  convert he.even_add_odd ho using 1
  simp

end

end ZetaF.AppA
