/-
# Theta transformations with an additive character (Theorem 4.1, `|z| = 1`)

For real `α`, `z = e^{2πiα}`, `c_n = π²(n-α)²`:
`∑_{k ∈ ℤ} z^k e^{-k²u} = √(π/u) ∑_{n ∈ ℤ} e^{-c_n/u}`,
`∑_{k ∈ ℤ} k z^k e^{-k²u} = -i π^{3/2} u^{-3/2} ∑_{n ∈ ℤ} (n - α) e^{-c_n/u}`,
and the one-sided forms with `C_k = (z^k + z^{-k})/2`, `S_k = (z^k - z^{-k})/2` used in the proof of
Theorem 4.1.
-/
import ZetaF.Twisted.Odd

open Real Complex Finset

namespace ZetaF

/-- The dual points `c_n = π²(n - α)²`. -/
noncomputable def geoDual (α : ℝ) (n : ℤ) : ℝ := π ^ 2 * ((n : ℝ) - α) ^ 2

/-- `C_k = (z^k + z^{-k})/2`. -/
noncomputable def geoC (z : ℂ) (k : ℕ) : ℂ := (z ^ k + (z ^ k)⁻¹) / 2

/-- `S_k = (z^k - z^{-k})/2`. -/
noncomputable def geoS (z : ℂ) (k : ℕ) : ℂ := (z ^ k - (z ^ k)⁻¹) / 2

lemma tsum_int_neg {f : ℤ → ℂ} : ∑' n : ℤ, f (-n) = ∑' n : ℤ, f n :=
  (Equiv.neg ℤ).tsum_eq f

lemma summable_geoDual (α : ℝ) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℤ => rexp (-(geoDual α n / u)) := by
  have hs := (summable_int_exp_neg_mul_sq (c := π ^ 2 / u / 2) (by positivity)).mul_left
    (rexp (π ^ 2 / u * α ^ 2))
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun n => ?_) hs
  rw [← Real.exp_add, Real.exp_le_exp, geoDual]
  have hc : 0 < π ^ 2 / u := by positivity
  have : ((n : ℝ) - α) ^ 2 ≥ (n : ℝ) ^ 2 / 2 - α ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 2 * α)]
  have h2 : π ^ 2 * ((n : ℝ) - α) ^ 2 / u = π ^ 2 / u * ((n : ℝ) - α) ^ 2 := by ring
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left this hc.le]

lemma summable_abs_mul_geoDual (α : ℝ) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℤ => |(n : ℝ) - α| * rexp (-(geoDual α n / u)) := by
  have hs := (summable_geoDual α (u := 2 * u) (by positivity)).div_const (√(π ^ 2 / u))
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hs
  have := abs_mul_exp_neg_sq_le ((n : ℝ) - α) (u := π ^ 2 / u) (by positivity)
  convert this using 2
  · rw [geoDual]; congr 2; ring
  · rw [geoDual]; congr 2; field_simp

/-- `∑_{k ∈ ℤ} e^{2πiαk} e^{-k²u} = √(π/u) ∑_{n ∈ ℤ} e^{-c_n/u}`. -/
theorem tsum_geo_theta (α : ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' k : ℤ, cexp (2 * π * I * α * k) * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) =
      ((√(π / u) : ℝ) : ℂ) * ∑' n : ℤ, (rexp (-(geoDual α n / u)) : ℂ) := by
  have hπ := Real.pi_pos
  have key := tsum_exp_shifted_sq (q := 1) one_pos (-α) (u := π ^ 2 / u) (by positivity)
  have hL : ∀ j : ℤ, (rexp (-((-α + ((1 : ℕ) : ℝ) * j) ^ 2 * (π ^ 2 / u))) : ℂ) =
      (rexp (-(geoDual α j / u)) : ℂ) := fun j => by
    rw [geoDual]; congr 3; push_cast; ring
  have hR : ∀ n : ℤ, cexp (2 * π * I * n * ((-α : ℝ) : ℂ) / ((1 : ℕ) : ℂ)) *
      (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (((1 : ℕ) : ℝ) ^ 2 * (π ^ 2 / u)))) : ℂ) =
      cexp (2 * π * I * α * ((-n : ℤ) : ℝ)) * (rexp (-((((-n : ℤ) : ℝ)) ^ 2 * u)) : ℂ) := by
    intro n
    congr 2
    · push_cast; ring
    · push_cast; field_simp
  simp only [hL, hR] at key
  rw [tsum_int_neg (f := fun k : ℤ => cexp (2 * π * I * α * (k : ℝ)) *
    (rexp (-((k : ℝ) ^ 2 * u)) : ℂ))] at key
  rw [key, ← mul_assoc]
  have h1 : ((√(π / u) : ℝ) : ℂ) * ((1 / ((1 : ℕ) : ℝ) * √(π / (π ^ 2 / u)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Nat.cast_one, div_one, one_mul, ← Real.sqrt_mul (by positivity),
      show π / u * (π / (π ^ 2 / u)) = 1 by field_simp, Real.sqrt_one, Complex.ofReal_one]
  push_cast at h1 ⊢
  rw [h1, one_mul]

/-- `∑_{k ∈ ℤ} k e^{2πiαk} e^{-k²u} = -i π√π/(u√u) ∑_{n ∈ ℤ} (n - α) e^{-c_n/u}`. -/
theorem tsum_geo_theta_odd (α : ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' k : ℤ, (k : ℂ) * cexp (2 * π * I * α * k) * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) =
      -(I * ((π * √π / (u * √u) : ℝ) : ℂ)) *
        ∑' n : ℤ, ((((n : ℝ) - α) * rexp (-(geoDual α n / u)) : ℝ) : ℂ) := by
  have hπ := Real.pi_pos
  have key := tsum_mul_exp_shifted_sq (q := 1) one_pos (-α) (u := π ^ 2 / u) (by positivity)
  have hL : ∀ j : ℤ, ((((-α + ((1 : ℕ) : ℝ) * j) *
      rexp (-((-α + ((1 : ℕ) : ℝ) * j) ^ 2 * (π ^ 2 / u)))) : ℝ) : ℂ) =
      ((((j : ℝ) - α) * rexp (-(geoDual α j / u)) : ℝ) : ℂ) := fun j => by
    rw [geoDual]; congr 1; push_cast; congr 1
    · ring
    · congr 1; ring
  have hR : ∀ n : ℤ, (n : ℂ) * cexp (2 * π * I * n * ((-α : ℝ) : ℂ) / ((1 : ℕ) : ℂ)) *
      (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (((1 : ℕ) : ℝ) ^ 2 * (π ^ 2 / u)))) : ℂ) =
      -((((-n : ℤ) : ℂ)) * cexp (2 * π * I * α * ((-n : ℤ) : ℝ)) *
        (rexp (-((((-n : ℤ) : ℝ)) ^ 2 * u)) : ℂ)) := by
    intro n
    rw [show cexp (2 * π * I * n * ((-α : ℝ) : ℂ) / ((1 : ℕ) : ℂ)) =
      cexp (2 * π * I * α * ((-n : ℤ) : ℝ)) by congr 1; push_cast; ring,
      show (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (((1 : ℕ) : ℝ) ^ 2 * (π ^ 2 / u)))) : ℂ) =
      (rexp (-((((-n : ℤ) : ℝ)) ^ 2 * u)) : ℂ) by congr 2; push_cast; field_simp]
    push_cast; ring
  simp only [hL, hR] at key
  rw [tsum_neg, tsum_int_neg (f := fun k : ℤ => (k : ℂ) * cexp (2 * π * I * α * (k : ℝ)) *
    (rexp (-((k : ℝ) ^ 2 * u)) : ℂ))] at key
  rw [key]
  have hsu : 0 < √u := Real.sqrt_pos.2 hu
  have hsπ : 0 < √π := Real.sqrt_pos.2 hπ
  have h1 : √(π / (π ^ 2 / u)) = √u / √π := by
    rw [show π / (π ^ 2 / u) = u / π by field_simp, Real.sqrt_div' _ hπ.le]
  rw [Nat.cast_one, div_one, one_mul, h1]
  generalize (∑' k : ℤ, (k : ℂ) * cexp (2 * π * I * α * (k : ℝ)) *
    (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) = T
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  have hsu' : (√u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsu.ne'
  have hsπ' : (√π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsπ.ne'
  have hπ' : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hπ.ne'
  have hss : (√π : ℂ) * √π = π := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hπ.le]
  have hsu2 : (√u : ℂ) * √u = u := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu.le]
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

/-- `z^k` for `z = e^{2πiα}`. -/
lemma cexp_int_eq_pow (α : ℝ) (k : ℕ) :
    cexp (2 * π * I * α * ((k : ℂ) + 1)) = cexp (2 * π * I * α) ^ (k + 1) := by
  rw [← Complex.exp_natCast_mul]; congr 1; push_cast; ring

lemma cexp_neg_int_eq_inv_pow (α : ℝ) (k : ℕ) :
    cexp (2 * π * I * α * (-((k : ℂ) + 1))) = (cexp (2 * π * I * α) ^ (k + 1))⁻¹ := by
  rw [← cexp_int_eq_pow, ← Complex.exp_neg]; congr 1; ring

/-- **Even half sum**: `∑_{k ≥ 1} C_k e^{-k²u} = ½√(π/u) ∑_{n ∈ ℤ} e^{-c_n/u} - ½`. -/
theorem tsum_geoC_theta (α : ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' k : ℕ, geoC (cexp (2 * π * I * α)) (k + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      -(1 / 2) + ((√π / 2 * u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' n : ℤ, (rexp (-(geoDual α n / u)) : ℂ) := by
  set g : ℤ → ℂ := fun k => cexp (2 * π * I * α * k) * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) with hg
  have hgs : Summable g := by
    refine Summable.of_norm_bounded (Complex.summable_ofReal.2
      (summable_int_exp_neg_mul_sq hu)).norm fun k => le_of_eq ?_
    rw [hg, norm_mul, show 2 * π * I * α * (k : ℂ) = ((2 * π * α * k : ℝ) : ℂ) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Complex.norm_real]
    congr 3; ring
  have h1 : Summable fun n : ℕ => g n := hgs.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ => g (-((n : ℤ) + 1)) :=
    hgs.comp_injective (fun a b h => by simpa using h)
  have key := tsum_geo_theta α hu
  have h1' : Summable fun b : ℕ => g ((b + 1 : ℕ) : ℤ) := h1.comp_injective (add_left_injective 1)
  rw [show (∑' k : ℤ, cexp (2 * π * I * α * k) * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) = ∑' k, g k
    from rfl, tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_eq_zero_add, add_assoc,
    ← h1'.tsum_add h2] at key
  have hterm : ∀ k : ℕ, g ((k + 1 : ℕ) : ℤ) + g (-((k : ℤ) + 1)) =
      2 * (geoC (cexp (2 * π * I * α)) (k + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ)) := by
    intro k
    have e1 := cexp_int_eq_pow α k
    have e2 := cexp_neg_int_eq_inv_pow α k
    simp only [hg]
    push_cast
    rw [neg_sq, e1, e2, geoC]
    ring
  simp only [hterm, tsum_mul_left] at key
  have hg0 : g ((0 : ℕ) : ℤ) = 1 := by simp [hg]
  rw [hg0] at key
  have hsq : √(π / u) = √π * u ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div' _ hu.le, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [hsq] at key
  push_cast at key ⊢
  linear_combination key / 2

/-- **Odd half sum**: `∑_{k ≥ 1} k S_k e^{-k²u} = u^{-3/2} ∑_{n ∈ ℤ} (-i/2) π^{3/2} (n-α) e^{-c_n/u}`. -/
theorem tsum_geoS_theta (α : ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' k : ℕ, (((k : ℂ) + 1) * geoS (cexp (2 * π * I * α)) (k + 1)) *
      (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      ((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ∑' n : ℤ, (-(I / 2 * ((π * √π : ℝ) : ℂ))) *
        ((((n : ℝ) - α) * rexp (-(geoDual α n / u)) : ℝ) : ℂ) := by
  set g : ℤ → ℂ := fun k => (k : ℂ) * cexp (2 * π * I * α * k) * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)
    with hg
  have hgs : Summable g := by
    refine Summable.of_norm_bounded (Complex.summable_ofReal.2
      (summable_int_abs_mul_exp_neg_sq hu)).norm fun k => le_of_eq ?_
    rw [hg, norm_mul, norm_mul, show 2 * π * I * α * (k : ℂ) = ((2 * π * α * k : ℝ) : ℂ) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_pos (Real.exp_pos _)]
  have h1 : Summable fun n : ℕ => g n := hgs.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ => g (-((n : ℤ) + 1)) :=
    hgs.comp_injective (fun a b h => by simpa using h)
  have key := tsum_geo_theta_odd α hu
  have h1' : Summable fun b : ℕ => g ((b + 1 : ℕ) : ℤ) := h1.comp_injective (add_left_injective 1)
  rw [show (∑' k : ℤ, (k : ℂ) * cexp (2 * π * I * α * k) * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) =
    ∑' k, g k from rfl, tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_eq_zero_add, add_assoc,
    ← h1'.tsum_add h2] at key
  have hterm : ∀ k : ℕ, g ((k + 1 : ℕ) : ℤ) + g (-((k : ℤ) + 1)) =
      2 * ((((k : ℂ) + 1) * geoS (cexp (2 * π * I * α)) (k + 1)) *
        (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ)) := by
    intro k
    have e1 := cexp_int_eq_pow α k
    have e2 := cexp_neg_int_eq_inv_pow α k
    simp only [hg]
    push_cast
    rw [neg_sq, e1, e2, geoS]
    ring
  simp only [hterm, tsum_mul_left] at key
  have hg0 : g ((0 : ℕ) : ℤ) = 0 := by simp [hg]
  rw [hg0, zero_add] at key
  have h32 : u ^ (-(3 / 2 : ℝ)) = 1 / (u * √u) := by
    rw [show -(3 / 2 : ℝ) = -(1 + 1 / 2) by norm_num, Real.rpow_neg hu.le, Real.rpow_add hu,
      Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
  rw [← tsum_mul_left, h32]
  have hsu : (√u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  have : ∑' n : ℤ, ((1 / (u * √u) : ℝ) : ℂ) * (-(I / 2 * ((π * √π : ℝ) : ℂ)) *
      ((((n : ℝ) - α) * rexp (-(geoDual α n / u)) : ℝ) : ℂ)) =
      (1 / 2) * (-(I * ((π * √π / (u * √u) : ℝ) : ℂ)) * ∑' n : ℤ,
        ((((n : ℝ) - α) * rexp (-(geoDual α n / u)) : ℝ) : ℂ)) := by
    rw [← tsum_mul_left, ← tsum_mul_left]; congr 1; funext n; push_cast; field_simp
  rw [this, ← key]
  ring

end ZetaF
