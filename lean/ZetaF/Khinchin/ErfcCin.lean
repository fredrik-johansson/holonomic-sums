/-
Copyright (c) 2026. Released under Apache 2.0 license.

# The `erfc` and `Ci` closed form of `J_m` in Theorem 6.3

* `D_{-1/2}(c) = ∫_0^U u^{-3/2} e^{-c/u} du = √(π/c) erfc √(c/U)`, with
  `erfc x = (2/√π) ∫_x^∞ e^{-t²} dt`;
* `∑_{n≥1} (-16c)^n/(n(2n)!) = -2 Cin(4√c)`, with the entire cosine integral
  `Cin x = ∫_0^x (1 - cos t)/t dt` (classically `Cin x = γ + log x - Ci x`, so this is the paper's
  `2(Ci(4√c) - γ - log(4√c))`; that classical identity is not formalized here);
* hence `J = -(2π/√c) erfc(√(c/U)) Cin(4√c) + √π e^{-c/U} 𝓑(c)`, the paper's formula for `J_m`.
-/
import ZetaF.Khinchin.K3Closed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open MeasureTheory Set Filter Real
open scoped Nat Topology

namespace ZetaF.ErfcCin

open ZetaF.StartVals ZetaF.K3Closed

/-! ### `erfc` -/

/-- `∫_x^∞ e^{-t²} dt`. -/
noncomputable def gaussTail (x : ℝ) : ℝ := ∫ t in Ioi x, rexp (-t ^ 2)

/-- The complementary error function `erfc x = (2/√π) ∫_x^∞ e^{-t²} dt`. -/
noncomputable def erfc (x : ℝ) : ℝ := 2 / √π * gaussTail x

lemma integrable_gauss : Integrable fun t : ℝ => rexp (-t ^ 2) := by
  have := integrable_exp_neg_mul_sq (b := 1) one_pos
  simpa using this

lemma gaussTail_eq (x : ℝ) : gaussTail x = √π / 2 - ∫ t in (0 : ℝ)..x, rexp (-t ^ 2) := by
  have h := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := x)
    integrable_gauss.integrableOn integrable_gauss.integrableOn
  have hG : ∫ t in Ioi (0 : ℝ), rexp (-t ^ 2) = √π / 2 := by
    have := integral_gaussian_Ioi 1
    simpa using this
  unfold gaussTail
  linarith

lemma hasDerivAt_gaussTail (x : ℝ) : HasDerivAt gaussTail (-rexp (-x ^ 2)) x := by
  have hc : Continuous fun t : ℝ => rexp (-t ^ 2) := by fun_prop
  have := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have h2 := this.const_sub (√π / 2)
  convert h2 using 1
  ext y; exact gaussTail_eq y

lemma tendsto_gaussTail : Tendsto gaussTail atTop (𝓝 0) := by
  have h := intervalIntegral_tendsto_integral_Ioi (f := fun t : ℝ => rexp (-t ^ 2)) 0
    integrable_gauss.integrableOn tendsto_id
  have hG : ∫ t in Ioi (0 : ℝ), rexp (-t ^ 2) = √π / 2 := by
    have := integral_gaussian_Ioi 1
    simpa using this
  rw [hG] at h
  have := h.const_sub (√π / 2)
  rw [sub_self] at this
  refine this.congr (fun x => ?_)
  rw [gaussTail_eq]; rfl

/-- The antiderivative `(2/√c) ∫_{√c u^{-1/2}}^∞ e^{-t²} dt` of `u^{-3/2} e^{-c/u}`. -/
noncomputable def antiD (c u : ℝ) : ℝ := if 0 < u then 2 / √c * gaussTail (√c * u ^ (-(1 / 2 : ℝ))) else 0

lemma hasDerivAt_antiD {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    HasDerivAt (antiD c) (kx c (-(1 / 2) - 1) u) u := by
  have hr : HasDerivAt (fun u : ℝ => √c * u ^ (-(1 / 2 : ℝ)))
      (√c * ((-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ) - 1))) u :=
    (hasDerivAt_rpow_const (Or.inl hu.ne')).const_mul _
  have h := ((hasDerivAt_gaussTail _).comp u hr).const_mul (2 / √c)
  have hsq : (√c * u ^ (-(1 / 2 : ℝ))) ^ 2 = c / u := by
    rw [mul_pow, sq_sqrt hc.le, ← rpow_natCast, ← rpow_mul hu.le]
    norm_num
    rw [rpow_neg_one, div_eq_mul_inv]
  have hsc : √c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [lt_mem_nhds hu] with v hv
    simp [antiD, hv, Function.comp]
  · rw [kx_of_pos hu, hsq]
    field_simp

lemma continuousOn_antiD {c U : ℝ} (hc : 0 < c) : ContinuousOn (antiD c) (Icc 0 U) := by
  intro u hu
  rcases hu.1.eq_or_lt with h | h
  · subst h
    refine ContinuousWithinAt.mono ?_ (Icc_subset_Ici_self)
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
    have h0 : antiD c 0 = 0 := by simp [antiD]
    rw [h0]
    have ht : Tendsto (fun u : ℝ => √c * u ^ (-(1 / 2 : ℝ))) (𝓝[>] 0) atTop :=
      (tendsto_rpow_neg_nhdsGT_zero (by norm_num)).const_mul_atTop (Real.sqrt_pos.2 hc)
    have := (tendsto_gaussTail.comp ht).const_mul (2 / √c)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v (hv : 0 < v)
    simp [antiD, hv, Function.comp]
  · exact (hasDerivAt_antiD hc h).continuousAt.continuousWithinAt

/-- **`D_{-1/2}(c) = √(π/c) erfc √(c/U)`.** -/
theorem Dint_neg_half {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    Dint c U (-(1 / 2)) = √(π / c) * erfc (√(c / U)) := by
  unfold Dint
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hU.le (continuousOn_antiD hc)
    (fun u hu => hasDerivAt_antiD hc hu.1) (intervalIntegrable_kx hc _ hU.le)]
  have h0 : antiD c 0 = 0 := by simp [antiD]
  have hpt : √c * U ^ (-(1 / 2 : ℝ)) = √(c / U) := by
    rw [rpow_neg hU.le, ← Real.sqrt_eq_rpow, Real.sqrt_div hc.le, div_eq_mul_inv]
  rw [h0, sub_zero]
  simp only [antiD, hU, ite_true, hpt, erfc]
  rw [Real.sqrt_div Real.pi_pos.le]
  have hsc : √c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  have hsp : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp

/-! ### `Cin` -/

/-- The entire cosine integral `Cin x = ∫_0^x (1 - cos t)/t dt`. -/
noncomputable def Cin (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, (1 - Real.cos t) / t

lemma hasSum_one_sub_cos_div (t : ℝ) :
    HasSum (fun n : ℕ => (-1) ^ n * t ^ (2 * n + 1) / ((2 * n + 2)! : ℝ)) ((1 - Real.cos t) / t) := by
  have h := (hasSum_nat_add_iff' 1).2 (Real.hasSum_cos t)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul] at h
  have h2 := (h.neg).div_const t
  rw [show -(Real.cos t - 1) / t = (1 - Real.cos t) / t by ring] at h2
  convert h2 using 1
  ext n
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; simp
  · rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_succ (-1 : ℝ) n,
      show t ^ (2 * n + 2) = t ^ (2 * n + 1) * t by ring]
    field_simp

/-- **`Cin x = ∑_{n≥0} (-1)^n x^{2n+2}/((2n+2)(2n+2)!)`** for `x ≥ 0`. -/
theorem hasSum_Cin {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 2) / ((2 * n + 2 : ℝ) * ((2 * n + 2)! : ℝ)))
      (Cin x) := by
  set F : ℕ → ℝ → ℝ := fun n t => (-1) ^ n * t ^ (2 * n + 1) / ((2 * n + 2)! : ℝ)
  have hcont : ∀ n, Continuous (F n) := fun n => by
    show Continuous fun t : ℝ => (-1 : ℝ) ^ n * t ^ (2 * n + 1) / ((2 * n + 2)! : ℝ)
    fun_prop
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc 0 x)) := fun n =>
    (hcont n).integrableOn_Ioc
  have hpt : ∀ n, ∀ t ∈ Ioc (0 : ℝ) x, ‖F n t‖ = t ^ (2 * n + 1) / ((2 * n + 2)! : ℝ) := by
    intro n t ht
    have hf : (0 : ℝ) < ((2 * n + 2)! : ℝ) := by positivity
    simp only [F]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (pow_pos ht.1 _), abs_of_pos hf]
  have hpow : ∀ n, ∫ t in Ioc 0 x, t ^ (2 * n + 1) / ((2 * n + 2)! : ℝ) =
      x ^ (2 * n + 2) / ((2 * n + 2 : ℝ) * ((2 * n + 2)! : ℝ)) := by
    intro n
    rw [← intervalIntegral.integral_of_le hx, intervalIntegral.integral_div, integral_pow]
    have hf : ((2 * n + 2)! : ℝ) ≠ 0 := by positivity
    have h2 : (2 * n + 2 : ℝ) ≠ 0 := by positivity
    rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring]
    push_cast
    rw [show (2 * (n : ℝ) + 1 + 1) = 2 * n + 2 by ring, zero_pow (by omega), sub_zero, div_div]
  have hnorm_eq : ∀ n, ∫ t in Ioc 0 x, ‖F n t‖ = x ^ (2 * n + 2) / ((2 * n + 2 : ℝ) * ((2 * n + 2)! : ℝ)) := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioc (hpt n), hpow n]
  have hnorm : Summable fun n => ∫ t in Ioc 0 x, ‖F n t‖ := by
    simp_rw [hnorm_eq]
    have hsub : Summable fun n : ℕ => x ^ (2 * n + 2) / ((2 * n + 2)! : ℝ) :=
      (Real.summable_pow_div_factorial x).comp_injective (i := fun n : ℕ => 2 * n + 2)
        (fun a b h => by simp only at h; omega)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsub
    have h1 : (1 : ℝ) ≤ 2 * n + 2 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) h1)
  have hS := hasSum_integral_of_summable_integral_norm hint hnorm
  have hlim : ∫ t in Ioc 0 x, ∑' n, F n t = Cin x := by
    unfold Cin
    rw [intervalIntegral.integral_of_le hx]
    exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => (hasSum_one_sub_cos_div t).tsum_eq)
  rw [hlim] at hS
  convert hS using 1
  ext n
  have : ∫ t in Ioc 0 x, F n t = (-1) ^ n * ∫ t in Ioc 0 x, t ^ (2 * n + 1) / ((2 * n + 2)! : ℝ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [F]; ring
  rw [this, hpow n]
  ring

/-- **`∑_{n≥1} (-16c)^n/(n(2n)!) = -2 Cin(4√c)`** for `c ≥ 0`. -/
theorem hasSum_alpha_series {c : ℝ} (hc : 0 ≤ c) :
    HasSum (fun n : ℕ => (-16 * c) ^ (n + 1) / (((n : ℝ) + 1) * ((2 * (n + 1))! : ℝ)))
      (-2 * Cin (4 * √c)) := by
  have h := (hasSum_Cin (by positivity : 0 ≤ 4 * √c)).mul_left (-2)
  convert h using 1
  ext n
  have hsq : (4 * √c) ^ (2 * n + 2) = (16 * c) ^ (n + 1) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, mul_pow, sq_sqrt hc]; norm_num
  rw [hsq, show 2 * (n + 1) = 2 * n + 2 by ring, show (-16 * c) = (-1) * (16 * c) by ring, mul_pow,
    pow_succ (-1 : ℝ) n]
  have hf : ((2 * n + 2)! : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- **The paper's formula for `J_m`** (Theorem 6.3): for `c, U > 0`,
`J = -(2π/√c) erfc(√(c/U)) Cin(4√c) + √π e^{-c/U} 𝓑(c)`, where `𝓑(c) = ∑_{n≥1} 4^n/(n·n!) β_n(c)`
(and `-Cin(4√c) = Ci(4√c) - γ - log(4√c)`). -/
theorem dualTermK_closed_form {U c : ℝ} (hU : 0 < U) (hc : 0 < c) :
    dualTermK U c = -(2 * π / √c) * erfc (√(c / U)) * Cin (4 * √c) +
      √π * rexp (-(c / U)) * ∑' n : ℕ, gK n * betaS c U (n + 1) := by
  rw [(dualTermK_eq hU hc).2, (hasSum_alpha_series hc.le).tsum_eq, Dint_neg_half hc hU,
    Real.sqrt_div Real.pi_pos.le]
  have hsc : √c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  have hpi : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  rw [show (2 * π / √c) = 2 * (√π * √π) / √c by rw [hpi]]
  field_simp

end ZetaF.ErfcCin
