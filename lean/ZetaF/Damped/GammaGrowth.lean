/-
# Growth estimates for the damped kernel (Section 4.2)

The coefficients `c_j = (-τ)^j/(j! Γ(a_j))`, `a_j = (s - rj)/2`, of the damped kernel have
`|1/Γ(a_j)| ≲ Γ(1 - Re a_j) e^{π|Im a_j|}` (reflection formula), and the series built from them
are controlled by `Γ(β + rj/2)/j! ≤ (j!)^{r'/2 - 1}` for any `r < r' < 2` (log-convexity of `Γ`).
-/
import ZetaF.GammaG1
import ZetaF.GammaUniform

open Complex Filter Topology
open scoped Real Nat

namespace ZetaF

lemma norm_sin_le_exp_abs_im (w : ℂ) : ‖Complex.sin w‖ ≤ rexp |w.im| := by
  rw [Complex.sin]
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  calc ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ / 2
      ≤ (‖Complex.exp (-w * I)‖ + ‖Complex.exp (w * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ = (rexp w.im + rexp (-w.im)) / 2 := by
        rw [Complex.norm_exp, Complex.norm_exp]; simp
    _ ≤ (rexp |w.im| + rexp |w.im|) / 2 := by
        gcongr
        · exact le_abs_self _
        · exact neg_le_abs _
    _ = rexp |w.im| := by ring

/-- **`|1/Γ(z)| ≤ Γ(1 - Re z) e^{π|Im z|}/π` for `Re z < 1`** (reflection formula). -/
theorem norm_inv_Gamma_le_reflect {z : ℂ} (hz : z.re < 1) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ Real.Gamma (1 - z.re) * rexp (π * |z.im|) / π := by
  have hpos : 0 ≤ Real.Gamma (1 - z.re) * rexp (π * |z.im|) / π := by
    have := Real.Gamma_pos_of_pos (show 0 < 1 - z.re by linarith); positivity
  by_cases h : Complex.Gamma z = 0
  · rw [h, inv_zero, norm_zero]; exact hpos
  have h1 : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have href := Complex.Gamma_mul_Gamma_one_sub z
  have hsin : Complex.sin (π * z) ≠ 0 := by
    intro hs; rw [hs, div_zero] at href; exact mul_ne_zero h h1 href
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have key : Complex.Gamma z * (Complex.Gamma (1 - z) * Complex.sin (π * z)) = π := by
    rw [← mul_assoc, href]; field_simp
  have e : (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (π * z) / π := by
    calc (Complex.Gamma z)⁻¹
        = (Complex.Gamma z)⁻¹ * (Complex.Gamma z * (Complex.Gamma (1 - z) *
            Complex.sin (π * z))) / π := by rw [key, mul_div_assoc, div_self hπ, mul_one]
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
  have hG : ‖Complex.Gamma (1 - z)‖ ≤ Real.Gamma (1 - z.re) := by
    have : (1 : ℂ) - z = ((1 - z.re : ℝ) : ℂ) + (-z.im : ℝ) * I := by
      apply Complex.ext <;> simp
    rw [this]; exact norm_Gamma_le_Gamma_re (by linarith) _
  have hS : ‖Complex.sin (π * z)‖ ≤ rexp (π * |z.im|) := by
    refine (norm_sin_le_exp_abs_im _).trans (le_of_eq ?_)
    congr 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  rw [e, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  gcongr

/-- `x^j/(j!)^ε` is summable for `ε > 0` (ratio test). -/
lemma summable_pow_div_factorial_rpow {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    Summable fun j : ℕ => x ^ j / ((j ! : ℕ) : ℝ) ^ ε := by
  rcases hx.lt_or_eq with hx | rfl
  · refine summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
      (Eventually.of_forall fun j => by positivity) ?_
    have e : ∀ j : ℕ, ‖x ^ (j + 1) / (((j + 1) ! : ℕ) : ℝ) ^ ε‖ / ‖x ^ j / ((j ! : ℕ) : ℝ) ^ ε‖ =
        x / ((j : ℝ) + 1) ^ ε := by
      intro j
      have hj : (0 : ℝ) < (j ! : ℕ) := by exact_mod_cast Nat.factorial_pos j
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
        Nat.factorial_succ, Nat.cast_mul, Real.mul_rpow (by positivity) hj.le]
      push_cast
      field_simp
      ring
    simp_rw [e]
    exact tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop hε).comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
  · refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
    simp only [Finset.mem_singleton] at hj
    simp [zero_pow hj]

/-- **Log-convexity**: `Γ(1 + aj) ≤ (j!)^a` for `0 < a < 1`. -/
lemma Gamma_one_add_mul_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    Real.Gamma (1 + a * j) ≤ ((j ! : ℕ) : ℝ) ^ a := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := (j : ℝ) + 1) (t := 1)
    (a := a) (b := 1 - a) (by positivity) one_pos ha0 (by linarith) (by ring)
  rw [Real.Gamma_one, Real.one_rpow, mul_one, Real.Gamma_nat_eq_factorial] at h
  calc Real.Gamma (1 + a * j) = Real.Gamma (a * ((j : ℝ) + 1) + (1 - a)) := by ring_nf
    _ ≤ _ * 1 := h
    _ = _ := mul_one _

/-- Eventually `Γ(β + bj) ≤ Γ(1 + b'j)` for `0 ≤ b < b'`. -/
lemma eventually_Gamma_le {b b' β : ℝ} (hb : 0 < b) (hbb : b < b') :
    ∀ᶠ j : ℕ in atTop, 2 ≤ β + b * j ∧ Real.Gamma (β + b * j) ≤ Real.Gamma (1 + b' * j) := by
  obtain ⟨J, hJ⟩ := exists_nat_ge (max ((2 - β) / b) ((β - 1) / (b' - b)))
  filter_upwards [eventually_ge_atTop J] with j hj
  have hj' : (J : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : (2 - β) / b ≤ j := (le_max_left _ _).trans (hJ.trans hj')
  have h2 : (β - 1) / (b' - b) ≤ j := (le_max_right _ _).trans (hJ.trans hj')
  rw [div_le_iff₀ hb] at h1
  rw [div_le_iff₀ (by linarith)] at h2
  refine ⟨by linarith, ?_⟩
  apply Real.Gamma_strictMonoOn_Ici.monotoneOn
  · show 2 ≤ β + b * j; linarith
  · show 2 ≤ 1 + b' * j; nlinarith
  · nlinarith

/-- **`ρ^j Γ(β + bj)/j!` is summable for `0 < b < 1`.** -/
theorem summable_pow_mul_Gamma_div_factorial {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (β : ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Summable fun j : ℕ => ρ ^ j * Real.Gamma (β + b * j) / ((j ! : ℕ) : ℝ) := by
  set b' := (b + 1) / 2
  have hb' : b < b' := by simp only [b']; linarith
  have hb'1 : b' < 1 := by simp only [b']; linarith
  refine Summable.of_norm_bounded_eventually_nat
    (summable_pow_div_factorial_rpow hρ (show 0 < 1 - b' by linarith)) ?_
  filter_upwards [eventually_Gamma_le (β := β) hb0 hb', eventually_ge_atTop 1] with j hj hj1
  have hf : (0 : ℝ) < (j ! : ℕ) := by exact_mod_cast Nat.factorial_pos j
  have hG : 0 < Real.Gamma (β + b * j) := Real.Gamma_pos_of_pos (by linarith [hj.1])
  rw [Real.norm_of_nonneg (by positivity)]
  calc ρ ^ j * Real.Gamma (β + b * j) / ((j ! : ℕ) : ℝ)
      ≤ ρ ^ j * ((j ! : ℕ) : ℝ) ^ b' / ((j ! : ℕ) : ℝ) := by
        gcongr; exact hj.2.trans (Gamma_one_add_mul_le (by linarith) hb'1 j)
    _ = ρ ^ j / ((j ! : ℕ) : ℝ) ^ (1 - b') := by
        rw [Real.rpow_sub hf, Real.rpow_one]; field_simp
/-- **`ρ^j Γ(β + bj) Γ(β' + bj)/j!` is summable for `0 < b < 1/2`.** -/
theorem summable_pow_mul_Gamma_sq_div_factorial {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (β β' : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Summable fun j : ℕ =>
      ρ ^ j * (Real.Gamma (β + b * j) * Real.Gamma (β' + b * j)) / ((j ! : ℕ) : ℝ) := by
  set b' := (b + 1 / 2) / 2
  have hb' : b < b' := by simp only [b']; linarith
  have hb'1 : b' < 1 / 2 := by simp only [b']; linarith
  refine Summable.of_norm_bounded_eventually_nat
    (summable_pow_div_factorial_rpow hρ (show 0 < 1 - 2 * b' by linarith)) ?_
  filter_upwards [eventually_Gamma_le (β := β) hb0 hb', eventually_Gamma_le (β := β') hb0 hb']
    with j hj hj'
  have hf : (0 : ℝ) < (j ! : ℕ) := by exact_mod_cast Nat.factorial_pos j
  have hG : 0 < Real.Gamma (β + b * j) := Real.Gamma_pos_of_pos (by linarith [hj.1])
  have hG' : 0 < Real.Gamma (β' + b * j) := Real.Gamma_pos_of_pos (by linarith [hj'.1])
  have hJ := Gamma_one_add_mul_le (show 0 < b' by linarith) (by linarith) j
  rw [Real.norm_of_nonneg (by positivity)]
  calc ρ ^ j * (Real.Gamma (β + b * j) * Real.Gamma (β' + b * j)) / ((j ! : ℕ) : ℝ)
      ≤ ρ ^ j * (((j ! : ℕ) : ℝ) ^ b' * ((j ! : ℕ) : ℝ) ^ b') / ((j ! : ℕ) : ℝ) := by
        gcongr
        · exact hj.2.trans hJ
        · exact hj'.2.trans hJ
    _ = ρ ^ j / ((j ! : ℕ) : ℝ) ^ (1 - 2 * b') := by
        rw [← Real.rpow_add hf, Real.rpow_sub hf, Real.rpow_one]; ring_nf; field_simp

end ZetaF
