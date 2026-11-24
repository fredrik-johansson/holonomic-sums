/-
# The damped kernel and the termwise forms of `I_k` and `J_m` (Proposition 4.2)

For `Λ(s; τ, r) = ∑ e^{-τk^r} k^{-s}` the paper uses the kernel
`h_s(u) = ∑_j c_j u^{a_j - 1}`, `a_j = (s - rj)/2`, `c_j = (-τ)^j/(j! Γ(a_j))`.
We prove:
* the `k`-terms `I_k = ∫_{u₀}^∞ e^{-k²u} h_s` are the series `∑_j c_j ∫_{u₀}^∞ e^{-k²u} u^{a_j-1}`
  for `0 < r < 2` (`hasSum_kTerm_damped`);
* the dual terms `J_m = ∫₀^{u₀} u^{-1/2} e^{-π²m²/u} h_s` are the series
  `∑_j c_j D_{a_j-1/2}(π²m²)` for `0 < r < 1` (`hasSum_dualTerm_damped`).

The second statement is where the paper needed a correction: its `j`-th term is of size
`(τ (πm)^{-r})^j Γ(rj/2)²/j!`, which grows like `(j!)^{r-1}` for `r > 1`, so the series diverges for
`1 < r < 2` (and for `r = 1`, `τ ≥ 2πm`).  Our bound `Γ(β + rj/2)Γ(β' + rj/2)/j!` makes the
restriction `r < 1` visible.
-/
import ZetaF.Damped.GammaGrowth
import ZetaF.Continuation.Basic

open MeasureTheory Set Filter
open scoped Real Nat Topology

namespace ZetaF

/-- `a_j = (s - rj)/2`. -/
noncomputable def dExp (s : ℂ) (r : ℝ) (j : ℕ) : ℂ := (s - r * j) / 2

/-- `c_j = (-τ)^j/(j! Γ(a_j))`. -/
noncomputable def dCoeff (τ r : ℝ) (s : ℂ) (j : ℕ) : ℂ :=
  (((-τ) ^ j / (j ! : ℕ) : ℝ) : ℂ) * (Complex.Gamma (dExp s r j))⁻¹

/-- The kernel of `e^{-τx^r} x^{-s}`: `h_s(u) = ∑_j c_j u^{a_j - 1}`. -/
noncomputable def dampedKernel (τ r : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  ∑' j, dCoeff τ r s j * (u : ℂ) ^ (dExp s r j - 1)

lemma dExp_re (s : ℂ) (r : ℝ) (j : ℕ) : (dExp s r j).re = s.re / 2 - r / 2 * j := by
  simp [dExp]; ring

lemma dExp_im (s : ℂ) (r : ℝ) (j : ℕ) : (dExp s r j).im = s.im / 2 := by
  simp [dExp]

/-- `|c_j| ≤ |τ|^j Γ(1 - Re s/2 + rj/2) e^{π|Im s|/2}/(π j!)` once `Re a_j < 1`. -/
lemma norm_dCoeff_le {τ r : ℝ} {s : ℂ} {j : ℕ} (hj : (dExp s r j).re < 1) :
    ‖dCoeff τ r s j‖ ≤ (rexp (π * |s.im / 2|) / π) *
      (|τ| ^ j * Real.Gamma ((1 - s.re / 2) + r / 2 * j) / ((j ! : ℕ) : ℝ)) := by
  have h := norm_inv_Gamma_le_reflect hj
  rw [dExp_re, dExp_im] at h
  unfold dCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg,
    Nat.abs_cast]
  have hf : (0 : ℝ) < (j ! : ℕ) := by exact_mod_cast Nat.factorial_pos j
  have e : 1 - (s.re / 2 - r / 2 * j) = (1 - s.re / 2) + r / 2 * j := by ring
  rw [e] at h
  calc |τ| ^ j / ((j ! : ℕ) : ℝ) * ‖(Complex.Gamma (dExp s r j))⁻¹‖
      ≤ |τ| ^ j / ((j ! : ℕ) : ℝ) *
        (Real.Gamma ((1 - s.re / 2) + r / 2 * j) * rexp (π * |s.im / 2|) / π) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

lemma eventually_dExp_re_lt {r : ℝ} (hr : 0 < r) (s : ℂ) (c : ℝ) :
    ∀ᶠ j : ℕ in atTop, (dExp s r j).re < c := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ((s.re / 2 - c) / (r / 2))
  filter_upwards [eventually_ge_atTop J] with j hj
  have hj' : (J : ℝ) ≤ j := by exact_mod_cast hj
  rw [dExp_re]
  rw [div_lt_iff₀ (by positivity)] at hJ
  nlinarith

/-! ### The `k`-terms -/

/-- **`I_k` termwise, for `0 < r < 2`.** -/
theorem hasSum_kTerm_damped {τ r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) (s : ℂ) {u₀ : ℝ}
    (hu₀ : 0 < u₀) {k : ℕ} (hk : 0 < k) :
    HasSum (fun j => dCoeff τ r s j * upperLaplace ((k : ℝ) ^ 2) u₀ (dExp s r j))
      (kTerm (dampedKernel τ r s) u₀ k) := by
  have hκ : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  set F : ℕ → ℝ → ℂ := fun j u =>
    dCoeff τ r s j * ((u : ℂ) ^ (dExp s r j - 1) * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ))
  have hint : ∀ j, IntegrableOn (F j) (Ioi u₀) := fun j =>
    (integrableOn_upperLaplace hκ hu₀ _).const_mul _
  set K := ∫ u in Ioi u₀, rexp (-(k : ℝ) ^ 2 * u)
  have hexpint : IntegrableOn (fun u : ℝ => rexp (-(k : ℝ) ^ 2 * u)) (Ioi u₀) :=
    exp_neg_integrableOn_Ioi u₀ hκ
  have hnorm : ∀ j, (dExp s r j).re ≤ 1 → ∫ u in Ioi u₀, ‖F j u‖ ≤
      ‖dCoeff τ r s j‖ * u₀ ^ ((dExp s r j).re - 1) * K := by
    intro j hj
    rw [mul_assoc, ← integral_const_mul, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg (F j u))
      ((hexpint.const_mul _).const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu' : 0 < u := hu₀.trans hu
    simp only [F]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu', Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    simp only [Complex.sub_re, Complex.one_re]
    have h1 : u ^ ((dExp s r j).re - 1) ≤ u₀ ^ ((dExp s r j).re - 1) :=
      Real.rpow_le_rpow_of_nonpos hu₀ (le_of_lt (show u₀ < u from hu)) (by linarith)
    have : rexp (-((k : ℝ) ^ 2 * u)) = rexp (-(k : ℝ) ^ 2 * u) := by ring_nf
    rw [this]
    calc ‖dCoeff τ r s j‖ * (u ^ ((dExp s r j).re - 1) * rexp (-(k : ℝ) ^ 2 * u))
        ≤ ‖dCoeff τ r s j‖ * (u₀ ^ ((dExp s r j).re - 1) * rexp (-(k : ℝ) ^ 2 * u)) := by
          gcongr
      _ = _ := by ring
  have hsum : Summable fun j => ∫ u in Ioi u₀, ‖F j u‖ := by
    set C := (rexp (π * |s.im / 2|) / π) * u₀ ^ (s.re / 2 - 1) * K
    have hK : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun _ _ => (Real.exp_pos _).le
    refine Summable.of_norm_bounded_eventually_nat
      ((summable_pow_mul_Gamma_div_factorial (b := r / 2) (by positivity) (by linarith)
        (1 - s.re / 2) (ρ := |τ| * u₀ ^ (-(r / 2))) (by positivity)).mul_left C) ?_
    filter_upwards [eventually_dExp_re_lt hr0 s 1] with j hj
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    refine (hnorm j hj.le).trans ?_
    have hc := norm_dCoeff_le (τ := τ) hj
    have hpow : u₀ ^ ((dExp s r j).re - 1) = u₀ ^ (s.re / 2 - 1) * (u₀ ^ (-(r / 2))) ^ j := by
      rw [dExp_re, ← Real.rpow_natCast, ← Real.rpow_mul hu₀.le, ← Real.rpow_add hu₀]
      congr 1; ring
    rw [hpow]
    have hp : 0 ≤ u₀ ^ (s.re / 2 - 1) * (u₀ ^ (-(r / 2))) ^ j := by positivity
    calc ‖dCoeff τ r s j‖ * (u₀ ^ (s.re / 2 - 1) * (u₀ ^ (-(r / 2))) ^ j) * K
        ≤ (rexp (π * |s.im / 2|) / π) *
            (|τ| ^ j * Real.Gamma ((1 - s.re / 2) + r / 2 * j) / ((j ! : ℕ) : ℝ)) *
            (u₀ ^ (s.re / 2 - 1) * (u₀ ^ (-(r / 2))) ^ j) * K := by gcongr
      _ = C * ((|τ| * u₀ ^ (-(r / 2))) ^ j * Real.Gamma ((1 - s.re / 2) + r / 2 * j) /
            ((j ! : ℕ) : ℝ)) := by simp only [C]; rw [mul_pow]; ring
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext j; simp only [F]; rw [integral_const_mul]; rfl
  · unfold kTerm dampedKernel
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [F]
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring

/-! ### The dual terms -/

/-- `u^b e^{-c/u} ≤ Γ(1 - b) c^b` for `b < 0`, `c, u > 0`. -/
lemma rpow_mul_exp_le_Gamma {b c u : ℝ} (hb : b < 0) (hc : 0 < c) (hu : 0 < u) :
    u ^ b * rexp (-(c / u)) ≤ Real.Gamma (1 - b) * c ^ b := by
  have h := rpow_le_exp_mul_Gamma (x := -b) (y := c / u) (by linarith) (by positivity)
  rw [show -b + 1 = 1 - b by ring] at h
  have hcb : 0 < c ^ b := Real.rpow_pos_of_pos hc b
  have hub : 0 < u ^ b := Real.rpow_pos_of_pos hu b
  have e1 : u ^ b = (c / u) ^ (-b) * c ^ b := by
    rw [Real.div_rpow hc.le hu.le, Real.rpow_neg hc.le, Real.rpow_neg hu.le]
    field_simp
  calc u ^ b * rexp (-(c / u)) = (c / u) ^ (-b) * rexp (-(c / u)) * c ^ b := by rw [e1]; ring
    _ ≤ (rexp (c / u) * Real.Gamma (1 - b)) * rexp (-(c / u)) * c ^ b := by gcongr
    _ = Real.Gamma (1 - b) * c ^ b := by
        rw [Real.exp_neg]; field_simp

/-- **`J_m` termwise, for `0 < r < 1`** (the corrected Proposition 4.2). -/
theorem hasSum_dualTerm_damped {τ r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (s : ℂ) {u₀ : ℝ}
    (hu₀ : 0 < u₀) {m : ℕ} (hm : 0 < m) :
    HasSum (fun j => dCoeff τ r s j * lowerDual (π ^ 2 * (m : ℝ) ^ 2) u₀ (dExp s r j))
      (dualTerm (dampedKernel τ r s) u₀ m) := by
  set c := π ^ 2 * (m : ℝ) ^ 2 with hc_def
  have hc : 0 < c := by positivity
  set G : ℕ → ℝ → ℂ := fun j u =>
    dCoeff τ r s j * ((u : ℂ) ^ (dExp s r j - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ))
  have hint : ∀ j, IntegrableOn (G j) (Ioc 0 u₀) := fun j =>
    (integrableOn_lowerDual hc hu₀ _).const_mul _
  have hnorm : ∀ j, (dExp s r j).re < 1 / 2 → ∫ u in Ioc 0 u₀, ‖G j u‖ ≤
      ‖dCoeff τ r s j‖ * (u₀ * (Real.Gamma (5 / 2 - (dExp s r j).re) *
        c ^ ((dExp s r j).re - 3 / 2))) := by
    intro j hj
    have hb : (dExp s r j).re - 3 / 2 < 0 := by linarith
    calc ∫ u in Ioc 0 u₀, ‖G j u‖ ≤ ∫ u in Ioc 0 u₀, ‖dCoeff τ r s j‖ *
          (Real.Gamma (5 / 2 - (dExp s r j).re) * c ^ ((dExp s r j).re - 3 / 2)) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (integrableOn_const (by simp) eNorm_ne_top) ?_
          refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
          have hu1 := hu.1
          simp only [G]
          rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu1, Complex.norm_real,
            Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu1.le _) (Real.exp_pos _).le)]
          simp only [Complex.sub_re, Complex.one_re]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h := rpow_mul_exp_le_Gamma hb hc hu1
          rw [show 1 - ((dExp s r j).re - 3 / 2) = 5 / 2 - (dExp s r j).re by ring] at h
          calc u ^ ((dExp s r j).re - 1) * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)))
              = u ^ ((dExp s r j).re - 3 / 2) * rexp (-(c / u)) := by
                rw [← mul_assoc, ← Real.rpow_add hu1]; ring_nf
            _ ≤ _ := h
      _ = _ := by
          rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
            ENNReal.toReal_ofReal hu₀.le, smul_eq_mul]; ring
  have hsum : Summable fun j => ∫ u in Ioc 0 u₀, ‖G j u‖ := by
    set C := (rexp (π * |s.im / 2|) / π) * u₀ * c ^ (s.re / 2 - 3 / 2)
    refine Summable.of_norm_bounded_eventually_nat
      ((summable_pow_mul_Gamma_sq_div_factorial (b := r / 2) (by positivity) (by linarith)
        (1 - s.re / 2) (5 / 2 - s.re / 2) (ρ := |τ| * c ^ (-(r / 2))) (by positivity)).mul_left C) ?_
    filter_upwards [eventually_dExp_re_lt hr0 s (1 / 2)] with j hj
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    refine (hnorm j hj).trans ?_
    have hcoef := norm_dCoeff_le (τ := τ) (show (dExp s r j).re < 1 by linarith)
    have hpow : c ^ ((dExp s r j).re - 3 / 2) = c ^ (s.re / 2 - 3 / 2) * (c ^ (-(r / 2))) ^ j := by
      rw [dExp_re, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_add hc]
      congr 1; ring
    have hG : 5 / 2 - (dExp s r j).re = (5 / 2 - s.re / 2) + r / 2 * j := by rw [dExp_re]; ring
    rw [hpow, hG]
    have hΓ : 0 < Real.Gamma ((5 / 2 - s.re / 2) + r / 2 * j) :=
      Real.Gamma_pos_of_pos (by rw [← hG]; linarith)
    calc ‖dCoeff τ r s j‖ * (u₀ * (Real.Gamma ((5 / 2 - s.re / 2) + r / 2 * j) *
          (c ^ (s.re / 2 - 3 / 2) * (c ^ (-(r / 2))) ^ j)))
        ≤ (rexp (π * |s.im / 2|) / π) *
            (|τ| ^ j * Real.Gamma ((1 - s.re / 2) + r / 2 * j) / ((j ! : ℕ) : ℝ)) *
          (u₀ * (Real.Gamma ((5 / 2 - s.re / 2) + r / 2 * j) *
            (c ^ (s.re / 2 - 3 / 2) * (c ^ (-(r / 2))) ^ j))) := by gcongr
      _ = C * ((|τ| * c ^ (-(r / 2))) ^ j * (Real.Gamma ((1 - s.re / 2) + r / 2 * j) *
            Real.Gamma ((5 / 2 - s.re / 2) + r / 2 * j)) / ((j ! : ℕ) : ℝ)) := by
          simp only [C]; rw [mul_pow]; ring
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext j; simp only [G]; rw [integral_const_mul]; rfl
  · unfold dualTerm dampedKernel
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [G]
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring

end ZetaF
