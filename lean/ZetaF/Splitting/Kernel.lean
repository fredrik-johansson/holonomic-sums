/-
# The kernel `h_s` (paper §3.2, eq. (6)) and its basic properties

`h_s(u) = ∑_{n ≥ 0} a_n u^{(s+n)/2 - 1} / Γ((s+n)/2)`.

For `|a_n| ≤ C R^n` and `Re s > 0` we prove:
* termwise bounds by the real majorant `∑ D R^n u^{(σ+n)/2-1}/Γ((σ+n)/2)`, `σ = Re s`;
* continuity of `h_s` on `(0, ∞)`;
* the Laplace representation (eq. (7)): `k^{-s} f(1/k) = ∫₀^∞ e^{-k²u} h_s(u) du` for `k > R`;
* the integrability hypotheses of the abstract splitting (`theta_split`), for `Re s > 1`.
-/
import ZetaF.GammaBounds
import ZetaF.IntegralTools
import ZetaF.Splitting.Abstract
import ZetaF.Regular

set_option autoImplicit false
open MeasureTheory Set Filter Finset
open Real (pi_pos sqrt_eq_rpow)
open scoped Real

namespace ZetaF

/-- A term of the kernel: `a_n u^{(s+n)/2-1}/Γ((s+n)/2)`. -/
noncomputable def kernelTerm (a : ℕ → ℂ) (s : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  a n * (Complex.Gamma ((s + n) / 2))⁻¹ * (u : ℂ) ^ ((s + n) / 2 - 1)

/-- The kernel `h_s(u) = ∑_n a_n u^{(s+n)/2-1}/Γ((s+n)/2)` (eq. (6)). -/
noncomputable def kernel (a : ℕ → ℂ) (s : ℂ) (u : ℝ) : ℂ := ∑' n, kernelTerm a s n u

/-- Coefficients of the real majorant. -/
noncomputable def majCoeff (D R σ : ℝ) (n : ℕ) : ℝ := D * R ^ n / Real.Gamma ((σ + n) / 2)

variable {a : ℕ → ℂ} {s : ℂ} {R : ℝ}

lemma majCoeff_nonneg {D R σ : ℝ} (hD : 0 ≤ D) (hR : 0 ≤ R) (hσ : 0 < σ) (n : ℕ) :
    0 ≤ majCoeff D R σ n :=
  div_nonneg (mul_nonneg hD (pow_nonneg hR n)) (Real.Gamma_pos_of_pos (by positivity)).le

lemma norm_kernelTerm {u : ℝ} (hu : 0 < u) (n : ℕ) :
    ‖kernelTerm a s n u‖ = ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * u ^ ((s.re + n) / 2 - 1) := by
  rw [kernelTerm, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
  congr 2; simp

lemma exists_coeff_bound (ha : GeomBounded a R) (hs : 0 < s.re) :
    ∃ D, 0 ≤ D ∧ ∀ n : ℕ, ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ ≤ majCoeff D R s.re n := by
  obtain ⟨C, hC⟩ := ha
  obtain ⟨B, hB0, hB⟩ := norm_inv_Gamma_half_le hs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hC 0)
  refine ⟨C * B, mul_nonneg hC0 hB0, fun n => ?_⟩
  have hG := Real.Gamma_pos_of_pos (show 0 < (s.re + n) / 2 by positivity)
  unfold majCoeff
  rw [le_div_iff₀ hG]
  calc ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * Real.Gamma ((s.re + n) / 2)
      = ‖a n‖ * (‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * Real.Gamma ((s.re + n) / 2)) := by ring
    _ ≤ (C * R ^ n) * B := mul_le_mul (hC n) (hB n) (by positivity) ((norm_nonneg _).trans (hC n))
    _ = C * B * R ^ n := by ring

lemma rpow_half_eq {u : ℝ} (hu : 0 < u) (σ : ℝ) (n : ℕ) :
    u ^ ((σ + n) / 2 - 1) = u ^ (σ / 2 - 1) * (√u) ^ n := by
  rw [sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu.le, ← Real.rpow_add hu]
  congr 1; ring

lemma summable_maj {D σ u : ℝ} (hR : 0 ≤ R) (hσ : 0 < σ) (hu : 0 < u) :
    Summable fun n : ℕ => majCoeff D R σ n * u ^ ((σ + n) / 2 - 1) := by
  refine ((summable_pow_div_Gamma_half hσ (q := R * √u) (by positivity)).mul_left
    (D * u ^ (σ / 2 - 1))).congr fun n => ?_
  rw [rpow_half_eq hu, majCoeff, mul_pow]; ring

lemma summable_majCoeff_mul_pow {D σ q : ℝ} (hR : 0 ≤ R) (hσ : 0 < σ) (hq : 0 ≤ q) :
    Summable fun n : ℕ => majCoeff D R σ n * q ^ n := by
  refine ((summable_pow_div_Gamma_half hσ (q := R * q) (by positivity)).mul_left D).congr
    fun n => ?_
  rw [majCoeff, mul_pow]; ring

lemma norm_kernelTerm_le {D u : ℝ} (hD : ∀ n : ℕ, ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ ≤
    majCoeff D R s.re n) (hu : 0 < u) (n : ℕ) :
    ‖kernelTerm a s n u‖ ≤ majCoeff D R s.re n * u ^ ((s.re + n) / 2 - 1) := by
  rw [norm_kernelTerm hu]
  exact mul_le_mul_of_nonneg_right (hD n) (Real.rpow_nonneg hu.le _)

lemma continuousOn_kernelTerm (n : ℕ) : ContinuousOn (kernelTerm a s n) (Ioi 0) := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  unfold kernelTerm
  apply continuousAt_const.mul
  exact (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
    (Complex.ofReal_mem_slitPlane.2 hu)

/-- `h_s` is continuous on `(0, ∞)`. -/
lemma continuousOn_kernel (ha : GeomBounded a R) (hR : 0 ≤ R) (hs : 0 < s.re) :
    ContinuousOn (kernel a s) (Ioi 0) := by
  obtain ⟨D, hD0, hD⟩ := exists_coeff_bound ha hs
  intro u hu
  have hu : 0 < u := hu
  -- work on the neighbourhood `[u/2, 2u]`
  have hloc : ContinuousOn (kernel a s) (Icc (u / 2) (2 * u)) := by
    set c := (u / 2) ^ (s.re / 2 - 1) + (2 * u) ^ (s.re / 2 - 1)
    refine continuousOn_tsum (u := fun n => majCoeff D R s.re n * (c * (√(2 * u)) ^ n))
      (fun n => (continuousOn_kernelTerm n).mono fun v hv => lt_of_lt_of_le (by positivity) hv.1)
      ?_ fun n v hv => ?_
    · refine ((summable_majCoeff_mul_pow (D := D) (σ := s.re) (q := √(2 * u)) hR hs
        (Real.sqrt_nonneg _)).mul_left c).congr fun n => ?_
      ring
    · have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv.1
      refine (norm_kernelTerm_le hD hv0 n).trans ?_
      apply mul_le_mul_of_nonneg_left _ (majCoeff_nonneg hD0 hR hs n)
      rw [rpow_half_eq hv0]
      apply mul_le_mul _ (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hv.2) n)
        (by positivity) (by positivity)
      rcases le_or_gt 0 (s.re / 2 - 1) with h | h
      · exact (Real.rpow_le_rpow hv0.le hv.2 h).trans (le_add_of_nonneg_left (by positivity))
      · exact (Real.rpow_le_rpow_of_nonpos (by positivity) hv.1 h.le).trans
          (le_add_of_nonneg_right (by positivity))
  exact (hloc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt

/-! ### Laplace transforms of the terms -/

lemma one_div_sq_cpow {k : ℝ} (hk : 0 < k) (w : ℂ) :
    (1 / ((k ^ 2 : ℝ) : ℂ)) ^ w = (k : ℂ) ^ (-2 * w) := by
  have h1 : (1 / ((k ^ 2 : ℝ) : ℂ)) = ((k ^ (-2 : ℝ) : ℝ) : ℂ) := by
    rw [Real.rpow_neg hk.le]; push_cast; simp
  rw [h1, ← Complex.cpow_mul_ofReal_nonneg hk.le]; push_cast; ring_nf

lemma one_div_sq_rpow {k : ℝ} (hk : 0 < k) (σ : ℝ) (n : ℕ) :
    (1 / k ^ 2) ^ ((σ + n) / 2) = (1 / k) ^ σ * (1 / k) ^ n := by
  rw [show (1 / k ^ 2) = (1 / k) ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
    ← Real.rpow_mul (by positivity), ← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
  congr 1; ring

lemma integrableOn_rpow_mul_exp {x κ : ℝ} (hx : 0 < x) (hκ : 0 < κ) :
    IntegrableOn (fun u : ℝ => u ^ (x - 1) * rexp (-(κ * u))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := x - 1) (p := 1) (b := κ) (by linarith)
    one_pos hκ
  refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

lemma laplace_kernelTerm {k : ℝ} (hk : 0 < k) (hs : 0 < s.re) (n : ℕ) :
    ∫ u in Ioi 0, (rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u = a n * (k : ℂ) ^ (-(s + n)) := by
  have hw : 0 < ((s + n) / 2).re := by simp; positivity
  have hG : Complex.Gamma ((s + n) / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have e : ∀ u : ℝ, (rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u =
      (a n * (Complex.Gamma ((s + n) / 2))⁻¹) *
        ((u : ℂ) ^ ((s + n) / 2 - 1) * Complex.exp (-(((k ^ 2 : ℝ) : ℂ) * u))) := by
    intro u; unfold kernelTerm; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hw (by positivity),
    one_div_sq_cpow hk]
  field_simp

lemma integrableOn_exp_mul_kernelTerm {k : ℝ} (hk : 0 < k) (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun u => (rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u) (Ioi 0) := by
  have hx : 0 < (s.re + n) / 2 := by positivity
  refine Integrable.mono' ((integrableOn_rpow_mul_exp hx (by positivity : 0 < k ^ 2)).const_mul
    (‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun u : ℝ =>
      rexp (-(k ^ 2 * u)))).continuousOn.mul (continuousOn_kernelTerm n)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      norm_kernelTerm (a := a) hu]
    apply le_of_eq; ring

lemma integral_norm_exp_mul_kernelTerm_le {D k : ℝ} (hk : 0 < k) (hs : 0 < s.re)
    (hD : ∀ n : ℕ, ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ ≤ majCoeff D R s.re n) (n : ℕ) :
    ∫ u in Ioi 0, ‖(rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u‖ ≤
      D * (1 / k) ^ s.re * (R / k) ^ n := by
  have hx : 0 < (s.re + n) / 2 := by positivity
  have e : ∀ u ∈ Ioi (0 : ℝ), ‖(rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u‖ =
      (‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖) * (u ^ ((s.re + n) / 2 - 1) * rexp (-(k ^ 2 * u))) := by
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      norm_kernelTerm (a := a) hu]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hx (by positivity), one_div_sq_rpow hk]
  have hG := Real.Gamma_pos_of_pos hx
  calc ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ((1 / k) ^ s.re * (1 / k) ^ n *
        Real.Gamma ((s.re + n) / 2))
      ≤ majCoeff D R s.re n * ((1 / k) ^ s.re * (1 / k) ^ n * Real.Gamma ((s.re + n) / 2)) :=
        mul_le_mul_of_nonneg_right (hD n) (by positivity)
    _ = D * (1 / k) ^ s.re * (R / k) ^ n := by
        unfold majCoeff; simp only [div_pow, one_pow]; field_simp

/-- **Laplace representation (7)**: for `k > R`,
`∑_n a_n k^{-s-n} = ∫₀^∞ e^{-k²u} h_s(u) du`. -/
theorem hasSum_laplace_kernel (ha : GeomBounded a R) (hR : 0 ≤ R) (hs : 0 < s.re) {k : ℝ}
    (hk : R < k) :
    HasSum (fun n => a n * (k : ℂ) ^ (-(s + n)))
      (∫ u in Ioi 0, (rexp (-(k ^ 2 * u)) : ℂ) * kernel a s u) := by
  have hk0 : 0 < k := lt_of_le_of_lt hR hk
  obtain ⟨D, hD0, hD⟩ := exists_coeff_bound ha hs
  have hsum : Summable fun n => ∫ u in Ioi 0, ‖(rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (integral_norm_exp_mul_kernelTerm_le hk0 hs hD)
      ((summable_geometric_of_lt_one (div_nonneg hR hk0.le) ((div_lt_one hk0).2 hk)).mul_left _)
  have := hasSum_integral_of_summable_integral_norm
    (fun n => integrableOn_exp_mul_kernelTerm (a := a) hk0 hs n) hsum
  simp only [laplace_kernelTerm hk0 hs] at this
  convert this using 2
  funext u
  exact (tsum_mul_left (f := fun i => kernelTerm a s i u)).symm

/-! ### The integrability hypotheses of the abstract splitting -/

lemma integrableOn_exp_mul_norm_kernel (ha : GeomBounded a R) (hR : 0 ≤ R) (hs : 0 < s.re)
    {k : ℝ} (hk : R < k) :
    IntegrableOn (fun u => rexp (-(k ^ 2 * u)) * ‖kernel a s u‖) (Ioi 0) := by
  have hk0 : 0 < k := lt_of_le_of_lt hR hk
  obtain ⟨D, hD0, hD⟩ := exists_coeff_bound ha hs
  set g : ℕ → ℝ → ℝ := fun n u => majCoeff D R s.re n * (u ^ ((s.re + n) / 2 - 1) *
    rexp (-(k ^ 2 * u))) with hg
  have hgint : Integrable (fun u => ∑' n, g n u) (volume.restrict (Ioi 0)) := by
    refine integrable_tsum_of_nonneg
      (fun n => (integrableOn_rpow_mul_exp (by positivity) (by positivity)).const_mul _) ?_ ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu n => ?_)
      exact mul_nonneg (majCoeff_nonneg hD0 hR hs n)
        (mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (Real.exp_pos _).le)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      exact ((summable_maj (D := D) hR hs hu).mul_right (rexp (-(k ^ 2 * u)))).congr
        fun n => by simp only [hg]; ring
    · refine ((summable_geometric_of_lt_one (div_nonneg hR hk0.le)
        ((div_lt_one hk0).2 hk)).mul_left (D * (1 / k) ^ s.re)).congr fun n => ?_
      simp only [hg]
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity)
        (by positivity), one_div_sq_rpow hk0]
      have hG := Real.Gamma_pos_of_pos (show 0 < (s.re + n) / 2 by positivity)
      unfold majCoeff; simp only [div_pow, one_pow]; field_simp
  refine Integrable.mono' hgint ?_ ?_
  · exact ((by fun_prop : Continuous fun u : ℝ => rexp (-(k ^ 2 * u))).continuousOn.mul
      (continuousOn_kernel ha hR hs).norm).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu : 0 < u := hu
    have hsm := summable_maj (D := D) hR hs hu
    rw [Real.norm_of_nonneg (by positivity)]
    calc rexp (-(k ^ 2 * u)) * ‖kernel a s u‖
        ≤ rexp (-(k ^ 2 * u)) * ∑' n, majCoeff D R s.re n * u ^ ((s.re + n) / 2 - 1) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact tsum_of_norm_bounded hsm.hasSum (norm_kernelTerm_le hD hu)
      _ = ∑' n, g n u := by
          rw [← tsum_mul_left]; congr 1; funext n; simp only [hg]; ring

lemma integrableOn_rpow_neg_half_mul_norm_kernel (ha : GeomBounded a R) (hR : 0 ≤ R)
    (hs : 1 < s.re) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖kernel a s u‖) (Ioc 0 u₀) := by
  have hs0 : 0 < s.re := by linarith
  obtain ⟨D, hD0, hD⟩ := exists_coeff_bound ha hs0
  set g : ℕ → ℝ → ℝ := fun n u => majCoeff D R s.re n * u ^ ((s.re + n) / 2 - 3 / 2) with hg
  have hr : ∀ n : ℕ, -1 < (s.re + n) / 2 - 3 / 2 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hgi : ∀ n, IntegrableOn (g n) (Ioc 0 u₀) := fun n =>
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.le).1
      (intervalIntegral.intervalIntegrable_rpow' (hr n))).const_mul _
  have hgint : Integrable (fun u => ∑' n, g n u) (volume.restrict (Ioc 0 u₀)) := by
    refine integrable_tsum_of_nonneg hgi ?_ ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu n => ?_)
      exact mul_nonneg (majCoeff_nonneg hD0 hR hs0 n) (Real.rpow_nonneg hu.1.le _)
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      refine ((summable_maj (D := D) hR hs0 hu.1).mul_left (u ^ (-(1 / 2 : ℝ)))).congr
        fun n => ?_
      simp only [hg]
      rw [mul_left_comm, ← Real.rpow_add hu.1]; congr 2; ring
    · have hsm := (summable_majCoeff_mul_pow (D := D) (σ := s.re) (q := √u₀) hR hs0
        (Real.sqrt_nonneg _)).mul_left (2 / (s.re - 1) * u₀ ^ ((s.re + 1) / 2 - 1))
      refine Summable.of_nonneg_of_le (fun n => integral_nonneg_of_ae ?_) (fun n => ?_) hsm
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
        exact mul_nonneg (majCoeff_nonneg hD0 hR hs0 n) (Real.rpow_nonneg hu.1.le _)
      · simp only [hg]
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hu₀.le,
          integral_rpow (Or.inl (hr n)), Real.zero_rpow (by linarith [hr n]), sub_zero]
        have h1 : (s.re + n) / 2 - 3 / 2 + 1 = ((s.re + 1) + n) / 2 - 1 := by ring
        rw [h1, rpow_half_eq hu₀]
        have h2 : (s.re - 1) / 2 ≤ ((s.re + 1) + n) / 2 - 1 := by
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        have h3 : 0 < (s.re - 1) / 2 := by linarith
        have hm := majCoeff_nonneg hD0 hR hs0 n (D := D) (R := R)
        have hp : 0 ≤ u₀ ^ ((s.re + 1) / 2 - 1) * √u₀ ^ n := by positivity
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by linarith)]
        have : majCoeff D R s.re n * (u₀ ^ ((s.re + 1) / 2 - 1) * √u₀ ^ n) * 1 ≤
            majCoeff D R s.re n * (u₀ ^ ((s.re + 1) / 2 - 1) * √u₀ ^ n) *
              (2 / (s.re - 1) * (((s.re + 1) + n) / 2 - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hm hp)
          rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
        nlinarith [this]
  refine Integrable.mono' hgint ?_ ?_
  · exact (continuousOn_rpow_neg_half.mul (continuousOn_kernel ha hR hs0).norm).mono
      Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 < u := hu.1
    have hsm := summable_maj (D := D) hR hs0 hu0
    rw [Real.norm_of_nonneg (by positivity)]
    calc u ^ (-(1 / 2 : ℝ)) * ‖kernel a s u‖
        ≤ u ^ (-(1 / 2 : ℝ)) * ∑' n, majCoeff D R s.re n * u ^ ((s.re + n) / 2 - 1) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu0.le _)
          exact tsum_of_norm_bounded hsm.hasSum (norm_kernelTerm_le hD hu0)
      _ = ∑' n, g n u := by
          rw [← tsum_mul_left]; congr 1; funext n; simp only [hg]
          rw [mul_left_comm, ← Real.rpow_add hu0]; congr 2; ring

/-- `k^{-(s+n)} = k^{-s} (1/k)^n`. -/
lemma natCast_cpow_neg_add {k : ℕ} (hk : k ≠ 0) (s : ℂ) (n : ℕ) :
    (k : ℂ) ^ (-(s + n)) = ((k : ℂ) ^ s)⁻¹ * (k : ℂ)⁻¹ ^ n := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rw [neg_add, Complex.cpow_add _ _ hk', Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_natCast,
    inv_pow]

/-- **Theorem 3.2 (splitting), for `Re s > 1`, with the pieces as integrals.**
If `F(k) = f(1/k)` for `k ≥ k₀ > R`, `f = ∑ a_n x^n`, `|a_n| ≤ C R^n`, then for every `u₀ > 0`
`ζ_F^{≥k₀}(s) = ∑_{k ≥ k₀} I_k(s) + √π ∑_{m ≥ 1} J_m(s) + M(s)`. -/
theorem zetaTail_split (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) (hs : 1 < s.re) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    zetaTail F k₀ s = ∑' k : ℕ, kTerm (kernel a s) u₀ (k + k₀) +
      √π * ∑' m : ℕ, dualTerm (kernel a s) u₀ (m + 1) + mainTerm (kernel a s) u₀ k₀ := by
  have hs0 : 0 < s.re := by linarith
  have hspl := theta_split (h := kernel a s) hk₀ hu₀ (continuousOn_kernel ha hR hs0)
    (integrableOn_rpow_neg_half_mul_norm_kernel ha hR hs hu₀)
    ((integrableOn_exp_mul_norm_kernel ha hR hs0 hRk).mono_set (Ioi_subset_Ioi hu₀.le))
  have hterm : ∀ k : ℕ, ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * kernel a s u =
      LSeries.term (tail k₀ F) s (k + k₀) := by
    intro k
    have hK : (k + k₀ : ℕ) ≠ 0 := by omega
    have hRK : R < ((k + k₀ : ℕ) : ℝ) := lt_of_lt_of_le hRk (by exact_mod_cast Nat.le_add_left k₀ k)
    have h1 := (hasSum_laplace_kernel ha hR hs0 hRK).tsum_eq
    rw [← h1, LSeries.term_of_ne_zero hK, tail, if_pos (Nat.le_add_left k₀ k),
      hF _ (Nat.le_add_left k₀ k), evalInv]
    push_cast
    simp_rw [show ((k : ℂ) + k₀) = ((k + k₀ : ℕ) : ℂ) by push_cast; ring]
    simp_rw [natCast_cpow_neg_add hK]
    rw [div_eq_mul_inv, ← tsum_mul_right]
    congr 1; funext n; ring
  simp only [hterm] at hspl
  have hzero : ∑ i ∈ Finset.range k₀, LSeries.term (tail k₀ F) s i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [LSeries.term, tail, show ¬ k₀ ≤ i by omega]
  have hfull := (hasSum_nat_add_iff' (f := LSeries.term (tail k₀ F) s) k₀).1
    (by rw [hzero, sub_zero]; exact hspl)
  rw [zetaTail, LSeries, hfull.tsum_eq]

end ZetaF
