/-
# Theorem 4.1(1) inside the unit disc

For `α = α₁ + iα₂` with `α₂ > 0` we have `|z| = e^{-2πα₂} < 1` and complex dual points
`c_n = π²(n - α)²`, with `Re c_n = π²((n - α₁)² - α₂²)`.  On the *diamond*
`{α : |α₂| < min(α₁, 1 - α₁)}` all `Re c_n > 0`, so the dual integrals `J^{(δ)}(c_n)` converge
and the right-hand side of the splitting is holomorphic in `α`.  The left-hand side
`Li_F^{≥k₀}(s, e^{2πiα})` is holomorphic for `Im α > 0` and continuous up to the real axis, and
the two agree on the real segment (`polylogTail_split`).  Boundary uniqueness
(`eqOn_zero_of_boundary`, our substitute for the reflection principle) then gives the identity on
the upper half of the diamond, i.e. for `e^{-2π min(α₁, 1-α₁)} < |z| < 1`
(`polylogTail_split_disk`).

The rest of the disc needs `J^{(δ)}_w(c)` for `Re c ≤ 0`, which the paper obtains by continuing
`D_a(c) = c^a Γ(-a, c/u₀)` to the slit plane; that continuation is not formalized.
-/
import ZetaF.Continuation.Geometric
import ZetaF.Analysis.Boundary

open MeasureTheory Set Filter Metric
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-! ### Complex dual points and dual integrals -/

/-- `c_n = π²(n - α)²` for complex `α`. -/
noncomputable def geoDualC (α : ℂ) (n : ℤ) : ℂ := (π : ℂ) ^ 2 * ((n : ℂ) - α) ^ 2

/-- `J_t(c) = ∫₀^{u₀} u^{-t} e^{-c/u} h(u) du` for complex `c`. -/
noncomputable def geoJC (h : ℝ → ℂ) (u₀ t : ℝ) (c : ℂ) : ℂ :=
  ∫ u in Ioc 0 u₀, ((u ^ (-t) : ℝ) : ℂ) * Complex.exp (-(c / u)) * h u

lemma geoDualC_ofReal (α : ℝ) (n : ℤ) : geoDualC α n = (geoDual α n : ℂ) := by
  simp only [geoDualC, geoDual]; push_cast; ring

lemma geoJC_ofReal (h : ℝ → ℂ) (u₀ t c : ℝ) : geoJC h u₀ t c = geoJ h u₀ t c := by
  unfold geoJC geoJ
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div]

lemma geoDualC_re (α : ℂ) (n : ℤ) :
    (geoDualC α n).re = π ^ 2 * (((n : ℝ) - α.re) ^ 2 - α.im ^ 2) := by
  simp only [geoDualC, pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im]
  ring

/-- The margin `min(α₁, 1 - α₁) - |α₂|`; the diamond is where it is positive. -/
noncomputable def margin (α : ℂ) : ℝ := min α.re (1 - α.re) - |α.im|

/-- The diamond `{α : |Im α| < min(Re α, 1 - Re α)}`. -/
def diamond : Set ℂ := {α | 0 < margin α}

lemma continuous_margin : Continuous margin := by
  unfold margin; fun_prop

lemma isOpen_diamond : IsOpen diamond := isOpen_lt continuous_const continuous_margin

lemma re_mem_of_margin_pos {α : ℂ} (h : 0 < margin α) : 0 < α.re ∧ α.re < 1 := by
  unfold margin at h
  have := abs_nonneg α.im
  constructor
  · linarith [min_le_left α.re (1 - α.re)]
  · linarith [min_le_right α.re (1 - α.re)]

lemma margin_le_dist {α β : ℂ} : margin α - 2 * dist α β ≤ margin β := by
  unfold margin
  have h1 : |α.re - β.re| ≤ dist α β := by
    rw [Complex.dist_eq]; exact Complex.abs_re_le_norm (α - β) |>.trans_eq' (by simp)
  have h2 : |α.im - β.im| ≤ dist α β := by
    rw [Complex.dist_eq]; exact Complex.abs_im_le_norm (α - β) |>.trans_eq' (by simp)
  have h3 : |β.im| - |α.im| ≤ |α.im - β.im| := by
    rw [abs_sub_comm α.im]; exact abs_sub_abs_le_abs_sub _ _
  have h4 : min α.re (1 - α.re) - |α.re - β.re| ≤ min β.re (1 - β.re) :=
    le_min (by linarith [min_le_left α.re (1 - α.re), le_abs_self (α.re - β.re)])
      (by linarith [min_le_right α.re (1 - α.re), neg_abs_le (α.re - β.re)])
  linarith

lemma min_le_abs_int_sub {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (n : ℤ) :
    min x (1 - x) ≤ |(n : ℝ) - x| := by
  rcases le_or_gt n 0 with hn | hn
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    rw [abs_of_neg (by linarith)]; linarith [min_le_left x (1 - x)]
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_pos (by linarith)]; linarith [min_le_right x (1 - x)]

/-- **Lower bound for the dual points**: `Re c_n ≥ π² · margin(α) · |n - α₁|`. -/
lemma geoDualC_re_ge {α : ℂ} (hα : 0 < margin α) (n : ℤ) :
    π ^ 2 * margin α * |(n : ℝ) - α.re| ≤ (geoDualC α n).re := by
  obtain ⟨h0, h1⟩ := re_mem_of_margin_pos hα
  have hd := min_le_abs_int_sub h0 h1 n
  rw [geoDualC_re]
  set d := |(n : ℝ) - α.re|
  have hsq : ((n : ℝ) - α.re) ^ 2 = d ^ 2 := (sq_abs _).symm
  have hsq' : α.im ^ 2 = |α.im| ^ 2 := (sq_abs _).symm
  rw [hsq, hsq']
  have hm : margin α = min α.re (1 - α.re) - |α.im| := rfl
  have hai := abs_nonneg α.im
  have : margin α * d ≤ d ^ 2 - |α.im| ^ 2 := by nlinarith
  have hπ : 0 ≤ π ^ 2 := by positivity
  nlinarith

lemma abs_int_sub_ge {α : ℂ} (hα : 0 < margin α) (n : ℤ) : |(n : ℝ)| - 1 ≤ |(n : ℝ) - α.re| := by
  obtain ⟨h0, h1⟩ := re_mem_of_margin_pos hα
  have := abs_sub_abs_le_abs_sub (n : ℝ) α.re
  rw [abs_of_pos h0] at this; linarith

lemma geoDualC_re_pos {α : ℂ} (hα : 0 < margin α) (n : ℤ) : 0 < (geoDualC α n).re := by
  obtain ⟨h0, h1⟩ := re_mem_of_margin_pos hα
  have hd := min_le_abs_int_sub h0 h1 n
  have hm : margin α ≤ min α.re (1 - α.re) := by unfold margin; linarith [abs_nonneg α.im]
  have := geoDualC_re_ge hα n
  have : 0 < π ^ 2 * margin α * |(n : ℝ) - α.re| := by
    have : 0 < |(n : ℝ) - α.re| := by linarith
    positivity
  linarith

/-! ### The dual integrals for complex `c` -/

lemma norm_geoJC_integrand {h : ℝ → ℂ} {t : ℝ} {c : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖((u ^ (-t) : ℝ) : ℂ) * Complex.exp (-(c / u)) * h u‖ =
      rexp (-(c.re / u)) * (u ^ (-t) * ‖h u‖) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hu.le _),
    Complex.norm_exp]
  simp only [Complex.neg_re, Complex.div_ofReal_re]
  ring

lemma exp_neg_div_le {c u u₀ : ℝ} (hc : 0 ≤ c) (hu : 0 < u) (hu₀ : u ≤ u₀) :
    rexp (-(c / u)) ≤ rexp (-(c / u₀)) := by
  rw [Real.exp_le_exp, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hc hu hu₀

/-- `‖J_t(c)‖ ≤ e^{-Re c/u₀} ∫₀^{u₀} u^{-t}|h|` for `Re c ≥ 0`. -/
lemma norm_geoJC_le {h : ℝ → ℂ} {u₀ t : ℝ}
    (hint : IntegrableOn (fun u => u ^ (-t) * ‖h u‖) (Ioc 0 u₀)) {c : ℂ} (hc : 0 ≤ c.re) :
    ‖geoJC h u₀ t c‖ ≤ rexp (-(c.re / u₀)) * ∫ u in Ioc 0 u₀, u ^ (-t) * ‖h u‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
  rw [norm_geoJC_integrand hu.1]
  exact mul_le_mul_of_nonneg_right (exp_neg_div_le hc hu.1 hu.2)
    (mul_nonneg (Real.rpow_nonneg hu.1.le _) (norm_nonneg _))

lemma continuousOn_geoJC_integrand {h : ℝ → ℂ} (hcont : ContinuousOn h (Ioi 0)) (t : ℝ) (c : ℂ) :
    ContinuousOn (fun u : ℝ => ((u ^ (-t) : ℝ) : ℂ) * Complex.exp (-(c / u)) * h u) (Ioi 0) := by
  intro u hu
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hu)
  refine ContinuousAt.continuousWithinAt ?_ |>.mul (hcont u hu)
  refine (Complex.continuous_ofReal.continuousAt.comp
    (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hu)))).mul ?_
  refine Complex.continuous_exp.continuousAt.comp (ContinuousAt.neg ?_)
  exact continuousAt_const.div Complex.continuous_ofReal.continuousAt hu0

lemma le_exp_self' (x : ℝ) : x ≤ rexp x := by
  linarith [Real.add_one_le_exp x]

/-- `J_t` is holomorphic on `Re c > 0`. -/
theorem differentiableOn_geoJC {h : ℝ → ℂ} {u₀ t : ℝ} (hcont : ContinuousOn h (Ioi 0))
    (hint : IntegrableOn (fun u => u ^ (-t) * ‖h u‖) (Ioc 0 u₀)) :
    DifferentiableOn ℂ (geoJC h u₀ t) {c | 0 < c.re} := by
  intro c₀ hc₀
  have hc₀ : 0 < c₀.re := hc₀
  apply DifferentiableAt.differentiableWithinAt
  set F : ℂ → ℝ → ℂ := fun c u => ((u ^ (-t) : ℝ) : ℂ) * Complex.exp (-(c / u)) * h u
  set F' : ℂ → ℝ → ℂ := fun c u =>
    ((u ^ (-t) : ℝ) : ℂ) * (Complex.exp (-(c / u)) * (-(1 / (u : ℂ)))) * h u
  set ε := c₀.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hmeas : ∀ c, AEStronglyMeasurable (F c) (volume.restrict (Ioc 0 u₀)) := fun c =>
    ((continuousOn_geoJC_integrand hcont t c).mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc
  have hmeas' : AEStronglyMeasurable (F' c₀) (volume.restrict (Ioc 0 u₀)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    intro u hu
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hu.1)
    have h1 := continuousOn_geoJC_integrand hcont t c₀ u hu.1
    have h2 : ContinuousWithinAt (fun u : ℝ => -(1 / (u : ℂ))) (Ioc 0 u₀) u :=
      (ContinuousAt.neg (continuousAt_const.div Complex.continuous_ofReal.continuousAt hu0)
        ).continuousWithinAt
    have := (h1.mono Ioc_subset_Ioi_self).mul h2
    refine this.congr (fun v _ => ?_) ?_ <;> simp only [F', Pi.mul_apply] <;> ring
  have hint0 : Integrable (F c₀) (volume.restrict (Ioc 0 u₀)) := by
    refine Integrable.mono' hint (hmeas c₀) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    simp only [F]
    rw [norm_geoJC_integrand hu.1]
    refine mul_le_of_le_one_left (mul_nonneg (Real.rpow_nonneg hu.1.le _) (norm_nonneg _)) ?_
    rw [Real.exp_le_one_iff, neg_nonpos]; exact div_nonneg hc₀.le hu.1.le
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioc 0 u₀)), ∀ c ∈ ball c₀ ε,
      ‖F' c u‖ ≤ ε⁻¹ * (u ^ (-t) * ‖h u‖) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu c hc => ?_)
    have hcre : ε < c.re := by
      have := Complex.abs_re_le_norm (c - c₀)
      rw [mem_ball, Complex.dist_eq] at hc
      simp only [Complex.sub_re] at this
      have := neg_abs_le (c.re - c₀.re)
      linarith
    simp only [F']
    have hu1 := hu.1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hu1.le _), Complex.norm_exp, norm_neg, norm_div,
      norm_one, Complex.norm_real, Real.norm_of_nonneg hu1.le]
    simp only [Complex.neg_re, Complex.div_ofReal_re]
    have key : rexp (-(c.re / u)) * (1 / u) ≤ ε⁻¹ := by
      have h1 : rexp (-(c.re / u)) ≤ rexp (-(ε / u)) := by
        rw [Real.exp_le_exp, neg_le_neg_iff]; exact div_le_div_of_nonneg_right hcre.le hu1.le
      have h2 : ε / u ≤ rexp (ε / u) := le_exp_self' _
      have h3a : rexp (-(ε / u)) ≤ u / ε := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]; exact h2
      have h3 : rexp (-(ε / u)) * (1 / u) ≤ ε⁻¹ :=
        calc rexp (-(ε / u)) * (1 / u) ≤ u / ε * (1 / u) :=
              mul_le_mul_of_nonneg_right h3a (by positivity)
          _ = ε⁻¹ := by field_simp
      calc rexp (-(c.re / u)) * (1 / u) ≤ rexp (-(ε / u)) * (1 / u) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ ε⁻¹ := h3
    calc u ^ (-t) * (rexp (-(c.re / u)) * (1 / u)) * ‖h u‖
        = (rexp (-(c.re / u)) * (1 / u)) * (u ^ (-t) * ‖h u‖) := by ring
      _ ≤ ε⁻¹ * (u ^ (-t) * ‖h u‖) :=
          mul_le_mul_of_nonneg_right key (mul_nonneg (Real.rpow_nonneg hu1.le _) (norm_nonneg _))
  have hdiff : ∀ᵐ u ∂(volume.restrict (Ioc 0 u₀)), ∀ c ∈ ball c₀ ε,
      HasDerivAt (fun c => F c u) (F' c u) c := by
    refine Eventually.of_forall fun u c _ => ?_
    simp only [F, F']
    have : HasDerivAt (fun c : ℂ => -(c / u)) (-(1 / (u : ℂ))) c :=
      ((hasDerivAt_id' c).div_const (u : ℂ)).neg
    exact (this.cexp.const_mul _).mul_const _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds c₀ hε0)
    (Eventually.of_forall hmeas) hint0 hmeas' hbound (hint.const_mul _) hdiff).2.differentiableAt

/-! ### The dual sum is holomorphic on the diamond -/

/-- The dual term `J^{(0)}(c_n) - iπ(n - α) J^{(1)}(c_n)` for complex `α`. -/
noncomputable def dualTermC (a : ℕ → ℂ) (u₀ : ℝ) (s α : ℂ) (n : ℤ) : ℂ :=
  geoJC (kernel a s) u₀ (1 / 2) (geoDualC α n) -
    Complex.I * π * ((n : ℂ) - α) * geoJC (kernel a (s + 1)) u₀ (3 / 2) (geoDualC α n)

lemma summable_int_exp_abs {l : ℝ} (hl : 0 < l) (A B : ℝ) :
    Summable fun n : ℤ => rexp (-(l * (|(n : ℝ)| - 1))) * (A + B * |(n : ℝ)|) := by
  have hr : ‖rexp (-l)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]; linarith
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs0 := summable_pow_mul_geometric_of_norm_lt_one 0 hr
  have hnat : Summable fun n : ℕ => rexp (-(l * ((n : ℝ) - 1))) * (A + B * (n : ℝ)) := by
    have := ((hs0.mul_left A).add (hs1.mul_left B)).mul_left (rexp l)
    refine this.congr fun n => ?_
    have : rexp (-(l * ((n : ℝ) - 1))) = rexp l * rexp (-l) ^ n := by
      rw [← Real.exp_natCast_mul, ← Real.exp_add]; ring_nf
    rw [this]; simp only [pow_zero, pow_one, one_mul]; ring
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hnat.congr fun n => ?_
    simp only [Int.cast_natCast, Nat.abs_cast]
  · refine hnat.congr fun n => ?_
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]

section DualSum

variable (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀) {s : ℂ} (hs : 2 < s.re)
include ha hR hu₀ hs

lemma integrableOn_kernel_half :
    IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖kernel a s u‖) (Ioc 0 u₀) :=
  integrableOn_rpow_neg_mul_norm_kernel ha hR (by linarith) (by linarith) hu₀

lemma integrableOn_kernel_three_half :
    IntegrableOn (fun u => u ^ (-(3 / 2 : ℝ)) * ‖kernel a (s + 1) u‖) (Ioc 0 u₀) :=
  integrableOn_rpow_neg_mul_norm_kernel ha hR (by simp; linarith) (by simp; linarith) hu₀

lemma differentiableAt_dualTermC {α : ℂ} (hα : 0 < margin α) (n : ℤ) :
    DifferentiableAt ℂ (fun α => dualTermC a u₀ s α n) α := by
  have hd : Differentiable ℂ fun α => geoDualC α n := fun α =>
    (differentiableAt_const _).mul (((differentiableAt_const _).sub differentiableAt_id).pow 2)
  have hopen : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem := hopen.mem_nhds (geoDualC_re_pos hα n)
  have hJ0 := (differentiableOn_geoJC (continuousOn_kernel ha hR (by linarith))
    (integrableOn_kernel_half ha hR hu₀ hs)).differentiableAt hmem
  have hJ1 := (differentiableOn_geoJC (continuousOn_kernel ha hR (by simp; linarith))
    (integrableOn_kernel_three_half ha hR hu₀ hs)).differentiableAt hmem
  have hlin : DifferentiableAt ℂ (fun α : ℂ => Complex.I * π * ((n : ℂ) - α)) α :=
    (differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)
  have h0 : DifferentiableAt ℂ (fun α => geoJC (kernel a s) u₀ (1 / 2) (geoDualC α n)) α :=
    DifferentiableAt.fun_comp' (f := fun α => geoDualC α n)
      (g := geoJC (kernel a s) u₀ (1 / 2)) α hJ0 (hd α)
  have h1 : DifferentiableAt ℂ
      (fun α => geoJC (kernel a (s + 1)) u₀ (3 / 2) (geoDualC α n)) α :=
    DifferentiableAt.fun_comp' (f := fun α => geoDualC α n)
      (g := geoJC (kernel a (s + 1)) u₀ (3 / 2)) α hJ1 (hd α)
  unfold dualTermC
  exact h0.sub (hlin.mul h1)

lemma norm_dualTermC_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {α : ℂ} (hα : δ₀ ≤ margin α) (n : ℤ) :
    ‖dualTermC a u₀ s α n‖ ≤
      rexp (-(π ^ 2 * δ₀ / u₀ * (|(n : ℝ)| - 1))) *
        ((∫ u in Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * ‖kernel a s u‖) +
          2 * π * (∫ u in Ioc 0 u₀, u ^ (-(3 / 2 : ℝ)) * ‖kernel a (s + 1) u‖) +
          π * (∫ u in Ioc 0 u₀, u ^ (-(3 / 2 : ℝ)) * ‖kernel a (s + 1) u‖) * |(n : ℝ)|) := by
  have hm : 0 < margin α := lt_of_lt_of_le hδ₀ hα
  set K₀ := ∫ u in Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * ‖kernel a s u‖
  set K₁ := ∫ u in Ioc 0 u₀, u ^ (-(3 / 2 : ℝ)) * ‖kernel a (s + 1) u‖
  have hK₀ : 0 ≤ K₀ := setIntegral_nonneg measurableSet_Ioc fun u hu =>
    mul_nonneg (Real.rpow_nonneg hu.1.le _) (norm_nonneg _)
  have hK₁ : 0 ≤ K₁ := setIntegral_nonneg measurableSet_Ioc fun u hu =>
    mul_nonneg (Real.rpow_nonneg hu.1.le _) (norm_nonneg _)
  have hre := geoDualC_re_pos hm n
  set E := rexp (-(π ^ 2 * δ₀ / u₀ * (|(n : ℝ)| - 1)))
  have hE : rexp (-((geoDualC α n).re / u₀)) ≤ E := by
    rw [Real.exp_le_exp, neg_le_neg_iff, mul_comm, ← mul_div_assoc, div_le_div_iff_of_pos_right hu₀]
    have h1 := geoDualC_re_ge hm n
    have h2 := abs_int_sub_ge hm n
    have hd : 0 ≤ |(n : ℝ) - α.re| := abs_nonneg _
    have hπ : 0 < π ^ 2 := by positivity
    calc (|(n : ℝ)| - 1) * (π ^ 2 * δ₀) ≤ |(n : ℝ) - α.re| * (π ^ 2 * δ₀) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ |(n : ℝ) - α.re| * (π ^ 2 * margin α) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hα hπ.le) hd
      _ ≤ _ := by linarith
  have hnα : ‖(n : ℂ) - α‖ ≤ |(n : ℝ)| + 2 := by
    obtain ⟨h0, h1⟩ := re_mem_of_margin_pos hm
    have him : |α.im| < 1 := by
      unfold margin at hm; linarith [min_le_left α.re (1 - α.re)]
    calc ‖(n : ℂ) - α‖ ≤ ‖(n : ℂ)‖ + ‖α‖ := norm_sub_le _ _
      _ ≤ |(n : ℝ)| + (|α.re| + |α.im|) := by
          gcongr
          · rw [Complex.norm_intCast]
          · exact Complex.norm_le_abs_re_add_abs_im α
      _ ≤ |(n : ℝ)| + 2 := by rw [abs_of_pos h0]; linarith
  have hJ0 := norm_geoJC_le (integrableOn_kernel_half ha hR hu₀ hs) hre.le
  have hJ1 := norm_geoJC_le (integrableOn_kernel_three_half ha hR hu₀ hs) hre.le
  unfold dualTermC
  calc _ ≤ ‖geoJC (kernel a s) u₀ (1 / 2) (geoDualC α n)‖ +
        ‖Complex.I * π * ((n : ℂ) - α)‖ * ‖geoJC (kernel a (s + 1)) u₀ (3 / 2) (geoDualC α n)‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
    _ ≤ E * K₀ + (π * (|(n : ℝ)| + 2)) * (E * K₁) := by
        gcongr
        · exact hJ0.trans (mul_le_mul_of_nonneg_right hE hK₀)
        · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_of_nonneg Real.pi_pos.le]
          exact mul_le_mul_of_nonneg_left hnα Real.pi_pos.le
        · exact hJ1.trans (mul_le_mul_of_nonneg_right hE hK₁)
    _ = _ := by ring

/-- **The dual sum is holomorphic in `α` on the diamond.** -/
theorem differentiableOn_dualSum :
    DifferentiableOn ℂ (fun α => ∑' n : ℤ, dualTermC a u₀ s α n) diamond := by
  intro α₀ hα₀
  have hα₀ : 0 < margin α₀ := hα₀
  set δ₀ := margin α₀
  have hball : ∀ α ∈ ball α₀ (δ₀ / 4), δ₀ / 2 ≤ margin α := fun α hα => by
    have := margin_le_dist (α := α₀) (β := α)
    rw [mem_ball, dist_comm] at hα
    linarith
  have hd : DifferentiableOn ℂ (fun α => ∑' n : ℤ, dualTermC a u₀ s α n) (ball α₀ (δ₀ / 4)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_int_exp_abs (by positivity) _ _) (fun n α hα => ?_) isOpen_ball
      (fun n α hα => norm_dualTermC_le ha hR hu₀ hs (by positivity) (hball α hα) n)
    exact (differentiableAt_dualTermC ha hR hu₀ hs
      (lt_of_lt_of_le (by positivity) (hball α hα)) n).differentiableWithinAt
  exact (hd.differentiableAt (ball_mem_nhds α₀ (by positivity))).differentiableWithinAt

end DualSum

/-! ### The `k`-sum is entire in `α` -/

/-- `z = e^{2πiα}`. -/
noncomputable def geoZ (α : ℂ) : ℂ := Complex.exp (2 * π * Complex.I * α)

lemma norm_geoZ (α : ℂ) : ‖geoZ α‖ = rexp (-(2 * π * α.im)) := by
  rw [geoZ, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma differentiable_geoZ : Differentiable ℂ geoZ := fun _ =>
  ((differentiableAt_const _).mul differentiableAt_id).cexp

lemma differentiable_geoC (m : ℕ) : Differentiable ℂ fun α => geoC (geoZ α) m := by
  unfold geoC
  exact ((differentiable_geoZ.pow m).add ((differentiable_geoZ.pow m).inv
    fun _ => pow_ne_zero _ (Complex.exp_ne_zero _))).div_const 2

lemma differentiable_geoS (m : ℕ) : Differentiable ℂ fun α => geoS (geoZ α) m := by
  unfold geoS
  exact ((differentiable_geoZ.pow m).sub ((differentiable_geoZ.pow m).inv
    fun _ => pow_ne_zero _ (Complex.exp_ne_zero _))).div_const 2

lemma norm_geoC_le_pow {z : ℂ} {E : ℝ} (h1 : ‖z‖ ≤ E) (h2 : ‖z‖⁻¹ ≤ E) (k : ℕ) :
    ‖geoC z k‖ ≤ E ^ k := by
  rw [geoC, norm_div, Complex.norm_two]
  calc ‖z ^ k + (z ^ k)⁻¹‖ / 2 ≤ (‖z ^ k‖ + ‖(z ^ k)⁻¹‖) / 2 := by gcongr; exact norm_add_le _ _
    _ = (‖z‖ ^ k + ‖z‖⁻¹ ^ k) / 2 := by rw [norm_inv, norm_pow, inv_pow]
    _ ≤ (E ^ k + E ^ k) / 2 := by gcongr
    _ = E ^ k := by ring

lemma norm_geoS_le_pow {z : ℂ} {E : ℝ} (h1 : ‖z‖ ≤ E) (h2 : ‖z‖⁻¹ ≤ E) (k : ℕ) :
    ‖geoS z k‖ ≤ E ^ k := by
  rw [geoS, norm_div, Complex.norm_two]
  calc ‖z ^ k - (z ^ k)⁻¹‖ / 2 ≤ (‖z ^ k‖ + ‖(z ^ k)⁻¹‖) / 2 := by gcongr; exact norm_sub_le _ _
    _ = (‖z‖ ^ k + ‖z‖⁻¹ ^ k) / 2 := by rw [norm_inv, norm_pow, inv_pow]
    _ ≤ (E ^ k + E ^ k) / 2 := by gcongr
    _ = E ^ k := by ring

lemma norm_geoZ_le {α₀ α : ℂ} (hα : α ∈ ball α₀ 1) :
    ‖geoZ α‖ ≤ rexp (2 * π * (|α₀.im| + 1)) ∧ ‖geoZ α‖⁻¹ ≤ rexp (2 * π * (|α₀.im| + 1)) := by
  have him : |α.im| ≤ |α₀.im| + 1 := by
    have h := Complex.abs_im_le_norm (α - α₀)
    rw [mem_ball, Complex.dist_eq] at hα
    simp only [Complex.sub_im] at h
    have := abs_sub_abs_le_abs_sub α.im α₀.im
    linarith
  have hπ := Real.pi_pos
  rw [norm_geoZ, ← Real.exp_neg, neg_neg]
  constructor <;> rw [Real.exp_le_exp]
  · nlinarith [neg_abs_le α.im]
  · nlinarith [le_abs_self α.im]

lemma quad_le (A u₀ : ℝ) (hu₀ : 0 < u₀) (k : ℝ) :
    A * k - u₀ * k ^ 2 ≤ (A + 1) ^ 2 / (4 * u₀) - k := by
  have h4 : 0 < 4 * u₀ := by linarith
  rw [le_sub_iff_add_le, le_div_iff₀ h4]
  nlinarith [sq_nonneg (2 * u₀ * k - (A + 1))]

/-- The `k`-th term `C_k I_k(s) + k S_k I_k(s+1)` of the `k`-sum, `k ≥ k₀`, as a function of `α`. -/
noncomputable def kSumTermC (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (s : ℂ) (k : ℕ) (α : ℂ) : ℂ :=
  geoC (geoZ α) (k + k₀) * kTerm (kernel a s) u₀ (k + k₀) +
    ((k + k₀ : ℕ) : ℂ) * geoS (geoZ α) (k + k₀) * kTerm (kernel a (s + 1)) u₀ (k + k₀)

/-- The bound on the `k`-th term used for summing over `k`. -/
lemma norm_kSumTermC_le {k₀ : ℕ} {u₀ : ℝ} (hu₀ : 0 < u₀) {s α : ℂ} {A B₁ B₂ : ℝ}
    (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂) (hz1 : ‖geoZ α‖ ≤ rexp A) (hz2 : ‖geoZ α‖⁻¹ ≤ rexp A) (k : ℕ)
    (hK1 : ‖kTerm (kernel a s) u₀ (k + k₀)‖ ≤
      rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀) * B₁)
    (hK2 : ‖kTerm (kernel a (s + 1)) u₀ (k + k₀)‖ ≤
      rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀) * B₂) :
    ‖kSumTermC a k₀ u₀ s k α‖ ≤
      rexp A ^ k₀ * rexp ((A + 1) ^ 2 / (4 * u₀)) * (B₁ + B₂ * k₀) * ((k : ℝ) ^ 0 * rexp (-1) ^ k) +
        rexp A ^ k₀ * rexp ((A + 1) ^ 2 / (4 * u₀)) * B₂ * ((k : ℝ) ^ 1 * rexp (-1) ^ k) := by
  set E := rexp A
  set q := rexp (-1)
  set M := E ^ k₀ * rexp ((A + 1) ^ 2 / (4 * u₀))
  have hexp : E ^ (k + k₀) * rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀) ≤ M * q ^ k := by
    have e1 : E ^ (k + k₀) = E ^ k₀ * rexp (k * A) := by
      rw [pow_add, mul_comm, Real.exp_natCast_mul]
    have e2 : M * q ^ k = E ^ k₀ * rexp ((A + 1) ^ 2 / (4 * u₀) - k) := by
      rw [show q ^ k = rexp (-(k : ℝ)) by simp only [q]; rw [← Real.exp_natCast_mul]; ring_nf]
      simp only [M]; rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
    rw [e1, e2, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have := quad_le A u₀ hu₀ k
    have hk0 : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    push_cast
    nlinarith [this, mul_nonneg (mul_nonneg hk hk0) hu₀.le]
  have hC := norm_geoC_le_pow hz1 hz2 (k + k₀)
  have hS := norm_geoS_le_pow hz1 hz2 (k + k₀)
  set X := rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀)
  have hX : 0 ≤ X := (Real.exp_pos _).le
  have hEk : 0 ≤ E ^ (k + k₀) := by positivity
  unfold kSumTermC
  calc _ ≤ ‖geoC (geoZ α) (k + k₀)‖ * ‖kTerm (kernel a s) u₀ (k + k₀)‖ +
        ((k + k₀ : ℕ) : ℝ) * ‖geoS (geoZ α) (k + k₀)‖ * ‖kTerm (kernel a (s + 1)) u₀ (k + k₀)‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
    _ ≤ E ^ (k + k₀) * (X * B₁) + ((k + k₀ : ℕ) : ℝ) * E ^ (k + k₀) * (X * B₂) := by
        gcongr
    _ = (E ^ (k + k₀) * X) * (B₁ + B₂ * ((k + k₀ : ℕ) : ℝ)) := by ring
    _ ≤ (M * q ^ k) * (B₁ + B₂ * ((k + k₀ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = _ := by push_cast; ring

lemma summable_kSumBound (A u₀ B₁ B₂ : ℝ) (k₀ : ℕ) :
    Summable fun k : ℕ =>
      rexp A ^ k₀ * rexp ((A + 1) ^ 2 / (4 * u₀)) * (B₁ + B₂ * k₀) * ((k : ℝ) ^ 0 * rexp (-1) ^ k) +
        rexp A ^ k₀ * rexp ((A + 1) ^ 2 / (4 * u₀)) * B₂ * ((k : ℝ) ^ 1 * rexp (-1) ^ k) := by
  have hq : ‖rexp (-1)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]; norm_num
  exact ((summable_pow_mul_geometric_of_norm_lt_one 0 hq).mul_left _).add
    ((summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_left _)

lemma differentiable_kSumTermC (k₀ : ℕ) (u₀ : ℝ) (s : ℂ) (k : ℕ) : Differentiable ℂ (kSumTermC a k₀ u₀ s k) := by
  unfold kSumTermC
  exact ((differentiable_geoC _).mul_const _).add
    (((differentiable_geoS _).const_mul _).mul_const _)

/-- **The `k`-sum is entire in `α`** (the Gaussian decay of `I_k` beats `|z|^{-k}`). -/
theorem differentiable_kSumC (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hRk : R < k₀)
    {u₀ : ℝ} (hu₀ : 0 < u₀) (s : ℂ) :
    Differentiable ℂ fun α => ∑' k, kSumTermC a k₀ u₀ s k α := by
  obtain ⟨B₁, hB₁⟩ := kTerm_local_bound ha hR hRk hu₀ s
  obtain ⟨B₂, hB₂⟩ := kTerm_local_bound ha hR hRk hu₀ (s + 1)
  have hB₁0 : 0 ≤ B₁ := by
    have := (norm_nonneg _).trans (hB₁ s (mem_ball_self one_pos) k₀ le_rfl); simpa using this
  have hB₂0 : 0 ≤ B₂ := by
    have := (norm_nonneg _).trans (hB₂ (s + 1) (mem_ball_self one_pos) k₀ le_rfl)
    simpa using this
  refine differentiable_tsum_of_local_bound (differentiable_kSumTermC k₀ u₀ s)
    fun α₀ => ⟨0, _, summable_kSumBound (2 * π * (|α₀.im| + 1)) u₀ B₁ B₂ k₀, fun k _ α hα => ?_⟩
  obtain ⟨hz1, hz2⟩ := norm_geoZ_le hα
  exact norm_kSumTermC_le hu₀ hB₁0 hB₂0 hz1 hz2 k
    (hB₁ s (mem_ball_self one_pos) (k + k₀) (Nat.le_add_left _ _))
    (hB₂ (s + 1) (mem_ball_self one_pos) (k + k₀) (Nat.le_add_left _ _))

/-! ### The right-hand side for complex `α` -/

/-- The right-hand side of Theorem 4.1(1) for complex `α`. -/
noncomputable def polylogRHSC (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (s α : ℂ) : ℂ :=
  (∑' k, kSumTermC a k₀ u₀ s k α) + ((√π / 2 : ℝ) : ℂ) * ∑' n : ℤ, dualTermC a u₀ s α n -
    1 / 2 * lowerH (kernel a s) u₀ -
    ∑ k ∈ Finset.Ico 1 k₀, (geoC (geoZ α) k * lowerL (kernel a s) u₀ k +
      (k : ℂ) * geoS (geoZ α) k * lowerL (kernel a (s + 1)) u₀ k)

theorem differentiableOn_polylogRHSC (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ}
    (hRk : R < k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) {s : ℂ} (hs : 2 < s.re) :
    DifferentiableOn ℂ (polylogRHSC a k₀ u₀ s) diamond := by
  have hfin : Differentiable ℂ fun α => ∑ k ∈ Finset.Ico 1 k₀,
      (geoC (geoZ α) k * lowerL (kernel a s) u₀ k +
        (k : ℂ) * geoS (geoZ α) k * lowerL (kernel a (s + 1)) u₀ k) :=
    Differentiable.fun_sum fun k _ => ((differentiable_geoC k).mul_const _).add
      (((differentiable_geoS k).const_mul _).mul_const _)
  unfold polylogRHSC
  exact ((((differentiable_kSumC ha hR hRk hu₀ s).differentiableOn).add
    ((differentiableOn_dualSum ha hR hu₀ hs).const_mul _)).sub_const _).sub hfin.differentiableOn

lemma polylogRHSC_ofReal (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (s : ℂ) (α : ℝ) :
    polylogRHSC a k₀ u₀ s α =
      (∑' k : ℕ, (geoC (Complex.exp (2 * π * Complex.I * α)) (k + k₀) *
          kTerm (kernel a s) u₀ (k + k₀) +
        ((k + k₀ : ℕ) : ℂ) * geoS (Complex.exp (2 * π * Complex.I * α)) (k + k₀) *
          kTerm (kernel a (s + 1)) u₀ (k + k₀))) +
      ((√π / 2 : ℝ) : ℂ) * ∑' n : ℤ, (geoJ (kernel a s) u₀ (1 / 2) (geoDual α n) -
        Complex.I * π * (((n : ℝ) - α : ℝ) : ℂ) *
          geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)) -
      1 / 2 * lowerH (kernel a s) u₀ -
      ∑ k ∈ Finset.Ico 1 k₀, (geoC (Complex.exp (2 * π * Complex.I * α)) k * lowerL (kernel a s) u₀ k +
        (k : ℂ) * geoS (Complex.exp (2 * π * Complex.I * α)) k * lowerL (kernel a (s + 1)) u₀ k) := by
  have hd : ∑' n : ℤ, dualTermC a u₀ s α n = ∑' n : ℤ, (geoJ (kernel a s) u₀ (1 / 2) (geoDual α n) -
        Complex.I * π * (((n : ℝ) - α : ℝ) : ℂ) *
          geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)) := by
    refine tsum_congr fun n => ?_
    unfold dualTermC
    rw [geoDualC_ofReal, geoJC_ofReal, geoJC_ofReal]
    push_cast; ring
  unfold polylogRHSC
  rw [hd]
  rfl

/-! ### The left-hand side -/

lemma term_tail_mul_pow (F : ℕ → ℂ) (k₀ : ℕ) (s z : ℂ) (n : ℕ) :
    LSeries.term (tail k₀ fun k => F k * z ^ k) s n = LSeries.term (tail k₀ F) s n * z ^ n := by
  rw [LSeries.term_def, LSeries.term_def]
  unfold tail
  split_ifs <;> ring

section LHS

variable (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ} (hRk : R < k₀)
  (hF : ∀ k ≥ k₀, F k = evalInv a k) {s : ℂ} (hs : 2 < s.re)
include ha hR hRk hF hs

lemma summable_norm_term_tail : Summable fun n => ‖LSeries.term (tail k₀ F) s n‖ := by
  have h := LSeriesSummable_tail_mul ha hR hRk hF (ψ := fun _ => 1) (B := 1) (fun _ => by simp)
    (s := s) (by linarith)
  simp only [one_mul] at h
  exact summable_norm_iff.2 h

omit ha hR hRk hF hs in
lemma lhs_eq (α : ℂ) :
    zetaTail (fun k => F k * geoZ α ^ k) k₀ s =
      ∑' n, LSeries.term (tail k₀ F) s n * geoZ α ^ n := by
  unfold zetaTail LSeries
  exact tsum_congr fun n => term_tail_mul_pow F k₀ s _ n

omit ha hR hRk hF hs in
lemma norm_term_mul_le {α : ℂ} (hα : 0 ≤ α.im) (n : ℕ) :
    ‖LSeries.term (tail k₀ F) s n * geoZ α ^ n‖ ≤ ‖LSeries.term (tail k₀ F) s n‖ := by
  rw [norm_mul, norm_pow, norm_geoZ]
  refine mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (Real.exp_pos _).le ?_)
  rw [Real.exp_le_one_iff, neg_nonpos]; positivity

/-- The polylogarithm tail is continuous in `α` for `Im α ≥ 0` (`|z| ≤ 1`). -/
theorem continuousOn_lhs :
    ContinuousOn (fun α => zetaTail (fun k => F k * geoZ α ^ k) k₀ s) {α | 0 ≤ α.im} := by
  simp only [lhs_eq]
  exact continuousOn_tsum (fun n => ((differentiable_geoZ.pow n).const_mul _).continuous.continuousOn)
    (summable_norm_term_tail ha hR hRk hF hs) fun n α hα => norm_term_mul_le hα n

/-- The polylogarithm tail is holomorphic in `α` for `Im α > 0` (`|z| < 1`). -/
theorem differentiableOn_lhs :
    DifferentiableOn ℂ (fun α => zetaTail (fun k => F k * geoZ α ^ k) k₀ s) {α | 0 < α.im} := by
  simp only [lhs_eq]
  exact Complex.differentiableOn_tsum_of_summable_norm (summable_norm_term_tail ha hR hRk hF hs)
    (fun n => ((differentiable_geoZ.pow n).const_mul _).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_im)
    fun n α hα => norm_term_mul_le (le_of_lt hα) n

end LHS

/-! ### Theorem 4.1(1) inside the disc -/

/-- The upper half of the diamond: `0 < α₂ < min(α₁, 1 - α₁)`. -/
def upperDiamond : Set ℂ := {α | 0 < α.im ∧ α.im < α.re ∧ α.im < 1 - α.re}

lemma isOpen_upperDiamond : IsOpen upperDiamond := by
  have h1 : IsOpen {α : ℂ | 0 < α.im} := isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen {α : ℂ | α.im < α.re} := isOpen_lt Complex.continuous_im Complex.continuous_re
  have h3 : IsOpen {α : ℂ | α.im < 1 - α.re} :=
    isOpen_lt Complex.continuous_im (continuous_const.sub Complex.continuous_re)
  exact h1.inter (h2.inter h3)

lemma convex_upperDiamond : Convex ℝ upperDiamond := by
  intro x hx y hy p q hp hq hpq
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [upperDiamond, mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  rcases hp.lt_or_eq with hp' | hp'
  · refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · subst hp'
    have hq1 : q = 1 := by linarith
    subst hq1
    refine ⟨by linarith, by linarith, by linarith⟩

lemma upperDiamond_subset : upperDiamond ⊆ {α | 0 < α.im} ∩ diamond := by
  rintro α ⟨h1, h2, h3⟩
  refine ⟨h1, ?_⟩
  show 0 < margin α
  unfold margin
  rw [abs_of_pos h1]
  exact sub_pos.2 (lt_min h2 h3)

lemma mem_upperDiamond {α : ℂ} (h0 : 0 < α.im) (hα : α ∈ diamond) : α ∈ upperDiamond := by
  have hm : 0 < margin α := hα
  unfold margin at hm
  rw [abs_of_pos h0] at hm
  exact ⟨h0, by linarith [min_le_left α.re (1 - α.re)], by linarith [min_le_right α.re (1 - α.re)]⟩

lemma ball_half_props {z : ℂ} (hz : z ∈ ball ((1 / 2 : ℝ) : ℂ) (1 / 4)) :
    |z.re - 1 / 2| < 1 / 4 ∧ |z.im| < 1 / 4 := by
  rw [mem_ball, Complex.dist_eq] at hz
  have h1 := Complex.abs_re_le_norm (z - ((1 / 2 : ℝ) : ℂ))
  have h2 := Complex.abs_im_le_norm (z - ((1 / 2 : ℝ) : ℂ))
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero] at h1 h2
  exact ⟨lt_of_le_of_lt h1 hz, lt_of_le_of_lt h2 hz⟩

lemma ball_half_subset_diamond : ball ((1 / 2 : ℝ) : ℂ) (1 / 4) ⊆ diamond := by
  intro z hz
  obtain ⟨h1, h2⟩ := ball_half_props hz
  rw [abs_lt] at h1
  show 0 < margin z
  unfold margin
  have : 1 / 4 < min z.re (1 - z.re) := lt_min (by linarith) (by linarith)
  linarith

/-- **Theorem 4.1(1) for `|z| < 1`** (on the upper half of the diamond, `Re s > 2`): for
`z = e^{2πiα}` with `0 < Im α < min(Re α, 1 - Re α)`, i.e. `e^{-2π min(α₁, 1-α₁)} < |z| < 1`,
`Li_F^{≥k₀}(s, z)` equals the splitting with the complex dual points `c_n = π²(n - α)²`. -/
theorem polylogTail_split_disk (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {s : ℂ} (hs : 2 < s.re)
    {u₀ : ℝ} (hu₀ : 0 < u₀) {α : ℂ} (hα0 : 0 < α.im) (hα : α ∈ diamond) :
    zetaTail (fun k => F k * geoZ α ^ k) k₀ s = polylogRHSC a k₀ u₀ s α := by
  set D : ℂ → ℂ := fun α => zetaTail (fun k => F k * geoZ α ^ k) k₀ s - polylogRHSC a k₀ u₀ s α
  have hRHS := differentiableOn_polylogRHSC ha hR hRk hu₀ hs
  have hD : DifferentiableOn ℂ D upperDiamond :=
    ((differentiableOn_lhs ha hR hRk hF hs).mono fun z hz => (upperDiamond_subset hz).1).sub
      (hRHS.mono fun z hz => (upperDiamond_subset hz).2)
  have hsub : ball ((1 / 2 : ℝ) : ℂ) (1 / 4) ∩ {z | 0 < z.im} ⊆ upperDiamond := by
    rintro z ⟨hz, hz'⟩
    obtain ⟨h1, h2⟩ := ball_half_props hz
    rw [abs_lt] at h1
    have : z.im < 1 / 4 := (le_abs_self _).trans_lt h2
    exact ⟨hz', by linarith, by linarith⟩
  have hcont : ContinuousOn D (ball ((1 / 2 : ℝ) : ℂ) (1 / 4) ∩ {z | 0 ≤ z.im}) :=
    ((continuousOn_lhs ha hR hRk hF hs).mono inter_subset_right).sub
      (hRHS.continuousOn.mono (inter_subset_left.trans ball_half_subset_diamond))
  have hzero : ∀ z ∈ ball ((1 / 2 : ℝ) : ℂ) (1 / 4), z.im = 0 → D z = 0 := by
    intro z _ hz
    have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz])
    simp only [D]
    rw [hz', polylogRHSC_ofReal, sub_eq_zero]
    exact polylogTail_split ha hR hk₀ hRk hF hs z.re hu₀
  have h := eqOn_zero_of_boundary isOpen_upperDiamond convex_upperDiamond.isPreconnected hD
    (by norm_num) hsub hcont hzero (mem_upperDiamond hα0 hα)
  exact sub_eq_zero.1 h

end ZetaF
