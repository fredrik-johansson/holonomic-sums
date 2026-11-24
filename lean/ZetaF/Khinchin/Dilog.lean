/-
# The real dilogarithm (used in Section 6.4, Lemma 6.2)

`Li₂ x = -∫_0^x log(1-t)/t dt` for `x ≤ 1`. We use the continuous kernel
`φ(t) = -log(1-t)/t` (`φ(0) = 1`), which agrees with `-log(1-t)/t` away from `t = 0`
(`Li₂_eq_neg_integral`). We prove
* `hasDerivAt_Li₂`: `Li₂' = φ` on `(-∞, 1)`;
* `hasSum_Li₂`: `Li₂ x = ∑_{n ≥ 1} xⁿ/n²` for `|x| ≤ 1`;
* `Li₂_add_Li₂_neg` (duplication), `Li₂_landen` (Landen), `Li₂_inversion` (inversion);
* the classical values `Li₂ 1`, `Li₂ (-1)`, `Li₂ (1/2)`, `Li₂ (1/4)`, `Li₂ (-2)`.
-/
import ZetaF.Khinchin.LogK
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open Filter Topology Real Set MeasureTheory intervalIntegral

namespace ZetaF

/-- The kernel `φ(t) = -log(1-t)/t`, extended by continuity with `φ(0) = 1`. -/
noncomputable def dilogKer (t : ℝ) : ℝ := if t = 0 then 1 else -Real.log (1 - t) / t

/-- The real dilogarithm `Li₂ x = ∫_0^x φ = -∫_0^x log(1-t)/t dt` (meaningful for `x ≤ 1`). -/
noncomputable def Li₂ (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, dilogKer t

lemma dilogKer_of_ne {t : ℝ} (ht : t ≠ 0) : dilogKer t = -Real.log (1 - t) / t := by
  simp [dilogKer, ht]

@[simp] lemma dilogKer_zero : dilogKer 0 = 1 := by simp [dilogKer]

theorem Li₂_eq_neg_integral (x : ℝ) : Li₂ x = -∫ t in (0 : ℝ)..x, Real.log (1 - t) / t := by
  rw [Li₂, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume 0] with t ht _
  rw [dilogKer_of_ne ht, neg_div]

@[simp] lemma Li₂_zero : Li₂ 0 = 0 := by simp [Li₂]

lemma hasDerivAt_neg_log_one_sub {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun t => -Real.log (1 - t)) (1 / (1 - t)) t := by
  have h := (((hasDerivAt_id t).const_sub 1).log (by simp; linarith)).neg
  convert h using 1
  · funext y; simp
  · simp only [id]; ring

lemma dilogKer_eq_dslope : dilogKer = dslope (fun t => -Real.log (1 - t)) 0 := by
  funext t
  by_cases ht : t = 0
  · subst ht
    rw [dslope_same, (hasDerivAt_neg_log_one_sub (by norm_num : (0 : ℝ) < 1)).deriv]
    simp
  · rw [dslope_of_ne _ ht, slope_def_field, dilogKer_of_ne ht]
    simp

lemma continuousOn_dilogKer : ContinuousOn dilogKer (Iio 1) := by
  intro t ht
  have ht : t < 1 := ht
  refine ContinuousAt.continuousWithinAt ?_
  rw [dilogKer_eq_dslope]
  by_cases h0 : t = 0
  · subst h0
    exact continuousAt_dslope_same.2 (hasDerivAt_neg_log_one_sub ht).differentiableAt
  · exact (continuousAt_dslope_of_ne h0).2 (hasDerivAt_neg_log_one_sub ht).continuousAt

lemma uIcc_zero_subset_Iio {x : ℝ} (hx : x < 1) : uIcc 0 x ⊆ Iio 1 := by
  intro t ht
  rw [mem_uIcc] at ht
  show t < 1
  rcases ht with h | h <;> linarith [h.2]

lemma intervalIntegrable_dilogKer {x : ℝ} (hx : x < 1) :
    IntervalIntegrable dilogKer volume 0 x :=
  (continuousOn_dilogKer.mono (uIcc_zero_subset_Iio hx)).intervalIntegrable

/-- `Li₂' = φ` on `(-∞, 1)`. -/
theorem hasDerivAt_Li₂ {x : ℝ} (hx : x < 1) : HasDerivAt Li₂ (dilogKer x) x :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_dilogKer hx)
    (continuousOn_dilogKer.stronglyMeasurableAtFilter isOpen_Iio x hx)
    (continuousOn_dilogKer.continuousAt (isOpen_Iio.mem_nhds hx))

lemma continuousOn_Li₂_Iio : ContinuousOn Li₂ (Iio 1) := fun _ hx =>
  (hasDerivAt_Li₂ hx).continuousAt.continuousWithinAt

/-! ### The power series -/

lemma hasSum_dilogKer {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => t ^ n / (n + 1)) (dilogKer t) := by
  by_cases h0 : t = 0
  · subst h0
    rw [dilogKer_zero]
    convert hasSum_ite_eq 0 (1 : ℝ) using 1
    funext n
    rcases n with _ | n <;> simp
  · rw [dilogKer_of_ne h0]
    convert (Real.hasSum_pow_div_log_of_abs_lt_one ht).div_const t using 1
    funext n
    field_simp
    ring

lemma abs_le_of_mem_uIcc {x t : ℝ} (ht : t ∈ uIcc 0 x) : |t| ≤ |x| := by
  rw [mem_uIcc] at ht
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

lemma hasSum_Li₂_of_abs_lt {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) (Li₂ x) := by
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) (t : ℝ) => t ^ n / ((n : ℝ) + 1)) (f := dilogKer) (a := 0) (b := x)
    (fun n _ => |x| ^ n)
    (fun n => (by fun_prop : Continuous fun t : ℝ => t ^ n / ((n : ℝ) + 1)).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t ht => by
      have ht' := abs_le_of_mem_uIcc (uIoc_subset_uIcc ht)
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
      calc |t| ^ n / ((n : ℝ) + 1) ≤ |t| ^ n := div_le_self (by positivity) (by
            have := n.cast_nonneg (α := ℝ); linarith)
        _ ≤ |x| ^ n := pow_le_pow_left₀ (abs_nonneg _) ht' n)
    (Eventually.of_forall fun t _ => summable_geometric_of_lt_one (abs_nonneg _) hx)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht =>
      hasSum_dilogKer ((abs_le_of_mem_uIcc (uIoc_subset_uIcc ht)).trans_lt hx))
  show HasSum _ (∫ t in (0 : ℝ)..x, dilogKer t)
  convert h using 1
  funext n
  rw [intervalIntegral.integral_div, integral_pow]
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    sub_zero]
  field_simp

/-- The kernel is integrable on `[-1, 1]` (it has a logarithmic singularity at `1`). -/
lemma intervalIntegrable_dilogKer_neg_one_one : IntervalIntegrable dilogKer volume (-1) 1 := by
  refine IntervalIntegrable.trans (b := 1 / 2) ?_ ?_
  · exact (continuousOn_dilogKer.mono fun t ht => by
      rw [mem_uIcc] at ht; show t < 1; rcases ht with h | h <;> linarith [h.2]).intervalIntegrable
  · have hlog : IntervalIntegrable (fun t => 2 * Real.log (1 - t)) volume (1 / 2) 1 := by
      have := (intervalIntegrable_log' (a := 1 / 2) (b := 0)).comp_sub_left 1
      norm_num at this
      exact this.const_mul 2
    refine hlog.mono_fun ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
    · rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      refine Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le (by norm_num)] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have htp : 0 < t := by linarith [ht.1]
      rw [dilogKer_of_ne ht0, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_neg, abs_mul,
        abs_of_pos htp, abs_two, div_le_iff₀ htp]
      have := abs_nonneg (Real.log (1 - t))
      nlinarith [ht.1]

lemma continuousOn_Li₂_Icc : ContinuousOn Li₂ (Icc (-1) 1) := by
  have h := continuousOn_primitive_interval' intervalIntegrable_dilogKer_neg_one_one
    (a := 0) (by rw [mem_uIcc]; left; norm_num)
  rwa [uIcc_of_le (by norm_num)] at h

lemma summable_one_div_succ_sq : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  exact this.congr fun k => by push_cast; rfl

lemma abs_pow_div_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    ‖x ^ (n + 1) / ((n : ℝ) + 1) ^ 2‖ ≤ |x| * (1 / ((n : ℝ) + 1) ^ 2) := by
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)]
  rw [mul_one_div]
  gcongr
  exact pow_le_of_le_one (abs_nonneg _) hx (Nat.succ_ne_zero n)

lemma summable_Li₂_series {x : ℝ} (hx : |x| ≤ 1) :
    Summable fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ 2 :=
  Summable.of_norm_bounded (summable_one_div_succ_sq.mul_left |x|) (abs_pow_div_le hx)

/-- **The power series**: `Li₂ x = ∑_{n ≥ 1} xⁿ/n²` for `|x| ≤ 1`. -/
theorem hasSum_Li₂ {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) (Li₂ x) := by
  have heq : EqOn (fun x : ℝ => ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) Li₂ (Icc (-1) 1) := by
    refine EqOn.of_subset_closure (s := Ioo (-1) 1) (fun y hy => ?_) ?_ continuousOn_Li₂_Icc
      Ioo_subset_Icc_self (by rw [closure_Ioo (by norm_num)])
    · exact (hasSum_Li₂_of_abs_lt (abs_lt.2 hy)).tsum_eq
    · refine continuousOn_tsum (u := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2)
        (fun n => by fun_prop) summable_one_div_succ_sq fun n y hy => ?_
      have hy' : |y| ≤ 1 := abs_le.2 hy
      exact (abs_pow_div_le hy' n).trans (by
        have := abs_nonneg y
        have h0 : 0 ≤ 1 / ((n : ℝ) + 1) ^ 2 := by positivity
        nlinarith)
  rw [← heq (abs_le.1 hx)]
  exact (summable_Li₂_series hx).hasSum

theorem Li₂_eq_tsum {x : ℝ} (hx : |x| ≤ 1) :
    Li₂ x = ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := (hasSum_Li₂ hx).tsum_eq.symm

lemma abs_Li₂_le {x : ℝ} (hx : |x| ≤ 1) : |Li₂ x| ≤ |x| * (π ^ 2 / 6) := by
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using this
  have hb : ∀ n : ℕ, |x ^ (n + 1) / ((n : ℝ) + 1) ^ 2| ≤ |x| * (1 / ((n : ℝ) + 1) ^ 2) :=
    fun n => by have := abs_pow_div_le hx n; rwa [Real.norm_eq_abs] at this
  have h1 := hasSum_le (fun n => (abs_le.1 (hb n)).2) (hasSum_Li₂ hx) (hz.mul_left |x|)
  have h2 := hasSum_le (fun n => (abs_le.1 (hb n)).1) (hz.mul_left |x|).neg (hasSum_Li₂ hx)
  rw [abs_le]
  constructor <;> linarith

/-! ### Functional equations -/

/-- **Duplication**: `Li₂ x + Li₂ (-x) = ½ Li₂ (x²)` for `|x| ≤ 1`. -/
theorem Li₂_add_Li₂_neg {x : ℝ} (hx : |x| ≤ 1) : Li₂ x + Li₂ (-x) = 1 / 2 * Li₂ (x ^ 2) := by
  have hx2 : |x ^ 2| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hx
  have hsum := (hasSum_Li₂ hx).add (hasSum_Li₂ (show |-x| ≤ 1 by rwa [abs_neg]))
  have hg : Function.Injective fun m : ℕ => 2 * m + 1 := fun a b h => by simpa using h
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ => 2 * m + 1) →
      x ^ (n + 1) / ((n : ℝ) + 1) ^ 2 + (-x) ^ (n + 1) / ((n : ℝ) + 1) ^ 2 = 0 := by
    intro n hn
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [Odd.neg_pow ⟨m, by omega⟩]; ring
    · exact absurd ⟨m, hm.symm⟩ hn
  rw [← hg.hasSum_iff hzero] at hsum
  have hhalf := (hasSum_Li₂ hx2).mul_left (1 / 2)
  refine hsum.unique (hhalf.congr_fun fun m => ?_)
  simp only [Function.comp]
  rw [Even.neg_pow ⟨m + 1, by ring⟩, ← pow_mul]
  push_cast
  field_simp
  ring_nf

lemma one_sub_div_sub_one {z : ℝ} (hz : z < 1) : 1 - z / (z - 1) = (1 - z)⁻¹ := by
  have : z - 1 ≠ 0 := by linarith
  have : 1 - z ≠ 0 := by linarith
  field_simp
  ring

lemma div_sub_one_lt_one {z : ℝ} (hz : z < 1) : z / (z - 1) < 1 := by
  rw [div_lt_one_of_neg (by linarith)]; linarith

/-- **Landen's identity**: `Li₂ z + Li₂ (z/(z-1)) = -½ log²(1-z)` for `z < 1`. -/
theorem Li₂_landen {z : ℝ} (hz : z < 1) :
    Li₂ z + Li₂ (z / (z - 1)) = -(1 / 2) * Real.log (1 - z) ^ 2 := by
  let h : ℝ → ℝ := fun z => Li₂ z + Li₂ (z / (z - 1)) + 1 / 2 * Real.log (1 - z) ^ 2
  have hd : ∀ z ∈ Iio (1 : ℝ), HasDerivAt h 0 z := by
    intro z hz
    have hz : z < 1 := hz
    have hz1 : z - 1 ≠ 0 := by linarith
    have hw : HasDerivAt (fun y => y / (y - 1)) ((1 * (z - 1) - z * 1) / (z - 1) ^ 2) z :=
      (hasDerivAt_id z).div ((hasDerivAt_id z).sub_const 1) hz1
    have hl : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - z)) z :=
      ((hasDerivAt_id z).const_sub 1).log (by simp; linarith)
    have hD := ((hasDerivAt_Li₂ hz).add ((hasDerivAt_Li₂ (div_sub_one_lt_one hz)).comp z hw)).add
      ((hl.pow 2).const_mul (1 / 2))
    refine hD.congr_deriv ?_
    by_cases h0 : z = 0
    · subst h0; simp
    · have hw0 : z / (z - 1) ≠ 0 := div_ne_zero h0 hz1
      have h1z : 1 - z ≠ 0 := by linarith
      rw [dilogKer_of_ne h0, dilogKer_of_ne hw0, one_sub_div_sub_one hz, Real.log_inv]
      field_simp
      ring
  have hconst := IsOpen.is_const_of_deriv_eq_zero (f := h) isOpen_Iio (convex_Iio 1).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) (x := z) (y := 0) hz (by norm_num)
  simp only [h, Li₂_zero, zero_div, sub_zero, Real.log_one] at hconst
  linarith

/-- **Inversion**: `Li₂ (-x) + Li₂ (-1/x) = -π²/6 - ½ log² x` for `x > 0`, given `Li₂(-1) = -π²/12`. -/
lemma Li₂_inversion_aux {x : ℝ} (hx : 0 < x) :
    Li₂ (-x) + Li₂ (-x⁻¹) + 1 / 2 * Real.log x ^ 2 = 2 * Li₂ (-1) := by
  let h : ℝ → ℝ := fun x => Li₂ (-x) + Li₂ (-x⁻¹) + 1 / 2 * Real.log x ^ 2
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt h 0 x := by
    intro x hx
    have hx : 0 < x := hx
    have h1 : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
    have h2 : HasDerivAt (fun y : ℝ => -y⁻¹) (-(-(x ^ 2)⁻¹)) x := (hasDerivAt_inv hx.ne').neg
    have hD := (((hasDerivAt_Li₂ (show -x < 1 by linarith)).comp x h1).add
      ((hasDerivAt_Li₂ (show -x⁻¹ < 1 by have := inv_pos.2 hx; linarith)).comp x h2)).add
      (((Real.hasDerivAt_log hx.ne').pow 2).const_mul (1 / 2))
    refine hD.congr_deriv ?_
    rw [dilogKer_of_ne (by linarith), dilogKer_of_ne (by simp; linarith)]
    have e : 1 - -x⁻¹ = (x + 1) / x := by field_simp; ring
    rw [sub_neg_eq_add, e, Real.log_div (by linarith) hx.ne', add_comm 1 x]
    field_simp
    ring
  have hconst := IsOpen.is_const_of_deriv_eq_zero (f := h) isOpen_Ioi (convex_Ioi 0).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) (x := x) (y := 1) hx (by norm_num)
  simp only [h, inv_one, Real.log_one] at hconst
  linarith

/-! ### Classical values -/

theorem Li₂_one : Li₂ 1 = π ^ 2 / 6 := by
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using this
  have h := hasSum_Li₂ (x := 1) (by norm_num)
  simp only [one_pow] at h
  exact h.unique hz

theorem Li₂_neg_one : Li₂ (-1) = -(π ^ 2 / 12) := by
  have h := Li₂_add_Li₂_neg (x := 1) (by norm_num)
  rw [one_pow, Li₂_one] at h
  linarith

theorem Li₂_half : Li₂ (1 / 2) = π ^ 2 / 12 - 1 / 2 * Real.log 2 ^ 2 := by
  have h := Li₂_landen (z := 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) / (1 / 2 - 1) = -1 by norm_num, Li₂_neg_one,
    show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_sq] at h
  linarith

theorem Li₂_quarter : Li₂ (1 / 4) = 2 * Li₂ (1 / 2) + 2 * Li₂ (-1 / 2) := by
  have h := Li₂_add_Li₂_neg (x := 1 / 2) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num, show -(1 / 2 : ℝ) = -1 / 2 by norm_num] at h
  linarith

/-- **Inversion**: `Li₂ (-x) + Li₂ (-1/x) = -π²/6 - ½ log² x` for `x > 0`. -/
theorem Li₂_inversion {x : ℝ} (hx : 0 < x) :
    Li₂ (-x) + Li₂ (-1 / x) = -(π ^ 2 / 6) - 1 / 2 * Real.log x ^ 2 := by
  have h := Li₂_inversion_aux hx
  rw [Li₂_neg_one] at h
  rw [neg_div, one_div]
  linarith

theorem Li₂_neg_two : Li₂ (-2) = -(π ^ 2 / 6) - 1 / 2 * Real.log 2 ^ 2 - Li₂ (-1 / 2) := by
  have h := Li₂_inversion (x := 2) (by norm_num)
  linarith

end ZetaF
