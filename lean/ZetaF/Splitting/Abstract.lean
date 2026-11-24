/-
# Theta splitting for an abstract kernel

This is the analytic heart of Theorem 3.2 (`thm:split`) of the paper, isolated from the specific kernel
`h_s`.  For a kernel `h` on `(0, ∞)` with
* `u^{-1/2} h(u)` integrable on `(0, u₀]`, and
* `e^{-k₀² u} h(u)` integrable on `(u₀, ∞)`,
we prove
`∑_{k ≥ k₀} ∫₀^∞ e^{-k²u} h = ∑_{k ≥ k₀} I_k + √π ∑_{m ≥ 1} J_m + M`
with `I_k = ∫_{u₀}^∞ e^{-k²u} h`, `J_m = ∫₀^{u₀} u^{-1/2} e^{-π²m²/u} h`,
`M = ∫₀^{u₀} (½√(π/u) - ½ - ∑_{k=1}^{k₀-1} e^{-k²u}) h`.
-/
import ZetaF.Theta

open Real MeasureTheory Set Filter Finset

namespace ZetaF

variable (h : ℝ → ℂ) (u₀ : ℝ)

/-- The `k`-term `I_k = ∫_{u₀}^∞ e^{-k²u} h(u) du`. -/
noncomputable def kTerm (k : ℕ) : ℂ := ∫ u in Ioi u₀, (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * h u

/-- The dual term `J_m = ∫₀^{u₀} u^{-1/2} e^{-π²m²/u} h(u) du`. -/
noncomputable def dualTerm (m : ℕ) : ℂ :=
  ∫ u in Ioc 0 u₀, ((u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 * (m : ℝ) ^ 2 / u)) : ℝ) : ℂ) * h u

/-- The weight of the main term, `½√(π/u) - ½ - ∑_{k=1}^{k₀-1} e^{-k²u}`. -/
noncomputable def mainWeight (k₀ : ℕ) (u : ℝ) : ℝ :=
  1 / 2 * √(π / u) - 1 / 2 - ∑ k ∈ Ico 1 k₀, rexp (-((k : ℝ) ^ 2 * u))

/-- The main term `M = ∫₀^{u₀} (½√(π/u) - ½ - ∑_{k<k₀} e^{-k²u}) h(u) du`. -/
noncomputable def mainTerm (k₀ : ℕ) : ℂ := ∫ u in Ioc 0 u₀, (mainWeight k₀ u : ℂ) * h u

variable {h u₀}

section integrability

variable (hcont : ContinuousOn h (Ioi 0))
include hcont

lemma aesm_weight_mul {w : ℝ → ℝ} (hw : ContinuousOn w (Ioi 0)) {s : Set ℝ} (hs : s ⊆ Ioi 0)
    (hms : MeasurableSet s) :
    AEStronglyMeasurable (fun u => (w u : ℂ) * h u) (volume.restrict s) :=
  ((Complex.continuous_ofReal.comp_continuousOn hw).mul hcont).mono hs
    |>.aestronglyMeasurable hms

lemma integrableOn_weight_mul_of_le {w g : ℝ → ℝ} (hw : ContinuousOn w (Ioi 0)) {s : Set ℝ}
    (hs : s ⊆ Ioi 0) (hms : MeasurableSet s) (hg : IntegrableOn (fun u => g u * ‖h u‖) s)
    (hle : ∀ u ∈ s, |w u| ≤ g u) : IntegrableOn (fun u => (w u : ℂ) * h u) s := by
  refine Integrable.mono' hg (aesm_weight_mul hcont hw hs hms) ?_
  refine (ae_restrict_iff' hms).2 (Eventually.of_forall fun u hu => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hle u hu) (norm_nonneg _)

end integrability

/-- `e^{-k²u} ≤ e^{-(k²-k₀²)u₀} e^{-k₀²u}` for `u ≥ u₀`, `k ≥ k₀`. -/
lemma exp_sq_le {k k₀ : ℝ} (hk : k₀ ≤ k) (hk₀ : 0 ≤ k₀) {u u₀ : ℝ} (hu : u₀ ≤ u) :
    rexp (-(k ^ 2 * u)) ≤ rexp (-((k ^ 2 - k₀ ^ 2) * u₀)) * rexp (-(k₀ ^ 2 * u)) := by
  rw [← exp_add, exp_le_exp]
  have : k₀ ^ 2 ≤ k ^ 2 := by nlinarith
  nlinarith

/-- Continuity of `u ↦ e^{-c u}`. -/
lemma continuous_expneg (c : ℝ) : Continuous fun u : ℝ => rexp (-(c * u)) := by fun_prop

lemma continuousOn_rpow_neg_half : ContinuousOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (Ioi 0) :=
  fun u hu => (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hu))).continuousWithinAt

lemma continuousOn_dualWeight (c : ℝ) :
    ContinuousOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u))) (Ioi 0) := by
  apply continuousOn_rpow_neg_half.mul
  apply ContinuousOn.rexp
  apply ContinuousOn.neg
  exact continuousOn_const.div continuousOn_id fun u hu => ne_of_gt hu

lemma continuousOn_mainWeight (k₀ : ℕ) : ContinuousOn (mainWeight k₀) (Ioi 0) := by
  have h1 : ContinuousOn (fun u : ℝ => 1 / 2 * √(π / u) - 1 / 2) (Ioi 0) :=
    (continuousOn_const.mul ((continuousOn_const.div continuousOn_id
      fun u hu => ne_of_gt hu).sqrt)).sub continuousOn_const
  have h2 : ContinuousOn (fun u : ℝ => ∑ k ∈ Ico 1 k₀, rexp (-((k : ℝ) ^ 2 * u))) (Ioi 0) :=
    continuousOn_finsetSum _ fun k _ => (continuous_expneg _).continuousOn
  exact h1.sub h2

/-- `1 ≤ √u₀ · u^{-1/2}` on `(0, u₀]`. -/
lemma one_le_rpow_neg_half {u u₀ : ℝ} (hu : 0 < u) (huu₀ : u ≤ u₀) :
    1 ≤ √u₀ * u ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.2 hu),
    one_mul]
  exact Real.sqrt_le_sqrt huu₀

lemma abs_mainWeight_le {k₀ : ℕ} {u : ℝ} (hu : 0 < u) :
    |mainWeight k₀ u| ≤ 1 / 2 * √π * u ^ (-(1 / 2 : ℝ)) + (k₀ + 1) := by
  rw [mainWeight]
  have h1 : ∑ k ∈ Ico 1 k₀, rexp (-((k : ℝ) ^ 2 * u)) ≤ (k₀ : ℝ) - 1 + 1 := by
    calc ∑ k ∈ Ico 1 k₀, rexp (-((k : ℝ) ^ 2 * u)) ≤ ∑ k ∈ Ico 1 k₀, (1 : ℝ) := by
          apply sum_le_sum; intro k _; rw [exp_le_one_iff]; have := sq_nonneg (k : ℝ); nlinarith
      _ ≤ (k₀ : ℝ) - 1 + 1 := by simp
  have h2 : 0 ≤ ∑ k ∈ Ico 1 k₀, rexp (-((k : ℝ) ^ 2 * u)) := sum_nonneg fun _ _ => (exp_pos _).le
  have h3 : √(π / u) = √π * u ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div' _ hu.le, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have h4 : 0 ≤ √(π / u) := Real.sqrt_nonneg _
  rw [abs_le]; constructor <;> nlinarith

/-- **Abstract theta splitting.** -/
theorem theta_split {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hu₀ : 0 < u₀) (hcont : ContinuousOn h (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖h u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀)) :
    HasSum (fun k : ℕ => ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u)
      (∑' k : ℕ, kTerm h u₀ (k + k₀) + √π * ∑' m : ℕ, dualTerm h u₀ (m + 1) + mainTerm h u₀ k₀) := by
  have hIoc : Ioc (0 : ℝ) u₀ ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hIoi : Ioi u₀ ⊆ Ioi 0 := Ioi_subset_Ioi hu₀.le
  set e : ℕ → ℝ → ℝ := fun k u => rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) with he
  have he_cont : ∀ k, ContinuousOn (e k) (Ioi 0) := fun k => (continuous_expneg _).continuousOn
  have he_pos : ∀ k u, 0 < e k u := fun k u => exp_pos _
  have he_le_one : ∀ k u, 0 ≤ u → e k u ≤ 1 := by
    intro k u hu; simp only [he, exp_le_one_iff, neg_nonpos]; positivity
  -- integrability of `‖h‖` near `0`
  have hnear' : IntegrableOn (fun u => ‖h u‖) (Ioc 0 u₀) := by
    refine Integrable.mono' (hnear.const_mul √u₀) ?_ ?_
    · exact (hcont.mono hIoc).norm.aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      rw [norm_norm, ← mul_assoc]
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_rpow_neg_half hu.1 hu.2)
  -- integrability of each piece
  have hint_near : ∀ k, IntegrableOn (fun u => (e k u : ℂ) * h u) (Ioc 0 u₀) := by
    intro k
    refine integrableOn_weight_mul_of_le hcont (he_cont k) hIoc measurableSet_Ioc
      (g := fun _ => 1) (by simpa using hnear') fun u hu => ?_
    rw [abs_of_pos (he_pos k u)]; exact he_le_one k u hu.1.le
  have hfar_bound : ∀ k u, u₀ ≤ u →
      e k u ≤ rexp (-(((((k + k₀ : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2) * u₀)) * rexp (-((k₀ : ℝ) ^ 2 * u)) :=
    fun k u hu => exp_sq_le (k := ((k + k₀ : ℕ) : ℝ)) (k₀ := (k₀ : ℝ))
      (Nat.cast_le.2 (Nat.le_add_left k₀ k)) (Nat.cast_nonneg _) hu
  have hint_far : ∀ k, IntegrableOn (fun u => (e k u : ℂ) * h u) (Ioi u₀) := by
    intro k
    set c := rexp (-(((((k + k₀ : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2) * u₀)) with hc
    have hg : IntegrableOn (fun u => c * rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀) := by
      have h' : IntegrableOn (fun u => c * (rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖)) (Ioi u₀) :=
        hfar.const_mul c
      simpa only [mul_assoc] using h'
    refine integrableOn_weight_mul_of_le hcont (he_cont k) hIoi measurableSet_Ioi hg
      fun u hu => ?_
    rw [abs_of_pos (he_pos k u)]; exact hfar_bound k u (le_of_lt hu)
  -- split each integral
  have hsplit : ∀ k, ∫ u in Ioi 0, (e k u : ℂ) * h u =
      (∫ u in Ioc 0 u₀, (e k u : ℂ) * h u) + kTerm h u₀ (k + k₀) := by
    intro k
    rw [← Ioc_union_Ioi_eq_Ioi hu₀.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint_near k) (hint_far k)]
    rfl
  -- the far part: summable norms
  have hfar_sum : HasSum (fun k => kTerm h u₀ (k + k₀)) (∑' k : ℕ, kTerm h u₀ (k + k₀)) := by
    apply Summable.hasSum
    set C := ∫ u in Ioi u₀, rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖
    refine Summable.of_norm_bounded (g := fun k : ℕ => C * rexp (-(u₀ * (k : ℝ) ^ 2))) ?_ ?_
    · exact (summable_exp_neg_mul_sq hu₀).mul_left C
    · intro k
      calc ‖kTerm h u₀ (k + k₀)‖ ≤ ∫ u in Ioi u₀, ‖(e k u : ℂ) * h u‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ u in Ioi u₀, rexp (-(u₀ * (k : ℝ) ^ 2)) *
              (rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) := by
            apply setIntegral_mono_on (hint_far k).norm (hfar.const_mul _) measurableSet_Ioi
            intro u hu
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (he_pos k u).le, ← mul_assoc]
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            refine (hfar_bound k u (le_of_lt hu)).trans ?_
            apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
            rw [exp_le_exp, neg_le_neg_iff]
            have hk2 : (k : ℝ) ^ 2 ≤ (((k + k₀ : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2 := by
              push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) k₀]
            nlinarith
        _ = C * rexp (-(u₀ * (k : ℝ) ^ 2)) := by
            rw [integral_const_mul]; ring
  -- the near part: interchange of sum and integral
  have hnear_sum_norm : Summable fun k => ∫ u in Ioc 0 u₀, ‖(e k u : ℂ) * h u‖ := by
    set C := ∫ u in Ioc 0 u₀, (1 / 2 + thetaDual u₀) * √π * (u ^ (-(1 / 2 : ℝ)) * ‖h u‖)
    refine summable_of_sum_range_le (c := C) (fun k => integral_nonneg fun _ => norm_nonneg _)
      fun N => ?_
    rw [← integral_finsetSum _ fun k _ => (hint_near k).norm]
    apply setIntegral_mono_on (integrable_finsetSum _ fun k _ => (hint_near k).norm)
      (hnear.const_mul _) measurableSet_Ioc
    intro u hu
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (he_pos _ _).le]
    rw [← sum_mul]
    have h1 : ∑ k ∈ range N, e k u ≤ theta1 u := by
      calc ∑ k ∈ range N, e k u ≤ ∑ k ∈ range N, rexp (-(((k : ℝ) + 1) ^ 2 * u)) := by
            apply sum_le_sum; intro k _
            simp only [he, exp_le_exp, neg_le_neg_iff]
            apply mul_le_mul_of_nonneg_right _ hu.1.le
            have : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
            push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]
        _ ≤ theta1 u := (summable_theta1 hu.1).sum_le_tsum _ (fun _ _ => (exp_pos _).le)
    have h2 := theta1_le hu.1 hu.2
    have h3 : (1 / 2 + thetaDual u₀) * √π / √u = (1 / 2 + thetaDual u₀) * √π * u ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hu.1.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    calc (∑ k ∈ range N, e k u) * ‖h u‖ ≤ ((1 / 2 + thetaDual u₀) * √π / √u) * ‖h u‖ :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (norm_nonneg _)
      _ = (1 / 2 + thetaDual u₀) * √π * (u ^ (-(1 / 2 : ℝ)) * ‖h u‖) := by rw [h3]; ring
  have hnear_hasSum := hasSum_integral_of_summable_integral_norm hint_near hnear_sum_norm
  -- `∑_{k ≥ k₀} e^{-k²u} = mainWeight + √(π/u) · thetaDual`
  have hsum_e : ∀ u, 0 < u → ∑' k, e k u = mainWeight k₀ u + √(π / u) * thetaDual u := by
    intro u hu
    have h1 := (summable_theta1 hu).sum_add_tsum_nat_add (k₀ - 1)
    have h2 : ∀ i, rexp (-((((i + (k₀ - 1) : ℕ) : ℝ) + 1) ^ 2 * u)) = e i u := by
      intro i; simp only [he]; congr 3; push_cast [Nat.cast_sub hk₀]; ring
    have h3 : ∑ i ∈ range (k₀ - 1), rexp (-(((i : ℝ) + 1) ^ 2 * u)) =
        ∑ k ∈ Ico 1 k₀, rexp (-((k : ℝ) ^ 2 * u)) := by
      rw [sum_Ico_eq_sum_range]; apply sum_congr rfl; intro i _; push_cast; ring_nf
    simp only [h2, h3] at h1
    have h4 : theta1 u = ∑' k : ℕ, rexp (-(((k : ℝ) + 1) ^ 2 * u)) := rfl
    have h5 := theta1_eq hu
    rw [mainWeight]
    linarith
  -- integrability of the two pieces
  have hint_main : IntegrableOn (fun u => (mainWeight k₀ u : ℂ) * h u) (Ioc 0 u₀) := by
    have hg : IntegrableOn (fun u => (1 / 2 * √π * u ^ (-(1 / 2 : ℝ)) + (k₀ + 1)) * ‖h u‖)
        (Ioc 0 u₀) := by
      refine ((hnear.const_mul (1 / 2 * √π)).add (hnear'.const_mul ((k₀ : ℝ) + 1))).congr
        (Eventually.of_forall fun u => ?_)
      simp only [Pi.add_apply]; ring
    exact integrableOn_weight_mul_of_le hcont (continuousOn_mainWeight k₀) hIoc measurableSet_Ioc
      hg fun u hu => abs_mainWeight_le hu.1
  set G : ℕ → ℝ → ℂ := fun m u =>
    ((u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) : ℝ) : ℂ) * h u with hG
  have hint_G : ∀ m, IntegrableOn (G m) (Ioc 0 u₀) := by
    intro m
    refine integrableOn_weight_mul_of_le hcont (continuousOn_dualWeight _) hIoc measurableSet_Ioc
      hnear fun u hu => ?_
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (exp_pos _).le)]
    apply mul_le_of_le_one_right (Real.rpow_nonneg hu.1.le _)
    rw [exp_le_one_iff, neg_nonpos]; exact div_nonneg (by positivity) hu.1.le
  have hG_sum_norm : Summable fun m => ∫ u in Ioc 0 u₀, ‖G m u‖ := by
    set C := ∫ u in Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * ‖h u‖
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_)
      ((summable_thetaDual hu₀).mul_right C)
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hint_G m).norm (hnear.const_mul _) measurableSet_Ioc
    intro u hu
    have hexp : rexp (-(π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) ≤
        rexp (-(π ^ 2 * ((m : ℝ) + 1) ^ 2 / u₀)) := by
      rw [exp_le_exp, neg_le_neg_iff]; push_cast
      exact div_le_div_of_nonneg_left (by positivity) hu.1 hu.2
    have hr := Real.rpow_nonneg hu.1.le (-(1 / 2 : ℝ))
    simp only [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hr, abs_of_pos (exp_pos _)]
    calc u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) * ‖h u‖
        = rexp (-(π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) * (u ^ (-(1 / 2 : ℝ)) * ‖h u‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (mul_nonneg hr (norm_nonneg _))
  have hG_hasSum := hasSum_integral_of_summable_integral_norm hint_G hG_sum_norm
  have hG_le : ∀ m, ∀ u ∈ Ioc 0 u₀,
      ‖G m u‖ ≤ rexp (-(π ^ 2 * ((m : ℝ) + 1) ^ 2 / u₀)) * (u ^ (-(1 / 2 : ℝ)) * ‖h u‖) := by
    intro m u hu
    have hexp : rexp (-(π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) ≤
        rexp (-(π ^ 2 * ((m : ℝ) + 1) ^ 2 / u₀)) := by
      rw [exp_le_exp, neg_le_neg_iff]; push_cast
      exact div_le_div_of_nonneg_left (by positivity) hu.1 hu.2
    have hr := Real.rpow_nonneg hu.1.le (-(1 / 2 : ℝ))
    simp only [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr, abs_of_pos (exp_pos _)]
    calc u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) * ‖h u‖
        = rexp (-(π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) * (u ^ (-(1 / 2 : ℝ)) * ‖h u‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (mul_nonneg hr (norm_nonneg _))
  have hint_dual : IntegrableOn (fun u => ∑' m, G m u) (Ioc 0 u₀) := by
    have hsumm : ∀ u ∈ Ioc 0 u₀, HasSum (fun m : ℕ => rexp (-(π ^ 2 * ((m : ℝ) + 1) ^ 2 / u₀)) *
        (u ^ (-(1 / 2 : ℝ)) * ‖h u‖)) (thetaDual u₀ * (u ^ (-(1 / 2 : ℝ)) * ‖h u‖)) :=
      fun u _ => (summable_thetaDual hu₀).hasSum.mul_right _
    refine Integrable.mono' (hnear.const_mul (thetaDual u₀)) ?_ ?_
    · refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun N u => ∑ m ∈ range N, G m u)
        (fun N => Finset.aestronglyMeasurable_fun_sum _ fun m _ => (hint_G m).1) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      exact (Summable.of_norm_bounded (hsumm u hu).summable fun m => hG_le m u hu).hasSum.tendsto_sum_nat
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      exact tsum_of_norm_bounded (hsumm u hu) fun m => hG_le m u hu
  -- pointwise identity on `(0, u₀]`
  have hpt : EqOn (fun u => ∑' k, (e k u : ℂ) * h u)
      (fun u => (mainWeight k₀ u : ℂ) * h u + (√π : ℂ) * ∑' m, G m u) (Ioc 0 u₀) := by
    intro u hu
    simp only [hG]
    rw [tsum_mul_right, ← Complex.ofReal_tsum, hsum_e u hu.1, tsum_mul_right, ← Complex.ofReal_tsum,
      tsum_mul_left]
    have : thetaDual u = ∑' m : ℕ, rexp (-(π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) := by
      unfold thetaDual; push_cast; rfl
    rw [← this, Real.sqrt_div' _ hu.1.le, Real.rpow_neg hu.1.le, ← Real.sqrt_eq_rpow]
    push_cast; ring
  have hnear_val : ∫ u in Ioc 0 u₀, ∑' k, (e k u : ℂ) * h u =
      mainTerm h u₀ k₀ + √π * ∑' m : ℕ, dualTerm h u₀ (m + 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add hint_main
      (hint_dual.const_mul _), integral_const_mul, ← hG_hasSum.tsum_eq]
    rfl
  have := hnear_hasSum.add hfar_sum
  rw [hnear_val] at this
  convert this using 1
  · funext k; exact hsplit k
  · ring

end ZetaF
