/-
# Theta splitting with complex coefficients (generalizes `theta_split`; used for Remark 3.6)

Let `c, d : ℕ → ℂ` be bounded and suppose the transformation
`∑_{k ≥ 1} c_k e^{-k²u} = α u^{-1/2} + β + u^{-1/2} ∑_{m ≥ 1} d_m e^{-λm²/u}` (`u > 0`).
Then for a kernel `h` as in `theta_split`,
`∑_{k≥k₀} c_k ∫₀^∞ e^{-k²u} h = ∑_{k≥k₀} c_k I_k + ∑_{m≥1} d_m J^λ_m + M`,
`J^λ_m = ∫₀^{u₀} u^{-1/2} e^{-λm²/u} h`, `M = ∫₀^{u₀} (α u^{-1/2} + β - ∑_{k<k₀} c_k e^{-k²u}) h`.
-/
import ZetaF.Splitting.Abstract
import ZetaF.Twisted.Theta
import ZetaF.Splitting.Kernel

open Real MeasureTheory Set Filter Finset

namespace ZetaF

variable {h : ℝ → ℂ} {u₀ : ℝ} {a : ℕ → ℂ} {R : ℝ}

/-- The generalized dual term `J^λ_m = ∫₀^{u₀} u^{-1/2} e^{-λm²/u} h(u) du`. -/
noncomputable def dualTermGen (h : ℝ → ℂ) (u₀ lam : ℝ) (m : ℕ) : ℂ :=
  ∫ u in Ioc 0 u₀, ((u ^ (-(1 / 2 : ℝ)) * rexp (-(lam * (m : ℝ) ^ 2 / u)) : ℝ) : ℂ) * h u

/-- The generalized main weight `α u^{-1/2} + β - ∑_{k<k₀} c_k e^{-k²u}`. -/
noncomputable def mainWeightGen (c : ℕ → ℂ) (α β : ℂ) (k₀ : ℕ) (u : ℝ) : ℂ :=
  α * (u ^ (-(1 / 2 : ℝ)) : ℝ) + β - ∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)

/-- The generalized main term. -/
noncomputable def mainTermGen (h : ℝ → ℂ) (u₀ : ℝ) (c : ℕ → ℂ) (α β : ℂ) (k₀ : ℕ) : ℂ :=
  ∫ u in Ioc 0 u₀, mainWeightGen c α β k₀ u * h u

lemma integrableOn_cweight_mul_of_le (hcont : ContinuousOn h (Ioi 0)) {W : ℝ → ℂ}
    (hW : ContinuousOn W (Ioi 0)) {g : ℝ → ℝ} {S : Set ℝ} (hS : S ⊆ Ioi 0) (hmS : MeasurableSet S)
    (hg : IntegrableOn (fun u => g u * ‖h u‖) S) (hle : ∀ u ∈ S, ‖W u‖ ≤ g u) :
    IntegrableOn (fun u => W u * h u) S := by
  refine Integrable.mono' hg ((hW.mul hcont).mono hS |>.aestronglyMeasurable hmS) ?_
  refine (ae_restrict_iff' hmS).2 (Eventually.of_forall fun u hu => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hle u hu) (norm_nonneg _)

/-- **Abstract theta splitting with complex coefficients.** -/
theorem theta_split_gen {c d : ℕ → ℂ} {B B' : ℝ} (hc : ∀ k, ‖c k‖ ≤ B) (hd : ∀ m, ‖d m‖ ≤ B')
    {lam : ℝ} (hlam : 0 < lam) {α β : ℂ}
    (hθ : ∀ u : ℝ, 0 < u → ∑' k : ℕ, c (k + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      α * (u ^ (-(1 / 2 : ℝ)) : ℝ) + β + (u ^ (-(1 / 2 : ℝ)) : ℝ) *
        ∑' m : ℕ, d (m + 1) * (rexp (-(lam * ((m : ℝ) + 1) ^ 2 / u)) : ℂ))
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hu₀ : 0 < u₀) (hcont : ContinuousOn h (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖h u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀)) :
    HasSum (fun k : ℕ => c (k + k₀) *
        ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u)
      (∑' k : ℕ, c (k + k₀) * kTerm h u₀ (k + k₀) + ∑' m : ℕ, d (m + 1) * dualTermGen h u₀ lam (m + 1) +
        mainTermGen h u₀ c α β k₀) := by
  have hIoc : Ioc (0 : ℝ) u₀ ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hIoi : Ioi u₀ ⊆ Ioi 0 := Ioi_subset_Ioi hu₀.le
  set e : ℕ → ℝ → ℝ := fun k u => rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) with he
  have he_cont : ∀ k, ContinuousOn (e k) (Ioi 0) := fun k => (continuous_expneg _).continuousOn
  have he_pos : ∀ k u, 0 < e k u := fun k u => exp_pos _
  have he_le_one : ∀ k u, 0 ≤ u → e k u ≤ 1 := by
    intro k u hu; simp only [he, exp_le_one_iff, neg_nonpos]; positivity
  have hB : 0 ≤ B := (norm_nonneg _).trans (hc 0)
  have hB' : 0 ≤ B' := (norm_nonneg _).trans (hd 0)
  have hnear' : IntegrableOn (fun u => ‖h u‖) (Ioc 0 u₀) := by
    refine Integrable.mono' (hnear.const_mul √u₀) ?_ ?_
    · exact (hcont.mono hIoc).norm.aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      rw [norm_norm, ← mul_assoc]
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_rpow_neg_half hu.1 hu.2)
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
    set c' := rexp (-(((((k + k₀ : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2) * u₀))
    have hg : IntegrableOn (fun u => c' * rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀) := by
      have h' : IntegrableOn (fun u => c' * (rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖)) (Ioi u₀) :=
        hfar.const_mul c'
      simpa only [mul_assoc] using h'
    refine integrableOn_weight_mul_of_le hcont (he_cont k) hIoi measurableSet_Ioi hg
      fun u hu => ?_
    rw [abs_of_pos (he_pos k u)]; exact hfar_bound k u (le_of_lt hu)
  have hsplit : ∀ k, c (k + k₀) * ∫ u in Ioi 0, (e k u : ℂ) * h u =
      c (k + k₀) * (∫ u in Ioc 0 u₀, (e k u : ℂ) * h u) + c (k + k₀) * kTerm h u₀ (k + k₀) := by
    intro k
    rw [← mul_add, ← Ioc_union_Ioi_eq_Ioi hu₀.le, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hint_near k) (hint_far k)]
    rfl
  -- far part
  have hfar_sum : HasSum (fun k => c (k + k₀) * kTerm h u₀ (k + k₀))
      (∑' k : ℕ, c (k + k₀) * kTerm h u₀ (k + k₀)) := by
    apply Summable.hasSum
    set C := ∫ u in Ioi u₀, rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖
    refine Summable.of_norm_bounded (g := fun k : ℕ => B * (C * rexp (-(u₀ * (k : ℝ) ^ 2))))
      (((summable_exp_neg_mul_sq hu₀).mul_left C).mul_left B) fun k => ?_
    rw [norm_mul]
    refine mul_le_mul (hc _) ?_ (norm_nonneg _) hB
    calc ‖kTerm h u₀ (k + k₀)‖ ≤ ∫ u in Ioi u₀, ‖(e k u : ℂ) * h u‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u in Ioi u₀, rexp (-(u₀ * (k : ℝ) ^ 2)) * (rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) := by
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
      _ = C * rexp (-(u₀ * (k : ℝ) ^ 2)) := by rw [integral_const_mul]; ring
  -- near part
  have hnear_sum_norm0 : Summable fun k => ∫ u in Ioc 0 u₀, ‖(e k u : ℂ) * h u‖ := by
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
  have hFint : ∀ k, IntegrableOn (fun u => c (k + k₀) * ((e k u : ℂ) * h u)) (Ioc 0 u₀) :=
    fun k => (hint_near k).const_mul _
  have hnear_sum_norm : Summable fun k =>
      ∫ u in Ioc 0 u₀, ‖c (k + k₀) * ((e k u : ℂ) * h u)‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_) (hnear_sum_norm0.mul_left B)
    simp only [norm_mul (c _)]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right (hc _) (integral_nonneg fun _ => norm_nonneg _)
  have hnear_hasSum := hasSum_integral_of_summable_integral_norm hFint hnear_sum_norm
  simp only [integral_const_mul] at hnear_hasSum
  -- pointwise identity for the coefficient series
  have hcs : ∀ u, 0 < u → Summable fun k : ℕ => c (k + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) :=
    fun u hu => Summable.of_norm_bounded ((summable_theta1 hu).mul_left B) fun k => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (hc _) (exp_pos _).le
  have hsum_e : ∀ u, 0 < u → ∑' k, c (k + k₀) * (e k u : ℂ) =
      mainWeightGen c α β k₀ u + (u ^ (-(1 / 2 : ℝ)) : ℝ) *
        ∑' m : ℕ, d (m + 1) * (rexp (-(lam * ((m : ℝ) + 1) ^ 2 / u)) : ℂ) := by
    intro u hu
    have h1 := (hcs u hu).sum_add_tsum_nat_add (k₀ - 1)
    have h2 : ∀ i, c (i + (k₀ - 1) + 1) * (rexp (-((((i + (k₀ - 1) : ℕ) : ℝ) + 1) ^ 2 * u)) : ℂ) =
        c (i + k₀) * (e i u : ℂ) := by
      intro i
      rw [show i + (k₀ - 1) + 1 = i + k₀ by omega]
      simp only [he]; congr 4; push_cast [Nat.cast_sub hk₀]; ring
    have h3 : ∑ i ∈ range (k₀ - 1), c (i + 1) * (rexp (-(((i : ℝ) + 1) ^ 2 * u)) : ℂ) =
        ∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) := by
      rw [sum_Ico_eq_sum_range]; apply sum_congr rfl; intro i _
      rw [add_comm 1 i]; push_cast; ring_nf
    simp only [h2, h3] at h1
    rw [hθ u hu] at h1
    rw [mainWeightGen]
    linear_combination h1
  -- dual series
  set G : ℕ → ℝ → ℂ := fun m u =>
    ((u ^ (-(1 / 2 : ℝ)) * rexp (-(lam * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) : ℝ) : ℂ) * h u with hG
  have hint_G : ∀ m, IntegrableOn (G m) (Ioc 0 u₀) := by
    intro m
    refine integrableOn_weight_mul_of_le hcont (continuousOn_dualWeight _) hIoc measurableSet_Ioc
      hnear fun u hu => ?_
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (exp_pos _).le)]
    apply mul_le_of_le_one_right (Real.rpow_nonneg hu.1.le _)
    rw [exp_le_one_iff, neg_nonpos]; exact div_nonneg (by positivity) hu.1.le
  have hdual_sum : Summable fun m : ℕ => rexp (-(lam / u₀ * ((m : ℝ) + 1) ^ 2)) :=
    summable_exp_neg_mul_sq_succ (by positivity)
  have hG_le : ∀ m, ∀ u ∈ Ioc 0 u₀,
      ‖d (m + 1) * G m u‖ ≤ B' * (rexp (-(lam / u₀ * ((m : ℝ) + 1) ^ 2)) *
        (u ^ (-(1 / 2 : ℝ)) * ‖h u‖)) := by
    intro m u hu
    have hexp : rexp (-(lam * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) ≤
        rexp (-(lam / u₀ * ((m : ℝ) + 1) ^ 2)) := by
      rw [exp_le_exp, neg_le_neg_iff]; push_cast
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) hu.1 hu.2
    have hr := Real.rpow_nonneg hu.1.le (-(1 / 2 : ℝ))
    calc ‖d (m + 1) * G m u‖ = ‖d (m + 1)‖ * (rexp (-(lam * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) *
          (u ^ (-(1 / 2 : ℝ)) * ‖h u‖)) := by
          simp only [hG, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (mul_nonneg hr (exp_pos _).le)]; ring
      _ ≤ _ := mul_le_mul (hd _) (mul_le_mul_of_nonneg_right hexp (mul_nonneg hr (norm_nonneg _)))
          (by positivity) hB'
  have hDint : ∀ m, IntegrableOn (fun u => d (m + 1) * G m u) (Ioc 0 u₀) :=
    fun m => (hint_G m).const_mul _
  have hD_sum_norm : Summable fun m => ∫ u in Ioc 0 u₀, ‖d (m + 1) * G m u‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_)
      ((hdual_sum.mul_right (∫ u in Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * ‖h u‖)).mul_left B')
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_mono_on (hDint m).norm ((hnear.const_mul _).const_mul _) measurableSet_Ioc
    exact hG_le m
  have hD_hasSum := hasSum_integral_of_summable_integral_norm hDint hD_sum_norm
  have hint_D : IntegrableOn (fun u => ∑' m, d (m + 1) * G m u) (Ioc 0 u₀) := by
    have hsumm : ∀ u ∈ Ioc 0 u₀, HasSum (fun m : ℕ => B' * (rexp (-(lam / u₀ * ((m : ℝ) + 1) ^ 2)) *
        (u ^ (-(1 / 2 : ℝ)) * ‖h u‖))) (B' * ((∑' m : ℕ, rexp (-(lam / u₀ * ((m : ℝ) + 1) ^ 2))) *
          (u ^ (-(1 / 2 : ℝ)) * ‖h u‖))) :=
      fun u _ => (hdual_sum.hasSum.mul_right _).mul_left _
    refine Integrable.mono' ((hnear.const_mul (∑' m : ℕ, rexp (-(lam / u₀ * ((m : ℝ) + 1) ^ 2)))).const_mul B')
      ?_ ?_
    · refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun N u => ∑ m ∈ range N, d (m + 1) * G m u)
        (fun N => Finset.aestronglyMeasurable_fun_sum _ fun m _ => (hDint m).1) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      exact (Summable.of_norm_bounded (hsumm u hu).summable fun m => hG_le m u hu).hasSum.tendsto_sum_nat
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      exact tsum_of_norm_bounded (hsumm u hu) fun m => hG_le m u hu
  have hcontW : ContinuousOn (mainWeightGen c α β k₀) (Ioi 0) := by
    unfold mainWeightGen
    refine ContinuousOn.sub (ContinuousOn.add (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn continuousOn_rpow_neg_half)) continuousOn_const) ?_
    exact continuousOn_finsetSum _ fun k _ => continuousOn_const.mul
      (Complex.continuous_ofReal.comp (continuous_expneg _)).continuousOn
  have hint_main : IntegrableOn (fun u => mainWeightGen c α β k₀ u * h u) (Ioc 0 u₀) := by
    have hg : IntegrableOn (fun u => (‖α‖ * u ^ (-(1 / 2 : ℝ)) + (‖β‖ + k₀ * B)) * ‖h u‖)
        (Ioc 0 u₀) := by
      refine ((hnear.const_mul ‖α‖).add (hnear'.const_mul (‖β‖ + k₀ * B))).congr
        (Eventually.of_forall fun u => ?_)
      simp only [Pi.add_apply]; ring
    refine integrableOn_cweight_mul_of_le hcont hcontW hIoc measurableSet_Ioc hg fun u hu => ?_
    have h1 : ‖α * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ = ‖α‖ * u ^ (-(1 / 2 : ℝ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _)]
    have h2 : ‖∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)‖ ≤ k₀ * B := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ B fun k _ => ?_).trans ?_
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
        calc ‖c k‖ * rexp (-((k : ℝ) ^ 2 * u)) ≤ B * 1 := by
              refine mul_le_mul (hc k) ?_ (exp_pos _).le hB
              rw [exp_le_one_iff, neg_nonpos]; exact mul_nonneg (sq_nonneg _) hu.1.le
          _ = B := mul_one B
      · rw [nsmul_eq_mul, Nat.card_Ico]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) hB
    calc ‖mainWeightGen c α β k₀ u‖ ≤ ‖α * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ + ‖β‖ +
          ‖∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by rw [h1]; linarith [h2]
  -- pointwise identity of the near integrand
  have hpt : EqOn (fun u => ∑' k, c (k + k₀) * ((e k u : ℂ) * h u))
      (fun u => mainWeightGen c α β k₀ u * h u + ∑' m, d (m + 1) * G m u) (Ioc 0 u₀) := by
    intro u hu
    simp only [hG]
    rw [show (fun k => c (k + k₀) * ((e k u : ℂ) * h u)) = fun k => c (k + k₀) * (e k u : ℂ) * h u
      from funext fun k => by ring, tsum_mul_right, hsum_e u hu.1, add_mul]
    congr 1
    rw [show (fun m => d (m + 1) * (((u ^ (-(1 / 2 : ℝ)) * rexp (-(lam * ((m + 1 : ℕ) : ℝ) ^ 2 / u)) :
      ℝ) : ℂ) * h u)) = fun m => ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * h u *
        (d (m + 1) * (rexp (-(lam * ((m : ℝ) + 1) ^ 2 / u)) : ℂ)) from funext fun m => by
          push_cast; ring, tsum_mul_left]
    ring
  have hnear_val : ∫ u in Ioc 0 u₀, ∑' k, c (k + k₀) * ((e k u : ℂ) * h u) =
      mainTermGen h u₀ c α β k₀ + ∑' m : ℕ, d (m + 1) * dualTermGen h u₀ lam (m + 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add hint_main hint_D,
      ← hD_hasSum.tsum_eq]
    congr 1
    congr 1; funext m
    rw [integral_const_mul]; rfl
  have := hnear_hasSum.add hfar_sum
  rw [hnear_val] at this
  convert this using 1
  · funext k; exact hsplit k
  · ring

/-! ### Even periodic twists -/

lemma gaussSum_norm_le {q : ℕ} (χ : ℤ → ℂ) (n : ℤ) :
    ‖gaussSum q χ n‖ ≤ ∑ a ∈ range q, ‖χ a‖ := by
  unfold gaussSum
  refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _) (le_of_eq _)
  rw [show 2 * π * Complex.I * (n : ℂ) * ((a : ℝ) : ℂ) / q = ((2 * π * n * a / q : ℝ) : ℂ) *
    Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The dual coefficients `(√π/q) χ̂(m)` of an even `q`-periodic twist. -/
noncomputable def charDual (q : ℕ) (χ : ℤ → ℂ) (m : ℕ) : ℂ := ((√π / q : ℝ) : ℂ) * gaussSum q χ m

/-- The main-term constants of an even `q`-periodic twist. -/
noncomputable def charAlpha (q : ℕ) (χ : ℤ → ℂ) : ℂ := ((1 / 2 * (√π / q) : ℝ) : ℂ) * gaussSum q χ 0

/-- **Twisted splitting** (abstract form, Section 5 of the paper, even case).  For an even
`q`-periodic `χ` the tail `∑_{k ≥ k₀} χ(k) ∫₀^∞ e^{-k²u} h(u) du` splits into the far part, the dual
part with coefficients `(√π/q) χ̂(m)` and Gaussian exponent `π²m²/(q²u)`, and the main term with
weight `½(√π/q) χ̂(0) u^{-1/2} - ½ χ(0) - ∑_{k < k₀} χ(k) e^{-k²u}`. -/
theorem theta_split_char {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (heven : ∀ k, χ (-k) = χ k)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hu₀ : 0 < u₀) (hcont : ContinuousOn h (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖h u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀)) :
    HasSum (fun k : ℕ => χ ((k + k₀ : ℕ) : ℤ) *
        ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u)
      (∑' k : ℕ, χ ((k + k₀ : ℕ) : ℤ) * kTerm h u₀ (k + k₀) +
        ∑' m : ℕ, charDual q χ (m + 1) * dualTermGen h u₀ (π ^ 2 / q ^ 2) (m + 1) +
        mainTermGen h u₀ (fun k => χ k) (charAlpha q χ) (-(1 / 2) * χ 0) k₀) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : ∀ k : ℕ, ‖χ k‖ ≤ ∑ a ∈ range q, ‖χ a‖ := fun k => periodic_bound hq hper k
  have hd : ∀ m : ℕ, ‖charDual q χ m‖ ≤ √π / q * ∑ a ∈ range q, ‖χ a‖ := fun m => by
    rw [charDual, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (gaussSum_norm_le χ m) (by positivity)
  refine theta_split_gen (c := fun k => χ k) hc hd (lam := π ^ 2 / q ^ 2) (by positivity)
    (fun u hu => ?_) hk₀ hu₀ hcont hnear hfar
  have h := tsum_char_theta_half hq hper heven hu
  simp only [Nat.cast_add, Nat.cast_one]
  rw [h, charAlpha]
  have hexp : ∀ n : ℕ, (rexp (-(π ^ 2 * ((n : ℝ) + 1) ^ 2 / (q ^ 2 * u))) : ℂ) =
      (rexp (-(π ^ 2 / q ^ 2 * ((n : ℝ) + 1) ^ 2 / u)) : ℂ) := fun n => by
    congr 3; field_simp
  simp only [hexp, charDual]
  rw [show (fun m : ℕ => ((√π / q : ℝ) : ℂ) * gaussSum q χ ((m + 1 : ℕ) : ℤ) *
      (rexp (-(π ^ 2 / q ^ 2 * ((m : ℝ) + 1) ^ 2 / u)) : ℂ)) = fun m : ℕ => ((√π / q : ℝ) : ℂ) *
      (gaussSum q χ ((m : ℤ) + 1) * (rexp (-(π ^ 2 / q ^ 2 * ((m : ℝ) + 1) ^ 2 / u)) : ℂ)) from
      funext fun m => by push_cast; ring, tsum_mul_left]
  push_cast; ring

/-- The twisted tail `∑_{k ≥ k₀} χ(k) F(k) k^{-s}` for `Re s > 1`, as an `LSeries`. -/
theorem zetaTail_split_char (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {s : ℂ} (hs : 1 < s.re)
    {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q) (heven : ∀ k, χ (-k) = χ k)
    (hu₀ : 0 < u₀) :
    zetaTail (fun k => χ k * F k) k₀ s =
      ∑' k : ℕ, χ ((k + k₀ : ℕ) : ℤ) * kTerm (kernel a s) u₀ (k + k₀) +
        ∑' m : ℕ, charDual q χ (m + 1) * dualTermGen (kernel a s) u₀ (π ^ 2 / q ^ 2) (m + 1) +
        mainTermGen (kernel a s) u₀ (fun k => χ k) (charAlpha q χ) (-(1 / 2) * χ 0) k₀ := by
  have hs0 : 0 < s.re := by linarith
  have hspl := theta_split_char (h := kernel a s) hq hper heven hk₀ hu₀
    (continuousOn_kernel ha hR hs0) (integrableOn_rpow_neg_half_mul_norm_kernel ha hR hs hu₀)
    ((integrableOn_exp_mul_norm_kernel ha hR hs0 hRk).mono_set (Ioi_subset_Ioi hu₀.le))
  have hterm : ∀ k : ℕ, χ ((k + k₀ : ℕ) : ℤ) *
      ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * kernel a s u =
      LSeries.term (tail k₀ (fun k => χ k * F k)) s (k + k₀) := by
    intro k
    have hK : (k + k₀ : ℕ) ≠ 0 := by omega
    have hRK : R < ((k + k₀ : ℕ) : ℝ) := lt_of_lt_of_le hRk (by exact_mod_cast Nat.le_add_left k₀ k)
    have h1 := (hasSum_laplace_kernel ha hR hs0 hRK).tsum_eq
    rw [← h1, LSeries.term_of_ne_zero hK, tail, ite_eq_left (Nat.le_add_left k₀ k),
      hF _ (Nat.le_add_left k₀ k), evalInv]
    push_cast
    simp_rw [show ((k : ℂ) + k₀) = ((k + k₀ : ℕ) : ℂ) by push_cast; ring]
    simp_rw [natCast_cpow_neg_add hK]
    rw [mul_div_assoc, div_eq_mul_inv, ← tsum_mul_right]
    congr 2; funext n; ring
  simp only [hterm] at hspl
  have hzero : ∑ i ∈ Finset.range k₀, LSeries.term (tail k₀ (fun k => χ k * F k)) s i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [LSeries.term, tail, show ¬ k₀ ≤ i by omega]
  have hfull := (hasSum_nat_add_iff' (f := LSeries.term (tail k₀ (fun k => χ k * F k)) s) k₀).1
    (by rw [hzero, sub_zero]; exact hspl)
  rw [zetaTail, LSeries, hfull.tsum_eq]

end ZetaF
