/-
# A general splitting lemma with linearly growing coefficients

`split_theta_lin`: the abstract splitting of `∑_{k ≥ k₀} c_k ∫₀^∞ e^{-k²u} h(u) du` for coefficients
with `|c_k| ≤ B(k+1)`, any theta transformation `∑_{k≥1} c_k e^{-k²u} = W₀(u) + ∑_m D_m(u)` on
`(0, u₀]`, and dual terms dominated by `b_m g(u)`.  Used for the geometric factors of Theorem 4.1.
-/
import ZetaF.Twisted.SplitOdd

open Real MeasureTheory Set Filter Finset

namespace ZetaF

variable {h : ℝ → ℂ} {u₀ : ℝ}

/-- **General splitting.** -/
theorem split_theta_lin {c : ℕ → ℂ} {B : ℝ} (hc : ∀ k, ‖c k‖ ≤ B * ((k : ℝ) + 1))
    {D : ℕ → ℝ → ℂ} {W₀ : ℝ → ℂ}
    (hθ : ∀ u ∈ Ioc 0 u₀, ∑' k : ℕ, c (k + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      W₀ u + ∑' m, D m u)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hu₀ : 0 < u₀) (hcont : ContinuousOn h (Ioi 0))
    (hn1 : IntegrableOn (fun u => u⁻¹ * ‖h u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀))
    (hD_cont : ∀ m, ContinuousOn (D m) (Ioi 0)) {b : ℕ → ℝ} {g : ℝ → ℝ} (hb : Summable b)
    (hg : IntegrableOn (fun u => g u * ‖h u‖) (Ioc 0 u₀))
    (hDb : ∀ m, ∀ u ∈ Ioc 0 u₀, ‖D m u‖ ≤ b m * g u)
    (hW₀c : ContinuousOn W₀ (Ioi 0)) {A : ℝ} (hW₀b : ∀ u ∈ Ioc 0 u₀, ‖W₀ u‖ ≤ A) :
    Summable (fun k : ℕ => c (k + k₀) * kTerm h u₀ (k + k₀)) ∧
    Summable (fun m => ∫ u in Ioc 0 u₀, D m u * h u) ∧
    HasSum (fun k : ℕ => c (k + k₀) *
        ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u)
      ((∑' k : ℕ, c (k + k₀) * kTerm h u₀ (k + k₀)) + (∑' m, ∫ u in Ioc 0 u₀, D m u * h u) +
        ∫ u in Ioc 0 u₀, (W₀ u - ∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) * h u) := by
  have hIoc : Ioc (0 : ℝ) u₀ ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hIoi : Ioi u₀ ⊆ Ioi 0 := Ioi_subset_Ioi hu₀.le
  have hB : 0 ≤ B := by
    have := (norm_nonneg _).trans (hc 0); simpa using this
  set e : ℕ → ℝ → ℝ := fun k u => rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) with he
  have he_pos : ∀ k u, 0 < e k u := fun k u => exp_pos _
  have he_le_one : ∀ k u, 0 ≤ u → e k u ≤ 1 := by
    intro k u hu; simp only [he, exp_le_one_iff, neg_nonpos]; positivity
  set E : ℕ → ℝ → ℂ := fun k u => c (k + k₀) * (e k u : ℂ) with hE
  have hE_cont : ∀ k, ContinuousOn (E k) (Ioi 0) := fun k =>
    continuousOn_const.mul (Complex.continuous_ofReal.comp (continuous_expneg _)).continuousOn
  have hnorm_E : ∀ k u, ‖E k u‖ = ‖c (k + k₀)‖ * e k u := fun k u => by
    rw [hE, norm_mul, Complex.norm_real, Real.norm_of_nonneg (he_pos k u).le]
  have hn0 : IntegrableOn (fun u => ‖h u‖) (Ioc 0 u₀) := by
    refine Integrable.mono' (hn1.const_mul u₀) ?_ ?_
    · exact (hcont.mono hIoc).norm.aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      rw [norm_norm, ← mul_assoc]
      refine le_mul_of_one_le_left (norm_nonneg _) ?_
      rw [← div_eq_mul_inv]; exact (one_le_div hu.1).2 hu.2
  -- far estimate
  have hfar_bound : ∀ k u, u₀ ≤ u →
      e k u ≤ rexp (-(((((k + k₀ : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2) * u₀)) *
        rexp (-((k₀ : ℝ) ^ 2 * u)) :=
    fun k u hu => exp_sq_le (k := ((k + k₀ : ℕ) : ℝ)) (k₀ := (k₀ : ℝ))
      (Nat.cast_le.2 (Nat.le_add_left k₀ k)) (Nat.cast_nonneg _) hu
  have hexp_far : ∀ k : ℕ, rexp (-(((((k + k₀ : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2) * u₀)) ≤
      rexp (-(u₀ * (k : ℝ) ^ 2)) := fun k => by
    rw [exp_le_exp, neg_le_neg_iff]
    have hk2 : (k : ℝ) ^ 2 ≤ (((k + k₀ : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2 := by
      push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) k₀]
    nlinarith
  have hEnear : ∀ k, IntegrableOn (fun u => E k u * h u) (Ioc 0 u₀) := by
    intro k
    refine integrableOn_cweight_mul_of_le hcont (hE_cont k) hIoc measurableSet_Ioc
      (g := fun _ => ‖c (k + k₀)‖) (hn0.const_mul _) fun u hu => ?_
    rw [hnorm_E]; exact mul_le_of_le_one_right (norm_nonneg _) (he_le_one k u hu.1.le)
  have hEfar : ∀ k, IntegrableOn (fun u => E k u * h u) (Ioi u₀) := by
    intro k
    set c' := ‖c (k + k₀)‖ * rexp (-(((((k + k₀ : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2) * u₀))
    have hg : IntegrableOn (fun u => c' * rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀) := by
      have h' : IntegrableOn (fun u => c' * (rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖)) (Ioi u₀) :=
        hfar.const_mul c'
      simpa only [mul_assoc] using h'
    refine integrableOn_cweight_mul_of_le hcont (hE_cont k) hIoi measurableSet_Ioi hg
      fun u hu => ?_
    rw [hnorm_E, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hfar_bound k u (le_of_lt hu)) (norm_nonneg _)
  -- summability of the near norms
  have hEsum : Summable fun k => ∫ u in Ioc 0 u₀, ‖E k u * h u‖ := by
    set M := 2 * B * ((1 / 2 + thetaDual u₀) * √π * √2) with hM
    refine summable_of_sum_range_le (c := ∫ u in Ioc 0 u₀, M * (u⁻¹ * ‖h u‖))
      (fun k => integral_nonneg fun _ => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ fun k _ => (hEnear k).norm]
    apply setIntegral_mono_on (integrable_finsetSum _ fun k _ => (hEnear k).norm)
      (hn1.const_mul _) measurableSet_Ioc
    intro u hu
    have hu0 := hu.1
    have hu2 : u / 2 ≤ u₀ := by linarith [hu.2]
    simp only [norm_mul (E _ _), hnorm_E]
    rw [← sum_mul]
    have h1 : ∑ k ∈ range N, ‖c (k + k₀)‖ * e k u ≤ 2 * B / √u * theta1 (u / 2) := by
      calc ∑ k ∈ range N, ‖c (k + k₀)‖ * e k u
          ≤ ∑ k ∈ range N, 2 * B / √u * rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) := by
            apply sum_le_sum; intro k _
            have hck := hc (k + k₀)
            have hK1 : (1 : ℝ) ≤ ((k + k₀ : ℕ) : ℝ) := by
              have : 1 ≤ k + k₀ := by omega
              exact_mod_cast this
            have hck' : ‖c (k + k₀)‖ ≤ 2 * B * ((k + k₀ : ℕ) : ℝ) := by
              refine hck.trans ?_; nlinarith
            have hab := abs_mul_exp_neg_sq_le (((k + k₀ : ℕ) : ℝ)) hu0
            rw [abs_of_nonneg (Nat.cast_nonneg _)] at hab
            have hmono : rexp (-(u / 2 * (((k + k₀ : ℕ) : ℝ)) ^ 2)) ≤
                rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) := by
              rw [exp_le_exp, neg_le_neg_iff]
              have : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
              have : ((k : ℝ) + 1) ^ 2 ≤ (((k + k₀ : ℕ) : ℝ)) ^ 2 := by
                push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]
              nlinarith
            calc ‖c (k + k₀)‖ * e k u ≤ 2 * B * ((((k + k₀ : ℕ) : ℝ)) * e k u) := by
                  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hck' (he_pos k u).le
              _ ≤ 2 * B * (rexp (-(u / 2 * (((k + k₀ : ℕ) : ℝ)) ^ 2)) / √u) :=
                  mul_le_mul_of_nonneg_left hab (by positivity)
              _ ≤ 2 * B * (rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) / √u) := by gcongr
              _ = 2 * B / √u * rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) := by ring
        _ = 2 * B / √u * ∑ k ∈ range N, rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) := by
            rw [mul_sum]
        _ ≤ 2 * B / √u * theta1 (u / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact (summable_theta1 (by positivity)).sum_le_tsum _ (fun _ _ => (exp_pos _).le)
    have h2 := theta1_le (u := u / 2) (by positivity) hu2
    have hsq : √(u / 2) = √u / √2 := Real.sqrt_div' _ (by norm_num)
    have hsu : 0 < √u := Real.sqrt_pos.2 hu0
    have h3 : 2 * B / √u * ((1 / 2 + thetaDual u₀) * √π / √(u / 2)) = M * u⁻¹ := by
      rw [hsq, show M * u⁻¹ = 2 * B * ((1 / 2 + thetaDual u₀) * √π * √2) / (√u * √u) by
        rw [Real.mul_self_sqrt hu0.le, hM]; ring]
      field_simp
    have h4 : 0 ≤ 2 * B / √u := by positivity
    calc (∑ k ∈ range N, ‖c (k + k₀)‖ * e k u) * ‖h u‖ ≤ (M * u⁻¹) * ‖h u‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [← h3]; exact h1.trans (mul_le_mul_of_nonneg_left h2 h4)
      _ = M * (u⁻¹ * ‖h u‖) := by ring
  -- summability of the far terms
  have hfar_sum : Summable fun k => ∫ u in Ioi u₀, E k u * h u := by
    set C := ∫ u in Ioi u₀, rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖
    have hC : 0 ≤ C := integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun u _ => mul_nonneg (exp_pos _).le (norm_nonneg _)))
    refine Summable.of_norm_bounded (g := fun k : ℕ => B * C * (((k : ℝ) + (k₀ + 1)) *
      rexp (-(u₀ * (k : ℝ) ^ 2)))) ((summable_add_mul_exp_neg_sq (by positivity)
        hu₀).mul_left (B * C)) fun k => ?_
    calc ‖∫ u in Ioi u₀, E k u * h u‖ ≤ ∫ u in Ioi u₀, ‖E k u * h u‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u in Ioi u₀, ‖c (k + k₀)‖ * rexp (-(u₀ * (k : ℝ) ^ 2)) *
            (rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) := by
          apply setIntegral_mono_on (hEfar k).norm (hfar.const_mul _) measurableSet_Ioi
          intro u hu
          rw [norm_mul, hnorm_E, mul_assoc, mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact (hfar_bound k u (le_of_lt hu)).trans
            (mul_le_mul_of_nonneg_right (hexp_far k) (exp_pos _).le)
      _ = ‖c (k + k₀)‖ * rexp (-(u₀ * (k : ℝ) ^ 2)) * C := integral_const_mul _ _
      _ ≤ B * ((((k + k₀ : ℕ) : ℝ)) + 1) * rexp (-(u₀ * (k : ℝ) ^ 2)) * C := by
          gcongr; exact hc _
      _ = B * C * (((k : ℝ) + (k₀ + 1)) * rexp (-(u₀ * (k : ℝ) ^ 2))) := by push_cast; ring
  -- dual terms
  have hDle : ∀ m, ∀ u ∈ Ioc 0 u₀, ‖D m u * h u‖ ≤ b m * (g u * ‖h u‖) := fun m u hu => by
    rw [norm_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (hDb m u hu) (norm_nonneg _)
  have hD_int : ∀ m, IntegrableOn (fun u => D m u * h u) (Ioc 0 u₀) := by
    intro m
    refine Integrable.mono' (hg.const_mul (b m)) ?_ ?_
    · exact ((hD_cont m).mul hcont).mono hIoc |>.aestronglyMeasurable measurableSet_Ioc
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (hDle m))
  have hDsum : Summable fun m => ∫ u in Ioc 0 u₀, D m u * h u := by
    refine Summable.of_norm_bounded (hb.mul_right (∫ u in Ioc 0 u₀, g u * ‖h u‖)) fun m => ?_
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hD_int m).norm (hg.const_mul _) measurableSet_Ioc (hDle m)
  -- main weight
  set W : ℝ → ℂ := fun u => W₀ u - ∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) with hW
  have hW_cont : ContinuousOn W (Ioi 0) :=
    hW₀c.sub (continuousOn_finsetSum _ fun k _ => continuousOn_const.mul
      (Complex.continuous_ofReal.comp (continuous_expneg _)).continuousOn)
  have hWint : IntegrableOn (fun u => W u * h u) (Ioc 0 u₀) := by
    refine integrableOn_cweight_mul_of_le hcont hW_cont hIoc measurableSet_Ioc
      (g := fun _ => A + ∑ k ∈ Ico 1 k₀, ‖c k‖) (hn0.const_mul _) fun u hu => ?_
    rw [hW]
    refine (norm_sub_le _ _).trans (add_le_add (hW₀b u hu) ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [exp_le_one_iff, neg_nonpos]; exact mul_nonneg (sq_nonneg _) hu.1.le
  -- pointwise identity
  have hpt : ∀ u ∈ Ioc 0 u₀, HasSum (fun k => E k u) (W u + ∑' m, D m u) := by
    intro u hu
    have hu0 := hu.1
    have hcs : Summable fun k : ℕ => c (k + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) := by
      refine Summable.of_norm_bounded ((summable_add_mul_exp_neg_sq (n₀ := 2) (by norm_num)
        hu0).mul_left B) fun k => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
      have hck := hc (k + 1)
      push_cast at hck
      calc ‖c (k + 1)‖ * rexp (-(((k : ℝ) + 1) ^ 2 * u)) ≤
          B * ((k : ℝ) + 1 + 1) * rexp (-(u * (k : ℝ) ^ 2)) := by
            apply mul_le_mul hck _ (exp_pos _).le (by positivity)
            rw [exp_le_exp, neg_le_neg_iff]
            nlinarith [Nat.cast_nonneg (α := ℝ) k]
        _ = _ := by ring
    have h1 := hcs.sum_add_tsum_nat_add (k₀ - 1)
    have h2 : ∀ i, c (i + (k₀ - 1) + 1) *
        (rexp (-((((i + (k₀ - 1) : ℕ) : ℝ) + 1) ^ 2 * u)) : ℂ) = E i u := by
      intro i
      rw [show i + (k₀ - 1) + 1 = i + k₀ by omega]
      simp only [hE, he]; congr 4; push_cast [Nat.cast_sub hk₀]; ring
    have h3 : ∑ i ∈ range (k₀ - 1), c (i + 1) * (rexp (-(((i : ℝ) + 1) ^ 2 * u)) : ℂ) =
        ∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) := by
      rw [sum_Ico_eq_sum_range]; apply sum_congr rfl; intro i _
      rw [add_comm 1 i]; push_cast; ring_nf
    simp only [h2, h3] at h1
    have hEs : Summable fun k => E k u := by
      have := (summable_nat_add_iff (k₀ - 1)).2 hcs
      refine this.congr fun i => ?_
      rw [← h2 i]
    refine hEs.hasSum_iff.2 ?_
    rw [← add_sub_cancel_left (∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ))
      (∑' k, E k u), h1, hθ u hu, hW]
    ring
  have key := split_of_pointwise hu₀ hEnear hEfar hEsum hfar_sum hD_int hb hg hDle hWint hpt
  have hEk : ∀ k, ∫ u in Ioi 0, E k u * h u =
      c (k + k₀) * ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u := fun k => by
    rw [← integral_const_mul]; congr 1; funext u; simp only [hE, he]; ring
  have hEk' : ∀ k, ∫ u in Ioi u₀, E k u * h u = c (k + k₀) * kTerm h u₀ (k + k₀) := fun k => by
    rw [kTerm, ← integral_const_mul]; congr 1; funext u; simp only [hE, he]; ring
  simp only [hEk, hEk'] at key hfar_sum
  exact ⟨hfar_sum, hDsum, key⟩

end ZetaF
