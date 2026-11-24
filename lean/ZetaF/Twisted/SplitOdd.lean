/-
# The twisted splitting for odd periodic weights (Remark 3.7, `δ = 1`)

For odd `χ` the summand is written `χ(k) F(k) k^{-s} = w(k) F(k) k^{-s-1}` with `w(k) = χ(k) k`,
and the splitting is applied with the kernel `h_{s+1}`, the theta transformation of
`Twisted/Odd.lean`, the dual weight `u^{-3/2}` and no constant main-term contribution.

The analytic interchange is factored through `split_of_pointwise`, a version of the abstract
splitting argument with all estimates as hypotheses.
-/
import ZetaF.Twisted.Split
import ZetaF.Twisted.Odd

open Real MeasureTheory Set Filter Finset

namespace ZetaF

variable {h : ℝ → ℂ} {u₀ : ℝ} {a : ℕ → ℂ} {R : ℝ}

/-- **Abstract splitting.**  If on `(0, u₀]` the series `∑_k E_k` equals `W + ∑_m D_m`, with the
integrability and summability needed to integrate termwise, then
`∑_k ∫₀^∞ E_k h = ∑_k ∫_{u₀}^∞ E_k h + ∑_m ∫₀^{u₀} D_m h + ∫₀^{u₀} W h`. -/
theorem split_of_pointwise (hu₀ : 0 < u₀) {E D : ℕ → ℝ → ℂ} {W : ℝ → ℂ}
    (hEnear : ∀ k, IntegrableOn (fun u => E k u * h u) (Ioc 0 u₀))
    (hEfar : ∀ k, IntegrableOn (fun u => E k u * h u) (Ioi u₀))
    (hEsum : Summable fun k => ∫ u in Ioc 0 u₀, ‖E k u * h u‖)
    (hfar_sum : Summable fun k => ∫ u in Ioi u₀, E k u * h u)
    (hD_int : ∀ m, IntegrableOn (fun u => D m u * h u) (Ioc 0 u₀))
    {b : ℕ → ℝ} {g : ℝ → ℝ} (hb : Summable b) (hg : IntegrableOn g (Ioc 0 u₀))
    (hDb : ∀ m, ∀ u ∈ Ioc 0 u₀, ‖D m u * h u‖ ≤ b m * g u)
    (hW : IntegrableOn (fun u => W u * h u) (Ioc 0 u₀))
    (hpt : ∀ u ∈ Ioc 0 u₀, HasSum (fun k => E k u) (W u + ∑' m, D m u)) :
    HasSum (fun k => ∫ u in Ioi 0, E k u * h u)
      ((∑' k, ∫ u in Ioi u₀, E k u * h u) + (∑' m, ∫ u in Ioc 0 u₀, D m u * h u) +
        ∫ u in Ioc 0 u₀, W u * h u) := by
  have hsplit : ∀ k, ∫ u in Ioi 0, E k u * h u =
      (∫ u in Ioc 0 u₀, E k u * h u) + ∫ u in Ioi u₀, E k u * h u := fun k => by
    rw [← Ioc_union_Ioi_eq_Ioi hu₀.le, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hEnear k) (hEfar k)]
  have hnear := hasSum_integral_of_summable_integral_norm hEnear hEsum
  have hDsum : Summable fun m => ∫ u in Ioc 0 u₀, ‖D m u * h u‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _)
      (fun m => ?_) (hb.mul_right (∫ u in Ioc 0 u₀, g u))
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hD_int m).norm (hg.const_mul _) measurableSet_Ioc (hDb m)
  have hdual := hasSum_integral_of_summable_integral_norm hD_int hDsum
  have hpts : ∀ u ∈ Ioc 0 u₀, HasSum (fun m => D m u * h u) (∑' m, D m u * h u) := fun u hu =>
    (Summable.of_norm_bounded (hb.mul_right (g u)) fun m => hDb m u hu).hasSum
  have hDint : IntegrableOn (fun u => ∑' m, D m u * h u) (Ioc 0 u₀) := by
    refine Integrable.mono' (hg.const_mul (∑' m, b m)) ?_ ?_
    · refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun N u => ∑ m ∈ range N, D m u * h u)
        (fun N => Finset.aestronglyMeasurable_fun_sum _ fun m _ => (hD_int m).1) ?_
      exact (ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall fun u hu => (hpts u hu).tendsto_sum_nat)
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      exact tsum_of_norm_bounded (hb.hasSum.mul_right (g u)) fun m => hDb m u hu
  have hpt' : EqOn (fun u => ∑' k, E k u * h u) (fun u => W u * h u + ∑' m, D m u * h u)
      (Ioc 0 u₀) := by
    intro u hu
    simp only
    rw [tsum_mul_right, (hpt u hu).tsum_eq, tsum_mul_right, add_mul]
  have hval : ∫ u in Ioc 0 u₀, ∑' k, E k u * h u =
      (∫ u in Ioc 0 u₀, W u * h u) + ∑' m, ∫ u in Ioc 0 u₀, D m u * h u := by
    rw [setIntegral_congr_fun measurableSet_Ioc hpt', integral_add hW hDint, hdual.tsum_eq]
  have := hnear.add hfar_sum.hasSum
  rw [hval] at this
  convert this using 1
  · funext k; exact hsplit k
  · ring

/-! ### Elementary estimates -/

lemma summable_add_mul_exp_neg_sq {n₀ r : ℝ} (hn₀ : 0 ≤ n₀) (hr : 0 < r) :
    Summable fun k : ℕ => ((k : ℝ) + n₀) * rexp (-(r * (k : ℝ) ^ 2)) := by
  have s1 := Real.summable_pow_mul_exp_neg_nat_mul 1 hr
  have s0 := (Real.summable_pow_mul_exp_neg_nat_mul 0 hr).mul_left n₀
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (s1.add s0)
  have hk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero k
  have he : rexp (-(r * (k : ℝ) ^ 2)) ≤ rexp (-r * k) := by
    rw [exp_le_exp]; nlinarith
  simp only [pow_one, pow_zero, one_mul]
  nlinarith [Real.exp_pos (-(r * (k : ℝ) ^ 2)), Nat.cast_nonneg (α := ℝ) k]

lemma one_le_rpow_mul_rpow_neg {u t : ℝ} (hu : 0 < u) (huu₀ : u ≤ u₀) (ht : 0 ≤ t) :
    1 ≤ u₀ ^ t * u ^ (-t) := by
  rw [Real.rpow_neg hu.le, ← div_eq_mul_inv, ← Real.div_rpow (hu.le.trans huu₀) hu.le]
  exact Real.one_le_rpow ((one_le_div hu).2 huu₀) ht

lemma continuousOn_dualWeightOdd (c : ℝ) :
    ContinuousOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * rexp (-(c / u))) (Ioi 0) := by
  refine ContinuousOn.mul (fun u hu => (Real.continuousAt_rpow_const _ _
    (Or.inl (ne_of_gt hu))).continuousWithinAt) ?_
  apply ContinuousOn.rexp
  apply ContinuousOn.neg
  exact continuousOn_const.div continuousOn_id fun u hu => ne_of_gt hu

/-! ### The odd splitting -/

/-- `J^χ_m = ∫₀^{u₀} u^{-3/2} e^{-λm²/u} h(u) du` (the paper's `Z_{3/2}[h](λm²)`). -/
noncomputable def dualTermOdd (h : ℝ → ℂ) (u₀ lam : ℝ) (m : ℕ) : ℂ :=
  ∫ u in Ioc 0 u₀, ((u ^ (-(3 / 2 : ℝ)) * rexp (-(lam * (m : ℝ) ^ 2 / u)) : ℝ) : ℂ) * h u

/-- The main term for `δ = 1`: `-∫₀^{u₀} ∑_{k < k₀} w(k) e^{-k²u} h(u) du`. -/
noncomputable def mainTermOdd (h : ℝ → ℂ) (u₀ : ℝ) (c : ℕ → ℂ) (k₀ : ℕ) : ℂ :=
  ∫ u in Ioc 0 u₀, (-∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) * h u

/-- **Abstract splitting with linearly growing coefficients and dual weight `u^{-3/2}`.** -/
theorem theta_split_odd_gen {c d : ℕ → ℂ} {B B' : ℝ} (hc : ∀ k, ‖c k‖ ≤ B * k)
    (hd : ∀ m, ‖d m‖ ≤ B' * m) {lam : ℝ} (hlam : 0 < lam)
    (hθ : ∀ u : ℝ, 0 < u → ∑' k : ℕ, c (k + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      ((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' m : ℕ, d (m + 1) * (rexp (-(lam * ((m : ℝ) + 1) ^ 2 / u)) : ℂ))
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hu₀ : 0 < u₀) (hcont : ContinuousOn h (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(3 / 2 : ℝ)) * ‖h u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀)) :
    HasSum (fun k : ℕ => c (k + k₀) *
        ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u)
      (∑' k : ℕ, c (k + k₀) * kTerm h u₀ (k + k₀) +
        ∑' m : ℕ, d (m + 1) * dualTermOdd h u₀ lam (m + 1) + mainTermOdd h u₀ c k₀) := by
  have hIoc : Ioc (0 : ℝ) u₀ ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hIoi : Ioi u₀ ⊆ Ioi 0 := Ioi_subset_Ioi hu₀.le
  have hB : 0 ≤ B := by simpa using (norm_nonneg _).trans (hc 1)
  have hB' : 0 ≤ B' := by simpa using (norm_nonneg _).trans (hd 1)
  set e : ℕ → ℝ → ℝ := fun k u => rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) with he
  have he_pos : ∀ k u, 0 < e k u := fun k u => exp_pos _
  have he_le_one : ∀ k u, 0 ≤ u → e k u ≤ 1 := by
    intro k u hu; simp only [he, exp_le_one_iff, neg_nonpos]; positivity
  set E : ℕ → ℝ → ℂ := fun k u => c (k + k₀) * (e k u : ℂ) with hE
  have hE_cont : ∀ k, ContinuousOn (E k) (Ioi 0) := fun k =>
    continuousOn_const.mul (Complex.continuous_ofReal.comp (continuous_expneg _)).continuousOn
  have hnorm_E : ∀ k u, ‖E k u‖ = ‖c (k + k₀)‖ * e k u := fun k u => by
    rw [hE, norm_mul, Complex.norm_real, Real.norm_of_nonneg (he_pos k u).le]
  -- integrability of `‖h‖` and `u⁻¹ ‖h‖` near `0`
  have hn0 : IntegrableOn (fun u => ‖h u‖) (Ioc 0 u₀) := by
    refine Integrable.mono' (hnear.const_mul (u₀ ^ (3 / 2 : ℝ))) ?_ ?_
    · exact (hcont.mono hIoc).norm.aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      rw [norm_norm, ← mul_assoc]
      exact le_mul_of_one_le_left (norm_nonneg _)
        (one_le_rpow_mul_rpow_neg hu.1 hu.2 (by norm_num))
  have hn1 : IntegrableOn (fun u => u⁻¹ * ‖h u‖) (Ioc 0 u₀) := by
    refine Integrable.mono' (hnear.const_mul (u₀ ^ (1 / 2 : ℝ))) ?_ ?_
    · exact ((continuousOn_inv₀.mono fun u (hu : u ∈ Set.Ioi (0 : ℝ)) => ne_of_gt hu).mul
        hcont.norm).mono hIoc |>.aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      have hu0 := hu.1
      rw [Real.norm_of_nonneg (by positivity), ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have h1 : u⁻¹ = u ^ (1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hu0]; norm_num [Real.rpow_neg_one]
      rw [h1]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hu0.le hu.2 (by norm_num))
        (Real.rpow_nonneg hu0.le _)
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
    set M := B * ((1 / 2 + thetaDual u₀) * √π * √2) with hM
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
    have h1 : ∑ k ∈ range N, ‖c (k + k₀)‖ * e k u ≤ B / √u * theta1 (u / 2) := by
      calc ∑ k ∈ range N, ‖c (k + k₀)‖ * e k u
          ≤ ∑ k ∈ range N, B / √u * rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) := by
            apply sum_le_sum; intro k _
            have hck := hc (k + k₀)
            have hab := abs_mul_exp_neg_sq_le (((k + k₀ : ℕ) : ℝ)) hu0
            rw [abs_of_nonneg (Nat.cast_nonneg _)] at hab
            have hmono : rexp (-(u / 2 * (((k + k₀ : ℕ) : ℝ)) ^ 2)) ≤
                rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) := by
              rw [exp_le_exp, neg_le_neg_iff]
              have : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
              have : ((k : ℝ) + 1) ^ 2 ≤ (((k + k₀ : ℕ) : ℝ)) ^ 2 := by
                push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]
              nlinarith
            calc ‖c (k + k₀)‖ * e k u ≤ B * ((((k + k₀ : ℕ) : ℝ)) * e k u) := by
                  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hck (he_pos k u).le
              _ ≤ B * (rexp (-(u / 2 * (((k + k₀ : ℕ) : ℝ)) ^ 2)) / √u) :=
                  mul_le_mul_of_nonneg_left hab hB
              _ ≤ B * (rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) / √u) := by gcongr
              _ = B / √u * rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) := by ring
        _ = B / √u * ∑ k ∈ range N, rexp (-(((k : ℝ) + 1) ^ 2 * (u / 2))) := by
            rw [mul_sum]
        _ ≤ B / √u * theta1 (u / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact (summable_theta1 (by positivity)).sum_le_tsum _ (fun _ _ => (exp_pos _).le)
    have h2 := theta1_le (u := u / 2) (by positivity) hu2
    have hsq : √(u / 2) = √u / √2 := Real.sqrt_div' _ (by norm_num)
    have hsu : 0 < √u := Real.sqrt_pos.2 hu0
    have h3 : B / √u * ((1 / 2 + thetaDual u₀) * √π / √(u / 2)) = M * u⁻¹ := by
      rw [hsq, show M * u⁻¹ = B * ((1 / 2 + thetaDual u₀) * √π * √2) / (√u * √u) by
        rw [Real.mul_self_sqrt hu0.le, hM]; ring]
      field_simp
    have h4 : 0 ≤ B / √u := by positivity
    calc (∑ k ∈ range N, ‖c (k + k₀)‖ * e k u) * ‖h u‖ ≤ (M * u⁻¹) * ‖h u‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [← h3]; exact h1.trans (mul_le_mul_of_nonneg_left h2 h4)
      _ = M * (u⁻¹ * ‖h u‖) := by ring
  -- summability of the far terms
  have hfar_sum : Summable fun k => ∫ u in Ioi u₀, E k u * h u := by
    set C := ∫ u in Ioi u₀, rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖
    have hC : 0 ≤ C := integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun u _ => mul_nonneg (exp_pos _).le (norm_nonneg _)))
    refine Summable.of_norm_bounded (g := fun k : ℕ => B * C * (((k : ℝ) + k₀) *
      rexp (-(u₀ * (k : ℝ) ^ 2)))) ((summable_add_mul_exp_neg_sq (Nat.cast_nonneg _)
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
      _ ≤ B * (((k + k₀ : ℕ) : ℝ)) * rexp (-(u₀ * (k : ℝ) ^ 2)) * C := by
          gcongr; exact hc _
      _ = B * C * (((k : ℝ) + k₀) * rexp (-(u₀ * (k : ℝ) ^ 2))) := by push_cast; ring
  -- dual terms
  set D : ℕ → ℝ → ℂ := fun m u => d (m + 1) *
    ((u ^ (-(3 / 2 : ℝ)) * rexp (-(lam * ((m : ℝ) + 1) ^ 2 / u)) : ℝ) : ℂ) with hD
  have hD_cont : ∀ m, ContinuousOn (D m) (Ioi 0) := fun m =>
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_dualWeightOdd _))
  have hDle : ∀ m, ∀ u ∈ Ioc 0 u₀, ‖D m u * h u‖ ≤
      (B' * (((m : ℝ) + 1) * rexp (-(lam / u₀ * (m : ℝ) ^ 2)))) * (u ^ (-(3 / 2 : ℝ)) * ‖h u‖) := by
    intro m u hu
    have hr := Real.rpow_nonneg hu.1.le (-(3 / 2 : ℝ))
    have hexp : rexp (-(lam * ((m : ℝ) + 1) ^ 2 / u)) ≤ rexp (-(lam / u₀ * (m : ℝ) ^ 2)) := by
      rw [exp_le_exp, neg_le_neg_iff]
      calc lam / u₀ * (m : ℝ) ^ 2 ≤ lam / u₀ * ((m : ℝ) + 1) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [Nat.cast_nonneg (α := ℝ) m]
        _ = lam * ((m : ℝ) + 1) ^ 2 / u₀ := by ring
        _ ≤ lam * ((m : ℝ) + 1) ^ 2 / u := div_le_div_of_nonneg_left (by positivity) hu.1 hu.2
    have hdm := hd (m + 1)
    push_cast at hdm
    calc ‖D m u * h u‖ = ‖d (m + 1)‖ * rexp (-(lam * ((m : ℝ) + 1) ^ 2 / u)) *
          (u ^ (-(3 / 2 : ℝ)) * ‖h u‖) := by
          simp only [hD, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (mul_nonneg hr (exp_pos _).le)]; ring
      _ ≤ (B' * ((m : ℝ) + 1)) * rexp (-(lam / u₀ * (m : ℝ) ^ 2)) *
          (u ^ (-(3 / 2 : ℝ)) * ‖h u‖) := by
          gcongr
      _ = _ := by ring
  have hD_int : ∀ m, IntegrableOn (fun u => D m u * h u) (Ioc 0 u₀) := by
    intro m
    refine Integrable.mono' (hnear.const_mul (B' * (((m : ℝ) + 1) *
      rexp (-(lam / u₀ * (m : ℝ) ^ 2))))) ?_ ?_
    · exact ((hD_cont m).mul hcont).mono hIoc |>.aestronglyMeasurable measurableSet_Ioc
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (hDle m))
  have hb : Summable fun m : ℕ => B' * (((m : ℝ) + 1) * rexp (-(lam / u₀ * (m : ℝ) ^ 2))) :=
    (summable_add_mul_exp_neg_sq zero_le_one (by positivity)).mul_left B'
  -- main weight
  set W : ℝ → ℂ := fun u => -∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) with hW
  have hW_cont : ContinuousOn W (Ioi 0) :=
    (continuousOn_finsetSum _ fun k _ => continuousOn_const.mul
      (Complex.continuous_ofReal.comp (continuous_expneg _)).continuousOn).neg
  have hWint : IntegrableOn (fun u => W u * h u) (Ioc 0 u₀) := by
    refine integrableOn_cweight_mul_of_le hcont hW_cont hIoc measurableSet_Ioc
      (g := fun _ => ∑ k ∈ Ico 1 k₀, ‖c k‖) (hn0.const_mul _) fun u hu => ?_
    rw [hW, norm_neg]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [exp_le_one_iff, neg_nonpos]; exact mul_nonneg (sq_nonneg _) hu.1.le
  -- pointwise identity
  have hpt : ∀ u ∈ Ioc 0 u₀, HasSum (fun k => E k u) (W u + ∑' m, D m u) := by
    intro u hu
    have hu0 := hu.1
    have hcs : Summable fun k : ℕ => c (k + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) := by
      refine Summable.of_norm_bounded ((summable_add_mul_exp_neg_sq zero_le_one hu0).mul_left B)
        fun k => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
      have hck := hc (k + 1)
      push_cast at hck
      calc ‖c (k + 1)‖ * rexp (-(((k : ℝ) + 1) ^ 2 * u)) ≤
          B * ((k : ℝ) + 1) * rexp (-(u * (k : ℝ) ^ 2)) := by
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
    have hDs : ∑' m, D m u = ((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' m : ℕ, d (m + 1) * (rexp (-(lam * ((m : ℝ) + 1) ^ 2 / u)) : ℂ) := by
      rw [← tsum_mul_left]; congr 1; funext m; simp only [hD]; push_cast; ring
    rw [hDs, ← hθ u hu0, hW]
    linear_combination h1
  have key := split_of_pointwise hu₀ hEnear hEfar hEsum hfar_sum hD_int hb hnear hDle hWint hpt
  have hEk : ∀ k, ∫ u in Ioi 0, E k u * h u =
      c (k + k₀) * ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u := fun k => by
    rw [← integral_const_mul]; congr 1; funext u; simp only [hE, he]; ring
  have hEk' : ∀ k, ∫ u in Ioi u₀, E k u * h u = c (k + k₀) * kTerm h u₀ (k + k₀) := fun k => by
    rw [kTerm, ← integral_const_mul]; congr 1; funext u; simp only [hE, he]; ring
  have hDm : ∀ m, ∫ u in Ioc 0 u₀, D m u * h u = d (m + 1) * dualTermOdd h u₀ lam (m + 1) :=
    fun m => by
      rw [dualTermOdd, ← integral_const_mul]; congr 1; funext u; simp only [hD]; push_cast; ring
  simp only [hEk, hEk', hDm] at key
  exact key

/-! ### Odd periodic twists -/

/-- **Twisted splitting** (abstract form, Remark 3.7, odd case).  For an odd `q`-periodic `χ`,
`∑_{k ≥ k₀} χ(k) k ∫₀^∞ e^{-k²u} h(u) du` splits into the far part, the dual part with coefficients
`c₁ m χ̂(m)` and weight `u^{-3/2} e^{-π²m²/(q²u)}`, and the main term with weight
`-∑_{k < k₀} χ(k) k e^{-k²u}`. -/
theorem theta_split_char_odd {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (hodd : ∀ k, χ (-k) = -χ k)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hu₀ : 0 < u₀) (hcont : ContinuousOn h (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(3 / 2 : ℝ)) * ‖h u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀)) :
    HasSum (fun k : ℕ => χ ((k + k₀ : ℕ) : ℤ) * ((k + k₀ : ℕ) : ℂ) *
        ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u)
      (∑' k : ℕ, χ ((k + k₀ : ℕ) : ℤ) * ((k + k₀ : ℕ) : ℂ) * kTerm h u₀ (k + k₀) +
        ∑' m : ℕ, charDualOdd q χ (m + 1) * dualTermOdd h u₀ (π ^ 2 / q ^ 2) (m + 1) +
        mainTermOdd h u₀ (fun k => χ k * k) k₀) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set Bχ := ∑ a ∈ range q, ‖χ a‖
  have hc : ∀ k : ℕ, ‖χ k * (k : ℂ)‖ ≤ Bχ * k := fun k => by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (periodic_bound hq hper k) (Nat.cast_nonneg _)
  have hd : ∀ m : ℕ, ‖charDualOdd q χ m‖ ≤ (π * √π / q ^ 2 * Bχ) * m := fun m => by
    rw [charDualOdd, norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_natCast]
    have := gaussSum_norm_le (q := q) χ m
    have h0 : 0 ≤ π * √π / q ^ 2 := by positivity
    calc π * √π / q ^ 2 * m * ‖gaussSum q χ m‖ ≤ π * √π / q ^ 2 * m * Bχ :=
          mul_le_mul_of_nonneg_left this (mul_nonneg h0 (Nat.cast_nonneg _))
      _ = _ := by ring
  refine theta_split_odd_gen (c := fun k => χ k * k) hc hd (lam := π ^ 2 / q ^ 2)
    (by positivity) (fun u hu => ?_) hk₀ hu₀ hcont hnear hfar
  rw [← tsum_char_theta_odd_half hq hper hodd hu]
  congr 1; funext k; push_cast; ring

/-- `u^{-t} |h_s(u)|` is integrable on `(0, u₀]` for `2t < Re s`. -/
lemma integrableOn_rpow_neg_mul_norm_kernel (ha : GeomBounded a R) (hR : 0 ≤ R) {s : ℂ}
    (hs0 : 0 < s.re) {t : ℝ} (hst : 2 * t < s.re) (hu₀ : 0 < u₀) :
    IntegrableOn (fun u => u ^ (-t) * ‖kernel a s u‖) (Ioc 0 u₀) := by
  obtain ⟨D, hD0, hD⟩ := exists_coeff_bound ha hs0
  set g : ℕ → ℝ → ℝ := fun n u => majCoeff D R s.re n * u ^ ((s.re + n) / 2 - 1 - t) with hg
  have hr : ∀ n : ℕ, -1 < (s.re + n) / 2 - 1 - t := fun n => by
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
      refine ((summable_maj (D := D) hR hs0 hu.1).mul_left (u ^ (-t))).congr fun n => ?_
      simp only [hg]
      rw [mul_left_comm, ← Real.rpow_add hu.1]; congr 2; ring
    · have hσ : 0 < s.re - 2 * t := by linarith
      have hsm := (summable_majCoeff_mul_pow (D := D) (σ := s.re) (q := √u₀) hR hs0
        (Real.sqrt_nonneg _)).mul_left (2 / (s.re - 2 * t) * u₀ ^ ((s.re + 2 - 2 * t) / 2 - 1))
      refine Summable.of_nonneg_of_le (fun n => integral_nonneg_of_ae ?_) (fun n => ?_) hsm
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
        exact mul_nonneg (majCoeff_nonneg hD0 hR hs0 n) (Real.rpow_nonneg hu.1.le _)
      · simp only [hg]
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hu₀.le,
          integral_rpow (Or.inl (hr n)), Real.zero_rpow (by linarith [hr n]), sub_zero]
        have h1 : (s.re + n) / 2 - 1 - t + 1 = ((s.re + 2 - 2 * t) + n) / 2 - 1 := by ring
        rw [h1, rpow_half_eq hu₀]
        set E := ((s.re + 2 - 2 * t) + n) / 2 - 1
        have hE : (s.re - 2 * t) / 2 ≤ E := by
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          simp only [E]; linarith
        have hE0 : 0 < E := by linarith
        have hm := majCoeff_nonneg hD0 hR hs0 n (D := D) (R := R)
        set P := u₀ ^ ((s.re + 2 - 2 * t) / 2 - 1) * √u₀ ^ n
        have hp : 0 ≤ P := by positivity
        have h2 : 1 ≤ 2 / (s.re - 2 * t) * E := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hσ]; linarith
        rw [mul_div_assoc', div_le_iff₀ hE0]
        calc majCoeff D R s.re n * P ≤ majCoeff D R s.re n * P * (2 / (s.re - 2 * t) * E) :=
              le_mul_of_one_le_right (mul_nonneg hm hp) h2
          _ = _ := by simp only [P]; ring
  have hct : ContinuousOn (fun u : ℝ => u ^ (-t)) (Ioi 0) := fun u hu =>
    (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hu))).continuousWithinAt
  refine Integrable.mono' hgint ?_ ?_
  · exact (hct.mul (continuousOn_kernel ha hR hs0).norm).mono Ioc_subset_Ioi_self
      |>.aestronglyMeasurable measurableSet_Ioc
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 < u := hu.1
    have hsm := summable_maj (D := D) hR hs0 hu0
    rw [Real.norm_of_nonneg (by positivity)]
    calc u ^ (-t) * ‖kernel a s u‖
        ≤ u ^ (-t) * ∑' n, majCoeff D R s.re n * u ^ ((s.re + n) / 2 - 1) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu0.le _)
          exact tsum_of_norm_bounded hsm.hasSum (norm_kernelTerm_le hD hu0)
      _ = ∑' n, g n u := by
          rw [← tsum_mul_left]; congr 1; funext n; simp only [hg]
          rw [mul_left_comm, ← Real.rpow_add hu0]; congr 2; ring

/-- **Remark 3.7, odd case**: the twisted tail `∑_{k ≥ k₀} χ(k) F(k) k^{-s}` for odd `q`-periodic
`χ` and `Re s > 2`, split with the kernel `h_{s+1}` of `F(x) x^{-s-1}`. -/
theorem zetaTail_split_char_odd (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {s : ℂ} (hs : 2 < s.re)
    {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q) (hodd : ∀ k, χ (-k) = -χ k)
    (hu₀ : 0 < u₀) :
    zetaTail (fun k => χ k * F k) k₀ s =
      ∑' k : ℕ, χ ((k + k₀ : ℕ) : ℤ) * ((k + k₀ : ℕ) : ℂ) * kTerm (kernel a (s + 1)) u₀ (k + k₀) +
        ∑' m : ℕ, charDualOdd q χ (m + 1) *
          dualTermOdd (kernel a (s + 1)) u₀ (π ^ 2 / q ^ 2) (m + 1) +
        mainTermOdd (kernel a (s + 1)) u₀ (fun k => χ k * k) k₀ := by
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hspl := theta_split_char_odd (h := kernel a (s + 1)) hq hper hodd hk₀ hu₀
    (continuousOn_kernel ha hR hs1)
    (integrableOn_rpow_neg_mul_norm_kernel ha hR hs1 (by simp; linarith) hu₀)
    ((integrableOn_exp_mul_norm_kernel ha hR hs1 hRk).mono_set (Ioi_subset_Ioi hu₀.le))
  have hterm : ∀ k : ℕ, χ ((k + k₀ : ℕ) : ℤ) * ((k + k₀ : ℕ) : ℂ) *
      ∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * kernel a (s + 1) u =
      LSeries.term (tail k₀ (fun k => χ k * F k)) s (k + k₀) := by
    intro k
    have hK : (k + k₀ : ℕ) ≠ 0 := by omega
    have hK' : ((k + k₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hK
    have hRK : R < ((k + k₀ : ℕ) : ℝ) := lt_of_lt_of_le hRk (by exact_mod_cast Nat.le_add_left k₀ k)
    have h1 := (hasSum_laplace_kernel ha hR hs1 hRK).tsum_eq
    rw [← h1, LSeries.term_of_ne_zero hK, tail, ite_eq_left (Nat.le_add_left k₀ k),
      hF _ (Nat.le_add_left k₀ k), evalInv]
    push_cast
    simp_rw [show ((k : ℂ) + k₀) = ((k + k₀ : ℕ) : ℂ) by push_cast; ring]
    simp_rw [natCast_cpow_neg_add hK]
    have hKs : ((k + k₀ : ℕ) : ℂ) ^ (s + 1) = ((k + k₀ : ℕ) : ℂ) ^ s * ((k + k₀ : ℕ) : ℂ) := by
      rw [Complex.cpow_add _ _ hK', Complex.cpow_one]
    have hKs0 : ((k + k₀ : ℕ) : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    have hn : ∀ n : ℕ, a n * ((((k + k₀ : ℕ) : ℂ) ^ (s + 1))⁻¹ * ((k + k₀ : ℕ) : ℂ)⁻¹ ^ n) =
        ((k + k₀ : ℕ) : ℂ)⁻¹ * (((k + k₀ : ℕ) : ℂ) ^ s)⁻¹ *
          (a n * ((k + k₀ : ℕ) : ℂ)⁻¹ ^ n) := fun n => by
      rw [hKs, mul_inv]; ring
    simp_rw [hn, tsum_mul_left]
    field_simp
  simp only [hterm] at hspl
  have hzero : ∑ i ∈ Finset.range k₀, LSeries.term (tail k₀ (fun k => χ k * F k)) s i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [LSeries.term, tail, show ¬ k₀ ≤ i by omega]
  have hfull := (hasSum_nat_add_iff' (f := LSeries.term (tail k₀ (fun k => χ k * F k)) s) k₀).1
    (by rw [hzero, sub_zero]; exact hspl)
  rw [zetaTail, LSeries, hfull.tsum_eq]

/-! ### General periodic weights -/

/-- The even part `(χ(k) + χ(-k))/2` of a weight. -/
noncomputable def evenPart (χ : ℤ → ℂ) (k : ℤ) : ℂ := (χ k + χ (-k)) / 2

/-- The odd part `(χ(k) - χ(-k))/2` of a weight. -/
noncomputable def oddPart (χ : ℤ → ℂ) (k : ℤ) : ℂ := (χ k - χ (-k)) / 2

lemma periodic_evenPart {q : ℕ} {χ : ℤ → ℂ} (hper : Function.Periodic χ q) :
    Function.Periodic (evenPart χ) q := fun k => by
  simp only [evenPart, hper k, show -(k + q) = -k - q by ring, hper.sub_eq]

lemma periodic_oddPart {q : ℕ} {χ : ℤ → ℂ} (hper : Function.Periodic χ q) :
    Function.Periodic (oddPart χ) q := fun k => by
  simp only [oddPart, hper k, show -(k + q) = -k - q by ring, hper.sub_eq]

lemma evenPart_neg (χ : ℤ → ℂ) (k : ℤ) : evenPart χ (-k) = evenPart χ k := by
  simp only [evenPart, neg_neg]; ring

lemma oddPart_neg (χ : ℤ → ℂ) (k : ℤ) : oddPart χ (-k) = -oddPart χ k := by
  simp only [oddPart, neg_neg]; ring

/-- A bounded weight times a regular-at-infinity sequence has an absolutely convergent
Dirichlet series for `Re s > 1`. -/
lemma LSeriesSummable_tail_mul (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {ψ : ℕ → ℂ} {B : ℝ}
    (hψ : ∀ k, ‖ψ k‖ ≤ B) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (tail k₀ fun k => ψ k * F k) s := by
  obtain ⟨M, hM⟩ := evalInv_bounded hR ha hRk
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨B * max M 0, fun n _ => ?_⟩
  rw [sub_self, Real.rpow_zero, mul_one]
  unfold tail
  split_ifs with h
  · rw [norm_mul, hF n h]
    exact mul_le_mul (hψ n) ((hM n (by exact_mod_cast h)).trans (le_max_left _ _))
      (norm_nonneg _) ((norm_nonneg _).trans (hψ n))
  · simp only [norm_zero]
    exact mul_nonneg ((norm_nonneg _).trans (hψ 0)) (le_max_right _ _)

/-- **Remark 3.7 for an arbitrary periodic weight** (`Re s > 2`): the twisted tail is the sum of
the splitting of its even part (`δ = 0`) and of its odd part (`δ = 1`). -/
theorem zetaTail_split_periodic (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {s : ℂ} (hs : 2 < s.re)
    {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q) (hu₀ : 0 < u₀) :
    zetaTail (fun k => χ k * F k) k₀ s =
      (∑' k : ℕ, evenPart χ ((k + k₀ : ℕ) : ℤ) * kTerm (kernel a s) u₀ (k + k₀) +
        ∑' m : ℕ, charDual q (evenPart χ) (m + 1) *
          dualTermGen (kernel a s) u₀ (π ^ 2 / q ^ 2) (m + 1) +
        mainTermGen (kernel a s) u₀ (fun k => evenPart χ k) (charAlpha q (evenPart χ))
          (-(1 / 2) * evenPart χ 0) k₀) +
      (∑' k : ℕ, oddPart χ ((k + k₀ : ℕ) : ℤ) * ((k + k₀ : ℕ) : ℂ) *
          kTerm (kernel a (s + 1)) u₀ (k + k₀) +
        ∑' m : ℕ, charDualOdd q (oddPart χ) (m + 1) *
          dualTermOdd (kernel a (s + 1)) u₀ (π ^ 2 / q ^ 2) (m + 1) +
        mainTermOdd (kernel a (s + 1)) u₀ (fun k => oddPart χ k * k) k₀) := by
  have hs1 : 1 < s.re := by linarith
  have hbd : ∀ ψ : ℤ → ℂ, Function.Periodic ψ q → ∀ k : ℕ, ‖ψ k‖ ≤ ∑ a ∈ range q, ‖ψ a‖ :=
    fun ψ hψ k => periodic_bound hq hψ k
  have he := LSeriesSummable_tail_mul (ψ := fun k : ℕ => evenPart χ k) ha hR hRk hF
    (hbd _ (periodic_evenPart hper)) hs1
  have ho := LSeriesSummable_tail_mul (ψ := fun k : ℕ => oddPart χ k) ha hR hRk hF
    (hbd _ (periodic_oddPart hper)) hs1
  have hsplit : tail k₀ (fun k => χ k * F k) =
      tail k₀ (fun k => evenPart χ k * F k) + tail k₀ (fun k => oddPart χ k * F k) := by
    funext k
    simp only [Pi.add_apply, tail, evenPart, oddPart]
    split_ifs <;> ring
  rw [zetaTail, hsplit, LSeries_add he ho, ← zetaTail, ← zetaTail,
    zetaTail_split_char ha hR hk₀ hRk hF hs1 hq (periodic_evenPart hper) (evenPart_neg χ) hu₀,
    zetaTail_split_char_odd ha hR hk₀ hRk hF hs hq (periodic_oddPart hper) (oddPart_neg χ) hu₀]

end ZetaF
