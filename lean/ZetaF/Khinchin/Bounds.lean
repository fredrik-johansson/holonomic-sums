/-
# The error bounds of Section 6.4.2 (omitted terms and the evaluation point)

For Algorithm K3 the kernel is `G(u) = Ein(4u)/u = ∑_{n≥1} 4^n u^{n-1}/(n·n!)`, the `k`-terms are
`I_k = ∫_U^∞ e^{-k²u} G` and the dual terms `J_m = √π ∫₀^U u^{-1/2} e^{-c_m/u} G`.  We prove the
bounds that make the evaluation rigorous:
* `kerG_le`: `G(u) ≤ e^{4u}/u`, and `kerG_mono`: `G` is nondecreasing on `[0, ∞)`;
* `kTermK_pos`, `kTermK_le`: `0 < I_k ≤ e^{-(k²-4)U}/((k²-4)U)` for `k ≥ 3`;
* `dualTermK_le`: `J_m ≤ 2√(πU) G(U) e^{-c/U}`;
* `dualTermK_lipschitz`: `|J(c) - J(c')| ≤ √π G(U) U^{1/2} e^{-ξ/U}/ξ · |c - c'|` for `c, c' ≥ ξ > 0`
  (the paper's `|J'(ξ)| ≤ 2√π Ein(4U) e^{-ξ/U}/(U^{1/2}ξ)`, without the factor 2).
-/
import ZetaF.Deps

open MeasureTheory Set Filter Real
open scoped Nat Topology

namespace ZetaF

/-- The kernel `G(u) = ∑_{n ≥ 0} 4^{n+1} u^n/((n+1)(n+1)!) = Ein(4u)/u`. -/
noncomputable def kerG (u : ℝ) : ℝ := ∑' n : ℕ, 4 ^ (n + 1) * u ^ n / ((n + 1) * ((n + 1)! : ℝ))

lemma kerG_term_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    4 ^ (n + 1) * u ^ n / ((n + 1) * ((n + 1)! : ℝ)) ≤ 4 * ((4 * u) ^ n / (n ! : ℝ)) := by
  have hf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [Nat.factorial_succ, Nat.cast_mul, mul_pow, div_le_iff₀ (by positivity)]
  push_cast
  have : (1 : ℝ) ≤ (n + 1) * (n + 1) := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  field_simp
  rw [pow_succ]
  have hp : 0 ≤ 4 ^ n * u ^ n * 4 := by positivity
  nlinarith

lemma summable_kerG {u : ℝ} (hu : 0 ≤ u) :
    Summable fun n : ℕ => 4 ^ (n + 1) * u ^ n / ((n + 1) * ((n + 1)! : ℝ)) :=
  Summable.of_nonneg_of_le (fun n => by positivity) (kerG_term_le hu)
    ((Real.summable_pow_div_factorial (4 * u)).mul_left 4)

lemma hasSum_exp_sub_one (y : ℝ) : HasSum (fun n : ℕ => y ^ (n + 1) / ((n + 1)! : ℝ)) (rexp y - 1) := by
  have h := (Real.summable_pow_div_factorial y).hasSum
  have e : ∑' n : ℕ, y ^ n / (n ! : ℝ) = rexp y := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [e] at h
  have := (hasSum_nat_add_iff' 1).2 h
  simpa using this

/-- `G(u) = Ein(4u)/u ≤ (e^{4u} - 1)/u ≤ e^{4u}/u`. -/
lemma kerG_le {u : ℝ} (hu : 0 < u) : kerG u ≤ rexp (4 * u) / u := by
  have h := hasSum_exp_sub_one (4 * u)
  have hle : ∀ n : ℕ, 4 ^ (n + 1) * u ^ n / ((n + 1) * ((n + 1)! : ℝ)) ≤
      (4 * u) ^ (n + 1) / ((n + 1)! : ℝ) / u := by
    intro n
    have hf : (0 : ℝ) < ((n + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), mul_pow, pow_succ u]
    have : (1 : ℝ) ≤ (n + 1 : ℝ) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hp : 0 ≤ 4 ^ (n + 1) * u ^ n * ((n + 1)! : ℝ) * u := by positivity
    nlinarith
  calc kerG u ≤ (rexp (4 * u) - 1) / u :=
        hasSum_le hle (summable_kerG hu.le).hasSum (h.div_const u)
    _ ≤ rexp (4 * u) / u := by gcongr; linarith

lemma four_le_kerG {u : ℝ} (hu : 0 ≤ u) : 4 ≤ kerG u := by
  have h := (summable_kerG hu).hasSum
  calc (4 : ℝ) = 4 ^ (0 + 1) * u ^ 0 / (((0 : ℕ) : ℝ) + 1) / ((0 + 1)! : ℝ) := by norm_num
    _ ≤ kerG u := by
        have := le_hasSum h 0 (fun n _ => by positivity)
        rw [div_div]; exact this

lemma kerG_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : kerG u ≤ kerG v :=
  hasSum_le (fun n => by gcongr) (summable_kerG hu).hasSum (summable_kerG (hu.trans huv)).hasSum

lemma continuous_kerG : Continuous kerG := by
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  set R := |u₀| + 1
  have hR : 0 ≤ R := by positivity
  have hc : ContinuousOn kerG (Ioo (-R) R) := by
    refine continuousOn_tsum (fun n => by fun_prop) (summable_kerG hR) fun n u hu => ?_
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 4),
      abs_of_pos (by positivity : (0 : ℝ) < (n + 1) * ((n + 1)! : ℝ))]
    gcongr
    exact (abs_lt.2 hu).le
  exact hc.continuousAt (Ioo_mem_nhds (by simp [R]; linarith [neg_abs_le u₀])
    (by simp [R]; linarith [le_abs_self u₀]))

/-! ### The `k`-terms -/

/-- `I_k = ∫_U^∞ e^{-k²u} G(u) du`. -/
noncomputable def kTermK (U : ℝ) (k : ℕ) : ℝ := ∫ u in Ioi U, rexp (-((k : ℝ) ^ 2 * u)) * kerG u

lemma integrableOn_kTermK {U : ℝ} (hU : 0 < U) {k : ℕ} (hk : 3 ≤ k) :
    IntegrableOn (fun u => rexp (-((k : ℝ) ^ 2 * u)) * kerG u) (Ioi U) := by
  have hk' : (9 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hint := (integrableOn_exp_mul_Ioi (a := -((k : ℝ) ^ 2 - 4)) (by linarith) U).const_mul U⁻¹
  refine Integrable.mono' hint (((by fun_prop : Continuous fun u : ℝ =>
    rexp (-((k : ℝ) ^ 2 * u))).mul continuous_kerG) |>.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  have hu : U < u := hu
  have hu0 : 0 < u := hU.trans hu
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith [four_le_kerG hu0.le]))]
  calc rexp (-((k : ℝ) ^ 2 * u)) * kerG u ≤ rexp (-((k : ℝ) ^ 2 * u)) * (rexp (4 * u) / U) := by
        gcongr
        exact (kerG_le hu0).trans (div_le_div_of_nonneg_left (Real.exp_pos _).le hU hu.le)
    _ = U⁻¹ * rexp (-((k : ℝ) ^ 2 - 4) * u) := by
        rw [div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]; ring_nf

/-- **`I_k ≤ e^{-(k²-4)U}/((k²-4)U)`** for `k ≥ 3`. -/
theorem kTermK_le {U : ℝ} (hU : 0 < U) {k : ℕ} (hk : 3 ≤ k) :
    kTermK U k ≤ rexp (-((k : ℝ) ^ 2 - 4) * U) / (((k : ℝ) ^ 2 - 4) * U) := by
  have hk' : (9 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hint := (integrableOn_exp_mul_Ioi (a := -((k : ℝ) ^ 2 - 4)) (by linarith) U).const_mul U⁻¹
  calc kTermK U k ≤ ∫ u in Ioi U, U⁻¹ * rexp (-((k : ℝ) ^ 2 - 4) * u) := by
        refine setIntegral_mono_on (integrableOn_kTermK hU hk) hint measurableSet_Ioi fun u hu => ?_
        have hu : U < u := hu
        have hu0 : 0 < u := hU.trans hu
        calc rexp (-((k : ℝ) ^ 2 * u)) * kerG u ≤ rexp (-((k : ℝ) ^ 2 * u)) * (rexp (4 * u) / U) := by
              gcongr
              exact (kerG_le hu0).trans (div_le_div_of_nonneg_left (Real.exp_pos _).le hU hu.le)
          _ = U⁻¹ * rexp (-((k : ℝ) ^ 2 - 4) * u) := by
              rw [div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]; ring_nf
    _ = rexp (-((k : ℝ) ^ 2 - 4) * U) / (((k : ℝ) ^ 2 - 4) * U) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
        field_simp

/-- **`I_k > 0`.** -/
theorem kTermK_pos {U : ℝ} (hU : 0 < U) {k : ℕ} (hk : 3 ≤ k) : 0 < kTermK U k := by
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have hint := (integrableOn_exp_mul_Ioi (a := -(k : ℝ) ^ 2) (by linarith) U).const_mul 4
  have h : ∫ u in Ioi U, 4 * rexp (-(k : ℝ) ^ 2 * u) ≤ kTermK U k := by
    refine setIntegral_mono_on hint (integrableOn_kTermK hU hk) measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hU.trans hu
    rw [show -(k : ℝ) ^ 2 * u = -((k : ℝ) ^ 2 * u) by ring, mul_comm]
    exact mul_le_mul_of_nonneg_left (four_le_kerG hu0.le) (Real.exp_pos _).le
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)] at h
  refine lt_of_lt_of_le ?_ h
  have := Real.exp_pos (-(k : ℝ) ^ 2 * U)
  have : 0 < -rexp (-(k : ℝ) ^ 2 * U) / -(k : ℝ) ^ 2 := div_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

/-! ### The dual terms -/

/-- `J(c) = √π ∫₀^U u^{-1/2} e^{-c/u} G(u) du`. -/
noncomputable def dualTermK (U c : ℝ) : ℝ :=
  √π * ∫ u in Ioc 0 U, u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) * kerG u

lemma integrableOn_rpow_neg_half {U : ℝ} (hU : 0 < U) :
    IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (Ioc 0 U) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hU.le).1
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num))

lemma integral_rpow_neg_half {U : ℝ} (hU : 0 < U) :
    ∫ u in Ioc 0 U, u ^ (-(1 / 2 : ℝ)) = 2 * √U := by
  rw [← intervalIntegral.integral_of_le hU.le, integral_rpow (Or.inl (by norm_num)),
    Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
  norm_num
  ring

lemma continuousOn_dualK_integrand (c : ℝ) :
    ContinuousOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) * kerG u) (Ioi 0) := by
  intro u hu
  have hu : u ≠ 0 := ne_of_gt hu
  exact (((Real.continuousAt_rpow_const _ _ (Or.inl hu)).mul
    ((continuousAt_const.div continuousAt_id hu).neg.rexp)).mul
      continuous_kerG.continuousAt).continuousWithinAt

/-- **`J_m ≤ 2√(πU) G(U) e^{-c/U}`.** -/
theorem dualTermK_le {U c : ℝ} (hU : 0 < U) (hc : 0 ≤ c) :
    dualTermK U c ≤ 2 * √(π * U) * kerG U * rexp (-(c / U)) := by
  have hb : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * (rexp (-(c / U)) * kerG U)) (Ioc 0 U) :=
    (integrableOn_rpow_neg_half hU).mul_const _
  have hle : ∀ u ∈ Ioc 0 U, u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) * kerG u ≤
      u ^ (-(1 / 2 : ℝ)) * (rexp (-(c / U)) * kerG U) := by
    intro u hu
    have h1 : rexp (-(c / u)) ≤ rexp (-(c / U)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]; exact div_le_div_of_nonneg_left hc hu.1 hu.2
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hu.1.le _)
    exact mul_le_mul h1 (kerG_mono hu.1.le hu.2) (by linarith [four_le_kerG hu.1.le])
      (Real.exp_pos _).le
  have hint : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) * kerG u) (Ioc 0 U) := by
    refine Integrable.mono' hb ((continuousOn_dualK_integrand c).mono Ioc_subset_Ioi_self
      |>.aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _)
      (Real.exp_pos _).le) (by linarith [four_le_kerG hu.1.le]))]
    exact hle u hu
  unfold dualTermK
  calc √π * ∫ u in Ioc 0 U, u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) * kerG u
      ≤ √π * ∫ u in Ioc 0 U, u ^ (-(1 / 2 : ℝ)) * (rexp (-(c / U)) * kerG U) := by
        exact mul_le_mul_of_nonneg_left (setIntegral_mono_on hint hb measurableSet_Ioc hle)
          (Real.sqrt_nonneg _)
    _ = 2 * √(π * U) * kerG U * rexp (-(c / U)) := by
        rw [integral_mul_const, integral_rpow_neg_half hU, Real.sqrt_mul Real.pi_pos.le]; ring

/-! ### The evaluation point -/

lemma integrableOn_dualK {U c : ℝ} (hU : 0 < U) (hc : 0 ≤ c) :
    IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) * kerG u) (Ioc 0 U) := by
  have hb : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * (rexp (-(c / U)) * kerG U)) (Ioc 0 U) :=
    (integrableOn_rpow_neg_half hU).mul_const _
  refine Integrable.mono' hb ((continuousOn_dualK_integrand c).mono Ioc_subset_Ioi_self
    |>.aestronglyMeasurable measurableSet_Ioc) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _)
    (Real.exp_pos _).le) (by linarith [four_le_kerG hu.1.le]))]
  have h1 : rexp (-(c / u)) ≤ rexp (-(c / U)) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]; exact div_le_div_of_nonneg_left hc hu.1 hu.2
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hu.1.le _)
  exact mul_le_mul h1 (kerG_mono hu.1.le hu.2) (by linarith [four_le_kerG hu.1.le])
    (Real.exp_pos _).le

/-- `|e^{-a} - e^{-b}| ≤ e^{-m}|a - b|` for `a, b ≥ m`. -/
lemma abs_exp_neg_sub_le {a b m : ℝ} (ha : m ≤ a) (hb : m ≤ b) :
    |rexp (-a) - rexp (-b)| ≤ rexp (-m) * |a - b| := by
  have key : ∀ x y : ℝ, m ≤ x → x ≤ y → rexp (-x) - rexp (-y) ≤ rexp (-m) * (y - x) := by
    intro x y hx hxy
    have h1 : rexp (-y) = rexp (-x) * rexp (-(y - x)) := by rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-(y - x))
    have h3 : rexp (-x) ≤ rexp (-m) := Real.exp_le_exp.2 (by linarith)
    rw [h1]
    nlinarith [Real.exp_pos (-x)]
  rcases le_total a b with hab | hab
  · have := key a b ha hab
    have h0 : 0 ≤ rexp (-a) - rexp (-b) := by
      have := Real.exp_le_exp.2 (show -b ≤ -a by linarith); linarith
    rw [abs_of_nonneg h0, abs_of_nonpos (by linarith)]; linarith
  · have := key b a hb hab
    have h0 : rexp (-a) - rexp (-b) ≤ 0 := by
      have := Real.exp_le_exp.2 (show -a ≤ -b by linarith); linarith
    rw [abs_of_nonpos h0, abs_of_nonneg (by linarith)]; linarith

/-- `∫₀^U u^{-2} e^{-ξ/u} du = e^{-ξ/U}/ξ`. -/
lemma integral_inv_sq_exp {U ξ : ℝ} (hU : 0 < U) (hξ : 0 < ξ) :
    ∫ u in Ioc 0 U, (u ^ 2)⁻¹ * rexp (-(ξ / u)) = rexp (-(ξ / U)) / ξ := by
  set F : ℝ → ℝ := fun u => if u ≤ 0 then 0 else rexp (-(ξ / u)) / ξ
  have hF0 : Tendsto (fun u : ℝ => rexp (-(ξ / u)) / ξ) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => -(ξ / u)) (𝓝[>] 0) atBot := by
      have := tendsto_neg_atTop_atBot.comp ((tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hξ)
      refine this.congr fun u => ?_
      simp [div_eq_mul_inv]
    have := (Real.tendsto_exp_atBot.comp h1).div_const ξ
    simpa using this
  have hcont : ContinuousOn F (Icc 0 U) := by
    intro u hu
    rcases hu.1.lt_or_eq with hu0 | rfl
    · have : F =ᶠ[𝓝 u] fun u => rexp (-(ξ / u)) / ξ := by
        filter_upwards [lt_mem_nhds hu0] with v hv
        simp [F, not_le.2 hv]
      exact (ContinuousAt.congr (((continuousAt_const.div continuousAt_id hu0.ne').neg.rexp).div_const ξ)
        this.symm).continuousWithinAt
    · refine (continuousWithinAt_Ioi_iff_Ici.1 ?_).mono (fun v hv => hv.1)
      have hF00 : F 0 = 0 := by simp [F]
      rw [ContinuousWithinAt, hF00]
      refine hF0.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      simp [F, not_le.2 (show (0 : ℝ) < v from hv)]
  have hderiv : ∀ u ∈ Ioo 0 U, HasDerivAt F ((u ^ 2)⁻¹ * rexp (-(ξ / u))) u := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have h := (((hasDerivAt_inv hu0.ne').const_mul (-ξ)).exp).div_const ξ
    have e : F =ᶠ[𝓝 u] fun u => rexp (-ξ * u⁻¹) / ξ := by
      filter_upwards [lt_mem_nhds hu0] with v hv
      simp [F, not_le.2 hv, div_eq_mul_inv]
    refine (h.congr_of_eventuallyEq e).congr_deriv ?_
    field_simp
  have hbound : ∀ u ∈ Ioc (0 : ℝ) U, (u ^ 2)⁻¹ * rexp (-(ξ / u)) ≤ 2 / ξ ^ 2 := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have h := Real.pow_div_factorial_le_exp (ξ / u) (by positivity) 2
    have h2 : ξ ^ 2 ≤ rexp (ξ / u) * 2 * u ^ 2 := by
      have e : (ξ / u) ^ 2 / ((2 : ℕ) ! : ℝ) = ξ ^ 2 / (2 * u ^ 2) := by
        rw [div_pow]; norm_num [Nat.factorial]; ring
      rw [e, div_le_iff₀ (by positivity)] at h
      linarith
    have he := Real.exp_pos (ξ / u)
    rw [Real.exp_neg, show (u ^ 2)⁻¹ * (rexp (ξ / u))⁻¹ = 1 / (u ^ 2 * rexp (ξ / u)) by
      field_simp, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h2]
  have hint : IntervalIntegrable (fun u : ℝ => (u ^ 2)⁻¹ * rexp (-(ξ / u))) volume 0 U := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hU.le]
    refine Integrable.mono' (integrableOn_const (C := 2 / ξ ^ 2) (by simp) (by simp)) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioc
      have hu0 : u ≠ 0 := ne_of_gt hu.1
      exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hu0) |>.mul
        ((continuousAt_const.div continuousAt_id hu0).neg.rexp)).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      rw [Real.norm_of_nonneg (by have := hu.1; positivity)]
      exact hbound u hu
  rw [← intervalIntegral.integral_of_le hU.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hU.le hcont hderiv hint]
  simp [F, not_le.2 hU]

/-- **The error from the evaluation point**: for `c, c' ≥ ξ > 0`,
`|J(c) - J(c')| ≤ √π G(U) U^{1/2} e^{-ξ/U}/ξ · |c - c'|`. -/
theorem dualTermK_lipschitz {U ξ c c' : ℝ} (hU : 0 < U) (hξ : 0 < ξ) (hc : ξ ≤ c) (hc' : ξ ≤ c') :
    |dualTermK U c - dualTermK U c'| ≤ √π * kerG U * √U * rexp (-(ξ / U)) / ξ * |c - c'| := by
  have hint := integrableOn_dualK hU (hξ.le.trans hc)
  have hint' := integrableOn_dualK hU (hξ.le.trans hc')
  have hG := four_le_kerG hU.le
  have hb : IntegrableOn (fun u : ℝ => √U * kerG U * |c - c'| * ((u ^ 2)⁻¹ * rexp (-(ξ / u))))
      (Ioc 0 U) := by
    have : IntervalIntegrable (fun u : ℝ => (u ^ 2)⁻¹ * rexp (-(ξ / u))) volume 0 U := by
      by_contra h
      have := intervalIntegral.integral_undef h
      rw [intervalIntegral.integral_of_le hU.le, integral_inv_sq_exp hU hξ] at this
      exact absurd this (div_pos (Real.exp_pos _) hξ).ne'
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hU.le).1 this).const_mul _
  unfold dualTermK
  rw [← mul_sub, ← integral_sub hint hint', abs_mul, abs_of_pos (Real.sqrt_pos.2 Real.pi_pos)]
  have hpt : ∀ u ∈ Ioc (0 : ℝ) U, ‖u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) * kerG u -
      u ^ (-(1 / 2 : ℝ)) * rexp (-(c' / u)) * kerG u‖ ≤
      √U * kerG U * |c - c'| * ((u ^ 2)⁻¹ * rexp (-(ξ / u))) := by
    intro u hu
    have hu0 := hu.1
    have hdiff := abs_exp_neg_sub_le (a := c / u) (b := c' / u) (m := ξ / u)
      (div_le_div_of_nonneg_right hc hu0.le) (div_le_div_of_nonneg_right hc' hu0.le)
    rw [div_sub_div_same, abs_div, abs_of_pos hu0] at hdiff
    have hsq : u ^ (-(1 / 2 : ℝ)) * u⁻¹ ≤ √U * (u ^ 2)⁻¹ := by
      have e : u ^ (-(1 / 2 : ℝ)) * u⁻¹ = √u * (u ^ 2)⁻¹ := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg hu0.le]
        have : u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = u := by
          rw [← Real.rpow_add hu0]; norm_num
        field_simp
        nlinarith [this]
      rw [e]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hu.2) (by positivity)
    rw [Real.norm_eq_abs, ← sub_mul, ← mul_sub, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hu0.le _),
      abs_of_pos (show 0 < kerG u by linarith [four_le_kerG hu0.le])]
    calc u ^ (-(1 / 2 : ℝ)) * |rexp (-(c / u)) - rexp (-(c' / u))| * kerG u
        ≤ u ^ (-(1 / 2 : ℝ)) * (rexp (-(ξ / u)) * (|c - c'| / u)) * kerG U :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdiff (Real.rpow_nonneg hu0.le _))
            (kerG_mono hu0.le hu.2) (by linarith [four_le_kerG hu0.le]) (by positivity)
      _ = (u ^ (-(1 / 2 : ℝ)) * u⁻¹) * kerG U * |c - c'| * rexp (-(ξ / u)) := by ring
      _ ≤ (√U * (u ^ 2)⁻¹) * kerG U * |c - c'| * rexp (-(ξ / u)) := by gcongr
      _ = _ := by ring
  calc √π * |∫ u in Ioc 0 U, (u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) * kerG u -
        u ^ (-(1 / 2 : ℝ)) * rexp (-(c' / u)) * kerG u)|
      ≤ √π * ∫ u in Ioc 0 U, √U * kerG U * |c - c'| * ((u ^ 2)⁻¹ * rexp (-(ξ / u))) := by
        gcongr
        exact norm_integral_le_of_norm_le hb ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall hpt))
    _ = _ := by
        rw [integral_const_mul, integral_inv_sq_exp hU hξ]; ring

end ZetaF
