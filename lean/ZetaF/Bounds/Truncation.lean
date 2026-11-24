/-
# Truncation of the theta splitting (Appendix A.3, eq. (18))

For the abstract splitting (`theta_split`) we prove explicit tail bounds
* `‖∑_{k ≥ K} I_k‖ ≤ C_far · e^{-(K² - k₀²)u₀} / (1 - e^{-u₀})`,
* `‖∑_{m ≥ M} J_m‖ ≤ C_near · e^{-π² M²/u₀} / (1 - e^{-π²/u₀})`,
with `C_far = ∫_{u₀}^∞ e^{-k₀²u}|h|` and `C_near = ∫₀^{u₀} u^{-1/2}|h|`, and that the choices
`K = ⌈√(p log 2 / u₀)⌉`, `M = ⌈√(p log 2 · u₀)/π⌉` make `e^{-K²u₀}, e^{-π²M²/u₀} ≤ 2^{-p}`, with
`p log 2 / π ≤ K M` and `(K - 1)(M - 1) < p log 2 / π` — so the product of the two counts is
`≈ p log 2/π` independently of `u₀`, as claimed in §5.2 ("Balancing").
-/
import ZetaF.Splitting.Abstract

open Real MeasureTheory Set Filter

namespace ZetaF

variable {h : ℝ → ℂ} {u₀ : ℝ}

/-- `∑_{k ≥ 0} e^{-(k+K)² c} ≤ e^{-K² c}/(1 - e^{-c})`. -/
lemma tsum_exp_neg_sq_shift_le {c : ℝ} (hc : 0 < c) (K : ℕ) (A : ℝ) :
    HasSum (fun k : ℕ => rexp (-((K : ℝ) ^ 2 - A) * c) * rexp (-c) ^ k)
      (rexp (-((K : ℝ) ^ 2 - A) * c) / (1 - rexp (-c))) := by
  have h1 : rexp (-c) < 1 := by simpa using Real.exp_lt_exp.2 (show -c < 0 by linarith)
  have := (hasSum_geometric_of_lt_one (exp_pos _).le h1).mul_left (rexp (-((K : ℝ) ^ 2 - A) * c))
  simpa [div_eq_mul_inv] using this

lemma exp_shift_le {c : ℝ} (hc : 0 < c) (K k : ℕ) (A : ℝ) :
    rexp (-((((k + K : ℕ) : ℝ)) ^ 2 - A) * c) ≤ rexp (-((K : ℝ) ^ 2 - A) * c) * rexp (-c) ^ k := by
  rw [← Real.exp_natCast_mul, ← Real.exp_add, Real.exp_le_exp]
  have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
  have h2 : 0 ≤ ((k : ℝ) ^ 2 - k + 2 * k * K) * c :=
    mul_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) k]) hc.le
  push_cast
  nlinarith [h2]

/-- Tail bound for the `k`-terms. -/
theorem norm_tsum_kTerm_tail_le {k₀ K : ℕ} (hK : k₀ ≤ K) (hu₀ : 0 < u₀)
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀)) :
    ‖∑' k : ℕ, kTerm h u₀ (k + K)‖ ≤
      (∫ u in Ioi u₀, rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) *
        (rexp (-((K : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀) / (1 - rexp (-u₀))) := by
  set C := ∫ u in Ioi u₀, rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖
  refine tsum_of_norm_bounded ((tsum_exp_neg_sq_shift_le hu₀ K ((k₀ : ℝ) ^ 2)).mul_left C) ?_
  intro k
  have hkk : (k₀ : ℝ) ≤ ((k + K : ℕ) : ℝ) := by exact_mod_cast le_trans hK (Nat.le_add_left K k)
  calc ‖kTerm h u₀ (k + K)‖
      ≤ ∫ u in Ioi u₀, ‖(rexp (-(((k + K : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi u₀, rexp (-((((k + K : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2) * u₀) *
          (rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
          (hfar.const_mul _) ?_
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, ← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have := exp_sq_le hkk (Nat.cast_nonneg _) (le_of_lt hu)
        convert this using 2; ring
    _ = C * rexp (-((((k + K : ℕ) : ℝ)) ^ 2 - (k₀ : ℝ) ^ 2) * u₀) := by
        rw [integral_const_mul]; ring
    _ ≤ C * (rexp (-((K : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀) * rexp (-u₀) ^ k) := by
        apply mul_le_mul_of_nonneg_left (exp_shift_le hu₀ K k _)
        exact integral_nonneg fun u => mul_nonneg (exp_pos _).le (norm_nonneg _)

/-- Tail bound for the dual terms. -/
theorem norm_tsum_dualTerm_tail_le (M : ℕ) (hu₀ : 0 < u₀)
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖h u‖) (Ioc 0 u₀)) :
    ‖∑' m : ℕ, dualTerm h u₀ (m + M)‖ ≤
      (∫ u in Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * ‖h u‖) *
        (rexp (-((M : ℝ) ^ 2 - 0) * (π ^ 2 / u₀)) / (1 - rexp (-(π ^ 2 / u₀)))) := by
  set C := ∫ u in Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * ‖h u‖
  have hc : 0 < π ^ 2 / u₀ := by positivity
  refine tsum_of_norm_bounded ((tsum_exp_neg_sq_shift_le hc M 0).mul_left C) ?_
  intro m
  calc ‖dualTerm h u₀ (m + M)‖
      ≤ ∫ u in Ioc 0 u₀, ‖(((u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 * (((m + M : ℕ) : ℝ)) ^ 2 / u))) : ℝ)
          : ℂ) * h u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioc 0 u₀, rexp (-((((m + M : ℕ) : ℝ)) ^ 2 - 0) * (π ^ 2 / u₀)) *
          (u ^ (-(1 / 2 : ℝ)) * ‖h u‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
          (hnear.const_mul _) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
        have hr := Real.rpow_nonneg hu.1.le (-(1 / 2 : ℝ))
        dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hr (exp_pos _).le)]
        rw [show u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 * (((m + M : ℕ) : ℝ)) ^ 2 / u)) * ‖h u‖ =
          rexp (-(π ^ 2 * (((m + M : ℕ) : ℝ)) ^ 2 / u)) * (u ^ (-(1 / 2 : ℝ)) * ‖h u‖) by ring]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hr (norm_nonneg _))
        rw [exp_le_exp]
        have : π ^ 2 * (((m + M : ℕ) : ℝ)) ^ 2 / u₀ ≤ π ^ 2 * (((m + M : ℕ) : ℝ)) ^ 2 / u :=
          div_le_div_of_nonneg_left (by positivity) hu.1 hu.2
        have e : -((((m + M : ℕ) : ℝ)) ^ 2 - 0) * (π ^ 2 / u₀) =
          -(π ^ 2 * (((m + M : ℕ) : ℝ)) ^ 2 / u₀) := by ring
        rw [e]; linarith
    _ = C * rexp (-((((m + M : ℕ) : ℝ)) ^ 2 - 0) * (π ^ 2 / u₀)) := by
        rw [integral_const_mul]; ring
    _ ≤ C * (rexp (-((M : ℝ) ^ 2 - 0) * (π ^ 2 / u₀)) * rexp (-(π ^ 2 / u₀)) ^ m) := by
        apply mul_le_mul_of_nonneg_left (exp_shift_le hc M m _)
        exact setIntegral_nonneg measurableSet_Ioc fun u hu =>
          mul_nonneg (Real.rpow_nonneg hu.1.le _) (norm_nonneg _)

/-! ### The term counts (18) -/

/-- Number of `k`-terms for `p` bits: `K = ⌈√(p log 2 / u₀)⌉`. -/
noncomputable def kCount (p : ℕ) (u₀ : ℝ) : ℕ := ⌈√(p * Real.log 2 / u₀)⌉₊

/-- Number of dual terms for `p` bits: `M = ⌈√(p log 2 · u₀)/π⌉`. -/
noncomputable def mCount (p : ℕ) (u₀ : ℝ) : ℕ := ⌈√(p * Real.log 2 * u₀) / π⌉₊

lemma exp_kCount_le (p : ℕ) (hu₀ : 0 < u₀) :
    rexp (-((kCount p u₀ : ℝ) ^ 2 * u₀)) ≤ 2⁻¹ ^ p := by
  have hx : √(p * Real.log 2 / u₀) ≤ kCount p u₀ := Nat.le_ceil _
  have hsq : p * Real.log 2 / u₀ ≤ (kCount p u₀ : ℝ) ^ 2 := by
    have h0 : 0 ≤ p * Real.log 2 / u₀ := by positivity
    calc p * Real.log 2 / u₀ = √(p * Real.log 2 / u₀) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
  have : p * Real.log 2 ≤ (kCount p u₀ : ℝ) ^ 2 * u₀ := by
    rwa [div_le_iff₀ hu₀] at hsq
  rw [inv_pow, ← Real.exp_log (show (0 : ℝ) < 2 ^ p by positivity), ← Real.exp_neg,
    Real.exp_le_exp, Real.log_pow]
  linarith

lemma exp_mCount_le (p : ℕ) (hu₀ : 0 < u₀) :
    rexp (-((mCount p u₀ : ℝ) ^ 2 * (π ^ 2 / u₀))) ≤ 2⁻¹ ^ p := by
  have hx : √(p * Real.log 2 * u₀) / π ≤ mCount p u₀ := Nat.le_ceil _
  have h0 : 0 ≤ p * Real.log 2 * u₀ := by positivity
  have hsq : p * Real.log 2 * u₀ / π ^ 2 ≤ (mCount p u₀ : ℝ) ^ 2 := by
    calc p * Real.log 2 * u₀ / π ^ 2 = (√(p * Real.log 2 * u₀) / π) ^ 2 := by
          rw [div_pow, Real.sq_sqrt h0]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hx 2
  have : p * Real.log 2 ≤ (mCount p u₀ : ℝ) ^ 2 * (π ^ 2 / u₀) := by
    rw [div_le_iff₀ (by positivity)] at hsq
    rw [mul_div_assoc', le_div_iff₀ hu₀]; nlinarith [pi_pos]
  rw [inv_pow, ← Real.exp_log (show (0 : ℝ) < 2 ^ p by positivity), ← Real.exp_neg,
    Real.exp_le_exp, Real.log_pow]
  linarith

/-- **Balancing**: `p log 2/π ≤ K M` for every `u₀ > 0`. -/
lemma kCount_mul_mCount_ge (p : ℕ) (hu₀ : 0 < u₀) :
    p * Real.log 2 / π ≤ (kCount p u₀ : ℝ) * mCount p u₀ := by
  have h1 : √(p * Real.log 2 / u₀) ≤ kCount p u₀ := Nat.le_ceil _
  have h2 : √(p * Real.log 2 * u₀) / π ≤ mCount p u₀ := Nat.le_ceil _
  have h0 : 0 ≤ (p : ℝ) * Real.log 2 := by positivity
  have e1 : √(p * Real.log 2 / u₀) * √(p * Real.log 2 * u₀) = p * Real.log 2 := by
    rw [← Real.sqrt_mul (by positivity),
      show p * Real.log 2 / u₀ * (p * Real.log 2 * u₀) = (p * Real.log 2) ^ 2 by field_simp]
    exact Real.sqrt_sq h0
  have e : √(p * Real.log 2 / u₀) * (√(p * Real.log 2 * u₀) / π) = p * Real.log 2 / π := by
    rw [mul_div_assoc', e1]
  rw [← e]
  exact mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg _)

/-- **Balancing**: `(K - 1)(M - 1) < p log 2/π` for `p ≥ 1`. -/
lemma kCount_mul_mCount_lt (p : ℕ) (hp : 1 ≤ p) (hu₀ : 0 < u₀) :
    ((kCount p u₀ : ℝ) - 1) * ((mCount p u₀ : ℝ) - 1) < p * Real.log 2 / π := by
  have hp' : (0 : ℝ) < p * Real.log 2 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  set x := √(p * Real.log 2 / u₀)
  set y := √(p * Real.log 2 * u₀) / π
  have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
  have hy : 0 < y := div_pos (Real.sqrt_pos.2 (by positivity)) pi_pos
  have hK1 : (kCount p u₀ : ℝ) - 1 < x := by
    have := Nat.ceil_lt_add_one hx.le; unfold kCount; linarith
  have hM1 : (mCount p u₀ : ℝ) - 1 < y := by
    have := Nat.ceil_lt_add_one hy.le; unfold mCount; linarith
  have hK0 : (1 : ℝ) ≤ kCount p u₀ := by
    have : 0 < kCount p u₀ := Nat.ceil_pos.2 hx
    exact_mod_cast this
  have hM0 : (1 : ℝ) ≤ mCount p u₀ := by
    have : 0 < mCount p u₀ := Nat.ceil_pos.2 hy
    exact_mod_cast this
  have e1 : x * √(p * Real.log 2 * u₀) = p * Real.log 2 := by
    rw [← Real.sqrt_mul (by positivity),
      show p * Real.log 2 / u₀ * (p * Real.log 2 * u₀) = (p * Real.log 2) ^ 2 by field_simp]
    exact Real.sqrt_sq hp'.le
  have hxy : x * y = p * Real.log 2 / π := by
    simp only [y]; rw [mul_div_assoc', e1]
  rw [← hxy]
  rcases eq_or_lt_of_le hK0 with hK | hK
  · rw [← hK, sub_self, zero_mul]; positivity
  · calc ((kCount p u₀ : ℝ) - 1) * ((mCount p u₀ : ℝ) - 1) < ((kCount p u₀ : ℝ) - 1) * y :=
          mul_lt_mul_of_pos_left hM1 (by linarith)
      _ ≤ x * y := mul_le_mul_of_nonneg_right hK1.le hy.le

end ZetaF
