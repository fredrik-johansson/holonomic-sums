/-
# Theorem 6.3: the theta splitting of Algorithm K3

`log K · log 2 = log²2 + Li₂(-1/2) + π²/12 + ½(M + ∑_{k≥3}(-1)^k I_k + ∑_{m≥0} J_m)` for every `U > 0`,
with `I_k = ∫_U^∞ e^{-k²u} G`, `J_m = √π ∫₀^U u^{-1/2} e^{-π²(m+½)²/u} G`,
`M = ∫₀^U (e^{-u} - e^{-4u} - ½) G`, `G(u) = Ein(4u)/u`.
Ingredients: `Li₂(4/k²) = ∫₀^∞ e^{-k²u} G` (`laplace_kerG`), the transformation of `θ₄`
(`theta4_half`), the general twisted splitting `theta_split_gen`, and Lemma 6.2.
-/
import ZetaF.Khinchin.BBC
import ZetaF.Khinchin.Bounds
import ZetaF.Twisted.Split
import ZetaF.Polylog.Theta

open MeasureTheory Set Filter Real
open scoped Nat Topology

namespace ZetaF

/-- **`Li₂(4/κ) = ∫₀^∞ e^{-κu} G(u) du`** for `κ ≥ 4`. -/
theorem laplace_kerG {κ : ℝ} (hκ : 4 ≤ κ) :
    HasSum (fun n : ℕ => ∫ u in Ioi 0, rexp (-(κ * u)) * (4 ^ (n + 1) * u ^ n /
      ((n + 1) * ((n + 1)! : ℝ)))) (Li₂ (4 / κ)) ∧
    ∫ u in Ioi 0, rexp (-(κ * u)) * kerG u = Li₂ (4 / κ) := by
  have hκ0 : 0 < κ := by linarith
  have hterm : ∀ n : ℕ, ∫ u in Ioi 0, rexp (-(κ * u)) * (4 ^ (n + 1) * u ^ n /
      ((n + 1) * ((n + 1)! : ℝ))) = (4 / κ) ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (by positivity) hκ0
    have e1 : ∀ u ∈ Ioi (0 : ℝ), rexp (-(κ * u)) * (4 ^ (n + 1) * u ^ n / ((n + 1) * ((n + 1)! : ℝ))) =
        (4 ^ (n + 1) / ((n + 1) * ((n + 1)! : ℝ))) * (u ^ ((n : ℝ) + 1 - 1) * rexp (-(κ * u))) := by
      intro u hu
      rw [show (n : ℝ) + 1 - 1 = (n : ℕ) by ring, Real.rpow_natCast]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi e1, integral_const_mul, h,
      Real.Gamma_nat_eq_factorial, show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    have hf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast
    field_simp
    ring
  have hint : ∀ n : ℕ, IntegrableOn (fun u => rexp (-(κ * u)) * (4 ^ (n + 1) * u ^ n /
      ((n + 1) * ((n + 1)! : ℝ)))) (Ioi 0) := by
    intro n
    have h : IntegrableOn (fun x : ℝ => (4 ^ (n + 1) / ((n + 1) * ((n + 1)! : ℝ))) *
        (x ^ (n : ℝ) * rexp (-κ * x ^ (1 : ℝ)))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := κ)
        (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) one_pos hκ0).const_mul _
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, Real.rpow_natCast]; ring
  have hx : |4 / κ| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one hκ0]; exact hκ
  have hsumLi := hasSum_Li₂ hx
  have hS : HasSum (fun n : ℕ => ∫ u in Ioi 0, rexp (-(κ * u)) * (4 ^ (n + 1) * u ^ n /
      ((n + 1) * ((n + 1)! : ℝ)))) (Li₂ (4 / κ)) := by
    simp_rw [hterm]; exact hsumLi
  refine ⟨hS, ?_⟩
  have hnorm : Summable fun n : ℕ => ∫ u in Ioi 0, ‖rexp (-(κ * u)) * (4 ^ (n + 1) * u ^ n /
      ((n + 1) * ((n + 1)! : ℝ)))‖ := by
    refine hS.summable.congr fun n => ?_
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu : 0 < u := hu
    rw [Real.norm_of_nonneg (by positivity)]
  have := hasSum_integral_of_summable_integral_norm hint hnorm
  rw [hS.unique this]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu : (0 : ℝ) ≤ u := le_of_lt hu
  simp only [kerG]
  rw [tsum_mul_left]

/-! ### The transformation of `θ₄` -/

/-- The weights of the dual terms: `√π` at odd indices. -/
noncomputable def dK3 (j : ℕ) : ℂ := if Odd j then ((√π : ℝ) : ℂ) else 0

lemma norm_dK3_le (j : ℕ) : ‖dK3 j‖ ≤ √π := by
  unfold dK3; split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  · simp [Real.sqrt_nonneg]

lemma hasSum_half_shift {u : ℝ} (hu : 0 < u) :
    Summable fun m : ℕ => rexp (-(π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 / u)) := by
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
    (summable_geometric_of_lt_one (r := rexp (-(π ^ 2 / u))) (Real.exp_pos _).le
      (by rw [Real.exp_lt_one_iff, neg_lt_zero]; positivity))
  rw [← Real.exp_natCast_mul, Real.exp_le_exp]
  have hm : (m : ℝ) ≤ ((m : ℝ) + 1 / 2) ^ 2 := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have : (m : ℝ) * (π ^ 2 / u) ≤ ((m : ℝ) + 1 / 2) ^ 2 * (π ^ 2 / u) :=
    mul_le_mul_of_nonneg_right hm (by positivity)
  have e : -(π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 / u) = -(((m : ℝ) + 1 / 2) ^ 2 * (π ^ 2 / u)) := by ring
  rw [e]; linarith

/-- **`θ₄`**: `∑_{k ≥ 1} (-1)^k e^{-k²u} = -½ + u^{-1/2} ∑_{j ≥ 1} d_j e^{-(π²/4) j²/u}`,
with `d_j = √π` for odd `j` and `0` otherwise. -/
theorem theta4_half {u : ℝ} (hu : 0 < u) :
    ∑' k : ℕ, ((-1 : ℂ) ^ (k + 1)) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      0 * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) + (-(1 / 2)) + ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' m : ℕ, dK3 (m + 1) * (rexp (-(π ^ 2 / 4 * ((m : ℝ) + 1) ^ 2 / u)) : ℂ) := by
  have hθ := tsum_geoC_theta (1 / 2) hu
  have hz : Complex.exp (2 * π * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [show 2 * π * Complex.I * ((1 / 2 : ℝ) : ℂ) = π * Complex.I by push_cast; ring,
      Complex.exp_pi_mul_I]
  have hC : ∀ k : ℕ, geoC (Complex.exp (2 * π * Complex.I * ((1 / 2 : ℝ) : ℂ))) (k + 1) =
      (-1 : ℂ) ^ (k + 1) := fun k => by
    rw [hz, geoC]
    rcases neg_one_pow_eq_or ℂ (k + 1) with h | h <;> rw [h] <;> norm_num
  simp_rw [hC] at hθ
  rw [hθ]
  -- the dual sum over `ℤ` is twice the sum over half-integers `m + 1/2`, `m ≥ 0`
  set h : ℕ → ℝ := fun m => rexp (-(π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 / u))
  have hs := hasSum_half_shift hu
  set S := ∑' m, h m
  have hf : ∀ n : ℕ, geoDual (1 / 2) ((n + 1 : ℕ) : ℤ) = π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 := fun n => by
    rw [geoDual]; push_cast; ring
  have hf' : ∀ n : ℕ, geoDual (1 / 2) (-((n : ℤ) + 1)) = π ^ 2 * (((n + 1 : ℕ) : ℝ) + 1 / 2) ^ 2 :=
    fun n => by rw [geoDual]; push_cast; ring
  have hf0 : geoDual (1 / 2) ((0 : ℕ) : ℤ) = π ^ 2 * (((0 : ℕ) : ℝ) + 1 / 2) ^ 2 := by
    rw [geoDual]; push_cast; ring
  have h1 : HasSum (fun n : ℕ => rexp (-(geoDual (1 / 2) (n : ℤ) / u))) (h 0 + S) := by
    refine (hasSum_nat_add_iff' 1).1 ?_
    simp only [Finset.range_one, Finset.sum_singleton]
    rw [hf0, add_sub_cancel_left]
    simp_rw [hf]; exact hs.hasSum
  have h2 : HasSum (fun n : ℕ => rexp (-(geoDual (1 / 2) (-((n : ℤ) + 1)) / u))) (S - h 0) := by
    simp_rw [hf']
    have := (hasSum_nat_add_iff' 1).2 hs.hasSum
    rw [Finset.range_one, Finset.sum_singleton] at this
    exact this
  have hZ := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => rexp (-(geoDual (1 / 2) n / u))) h1 h2
  rw [show h 0 + S + (S - h 0) = 2 * S by ring] at hZ
  have hZc : ∑' n : ℤ, (rexp (-(geoDual (1 / 2) n / u)) : ℂ) = ((2 * S : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum, hZ.tsum_eq]
  -- the odd-index sum
  have hodd : ∑' m : ℕ, dK3 (m + 1) * (rexp (-(π ^ 2 / 4 * ((m : ℝ) + 1) ^ 2 / u)) : ℂ) =
      ((√π * S : ℝ) : ℂ) := by
    set g : ℕ → ℂ := fun m => dK3 (m + 1) * (rexp (-(π ^ 2 / 4 * ((m : ℝ) + 1) ^ 2 / u)) : ℂ)
    have hinj : Function.Injective fun m : ℕ => 2 * m := fun a b hab => by simpa using hab
    have hsupp : Function.support g ⊆ Set.range fun m : ℕ => 2 * m := by
      intro j hj
      rcases Nat.even_or_odd j with ⟨r, hr⟩ | ho
      · exact ⟨r, by show 2 * r = j; omega⟩
      · exfalso; apply hj
        have : ¬ Odd (j + 1) := Nat.not_odd_iff_even.2 ho.add_one
        simp only [g, dK3, this, ite_false, zero_mul]
    rw [← hinj.tsum_eq hsupp]
    have e : ∀ m : ℕ, g (2 * m) = ((√π : ℝ) : ℂ) * (h m : ℂ) := fun m => by
      simp only [g, dK3, odd_two_mul_add_one, ite_true, h]
      congr 3
      push_cast; ring
    simp_rw [e]
    rw [tsum_mul_left, ← Complex.ofReal_tsum, ← Complex.ofReal_mul]
  rw [hZc, hodd]
  push_cast
  ring

/-! ### Theorem 6.3 -/

/-- The main term `M = ∫₀^U (e^{-u} - e^{-4u} - ½) G`. -/
noncomputable def mainK3 (U : ℝ) : ℝ :=
  ∫ u in Ioc 0 U, (rexp (-u) - rexp (-(4 * u)) - 1 / 2) * kerG u

lemma kerG_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ kerG u := by linarith [four_le_kerG hu]

/-- **Theorem 6.3** (with `I_k`, `J_m`, `M` as integrals): for every `U > 0`,
`log K log 2 = log²2 + Li₂(-1/2) + π²/12 + ½(M + ∑_{k≥3}(-1)^k I_k + ∑_{m≥0} J_m)`. -/
theorem khinchin_K3_split {U : ℝ} (hU : 0 < U) :
    logK * Real.log 2 = Real.log 2 ^ 2 + Li₂ (-1 / 2) + π ^ 2 / 12 +
      1 / 2 * (mainK3 U + ∑' k : ℕ, (-1) ^ (k + 3) * kTermK U (k + 3) +
        ∑' m : ℕ, dualTermK U (π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2)) := by
  set h : ℝ → ℂ := fun u => (kerG u : ℂ)
  have hcont : ContinuousOn h (Ioi 0) :=
    (Complex.continuous_ofReal.comp continuous_kerG).continuousOn
  have hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖h u‖) (Ioc 0 U) := by
    refine Integrable.mono' ((integrableOn_rpow_neg_half hU).mul_const (kerG U)) ?_ ?_
    · exact ((ContinuousOn.mono (s := Ioi (0 : ℝ)) (fun u hu => (Real.continuousAt_rpow_const u
        (-(1 / 2 : ℝ)) (Or.inl (ne_of_gt hu))).continuousWithinAt) Ioc_subset_Ioi_self).mul
        (continuous_norm.comp (Complex.continuous_ofReal.comp continuous_kerG)).continuousOn
        ) |>.aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      simp only [h, Complex.norm_real, Real.norm_of_nonneg (kerG_nonneg hu.1.le)]
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (kerG_nonneg hu.1.le))]
      exact mul_le_mul_of_nonneg_left (kerG_mono hu.1.le hu.2) (Real.rpow_nonneg hu.1.le _)
  have hfar : IntegrableOn (fun u => rexp (-(((3 : ℕ) : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi U) := by
    refine (integrableOn_kTermK hU (le_refl 3)).congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [h, Complex.norm_real, Real.norm_of_nonneg (kerG_nonneg (hU.trans hu).le)]
  have HS := theta_split_gen (c := fun k => (-1 : ℂ) ^ k) (d := dK3) (B := 1) (B' := √π)
    (fun k => by simp) norm_dK3_le (lam := π ^ 2 / 4) (by positivity) (α := 0) (β := -(1 / 2))
    (fun u hu => theta4_half hu) (k₀ := 3) (by norm_num) hU hcont hnear hfar
  -- the left-hand side
  have hL : ∀ k : ℕ, ∫ u in Ioi 0, (rexp (-(((k + 3 : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u =
      ((Li₂ (4 / ((k : ℝ) + 3) ^ 2) : ℝ) : ℂ) := by
    intro k
    have hκ : (4 : ℝ) ≤ ((k : ℝ) + 3) ^ 2 := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [← (laplace_kerG hκ).2, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [h]; push_cast; ring_nf
  simp_rw [hL] at HS
  -- the k-terms
  have hk : ∀ k : ℕ, kTerm h U (k + 3) = ((kTermK U (k + 3) : ℝ) : ℂ) := by
    intro k
    rw [kTerm, kTermK, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [h]; push_cast; ring_nf
  -- the dual terms
  have hd : ∑' m : ℕ, dK3 (m + 1) * dualTermGen h U (π ^ 2 / 4) (m + 1) =
      ((∑' m : ℕ, dualTermK U (π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2) : ℝ) : ℂ) := by
    set g : ℕ → ℂ := fun j => dK3 (j + 1) * dualTermGen h U (π ^ 2 / 4) (j + 1)
    have hinj : Function.Injective fun m : ℕ => 2 * m := fun a b hab => by simpa using hab
    have hsupp : Function.support g ⊆ Set.range fun m : ℕ => 2 * m := by
      intro j hj
      rcases Nat.even_or_odd j with ⟨r, hr⟩ | ho
      · exact ⟨r, by show 2 * r = j; omega⟩
      · exfalso; apply hj
        have : ¬ Odd (j + 1) := Nat.not_odd_iff_even.2 ho.add_one
        simp only [g, dK3, this, ite_false, zero_mul]
    have e : ∀ m : ℕ, g (2 * m) = ((dualTermK U (π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2) : ℝ) : ℂ) := by
      intro m
      simp only [g, dK3, odd_two_mul_add_one, ite_true, dualTermGen, dualTermK]
      rw [Complex.ofReal_mul, ← integral_complex_ofReal]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
      simp only [h]
      have : π ^ 2 / 4 * (((2 * m + 1 : ℕ) : ℝ)) ^ 2 = π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 := by
        push_cast; ring
      rw [this]; push_cast; ring
    rw [← hinj.tsum_eq hsupp]
    simp_rw [e]
    rw [Complex.ofReal_tsum]
  -- the main term
  have hm : mainTermGen h U (fun k => (-1 : ℂ) ^ k) 0 (-(1 / 2)) 3 = ((mainK3 U : ℝ) : ℂ) := by
    rw [mainTermGen, mainK3, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [mainWeightGen, h, show Finset.Ico 1 3 = {1, 2} by rfl,
      Finset.sum_pair (show (1 : ℕ) ≠ 2 by norm_num)]
    push_cast
    ring_nf
  simp_rw [hk] at HS
  rw [hd, hm] at HS
  have HSr : HasSum (fun k : ℕ => (-1 : ℝ) ^ (k + 3) * Li₂ (4 / ((k : ℝ) + 3) ^ 2))
      ((∑' k : ℕ, (-1) ^ (k + 3) * kTermK U (k + 3)) +
        (∑' m : ℕ, dualTermK U (π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2)) + mainK3 U) := by
    have : HasSum (fun k : ℕ => (((-1 : ℝ) ^ (k + 3) * Li₂ (4 / ((k : ℝ) + 3) ^ 2) : ℝ) : ℂ))
        ((((∑' k : ℕ, (-1) ^ (k + 3) * kTermK U (k + 3)) +
          (∑' m : ℕ, dualTermK U (π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2)) + mainK3 U : ℝ)) : ℂ) := by
      convert HS using 1
      · funext k; push_cast; ring
      · rw [Complex.ofReal_add, Complex.ofReal_add, Complex.ofReal_tsum]
        congr 2
        refine tsum_congr fun k => ?_
        push_cast; ring
    exact Complex.hasSum_ofReal.1 this
  -- Lemma 6.2 and the term `k = 2`
  rw [logK_mul_log_two_eq_dilog]
  have hsum := (summable_Li₂_div_sq (c := 4) (by norm_num) le_rfl).mul_left 1
  have hsum' : Summable fun k : ℕ => (-1 : ℝ) ^ k * Li₂ (4 / ((k : ℝ) + 2) ^ 2) :=
    Summable.of_norm_bounded (summable_Li₂_div_sq (c := 4) (by norm_num) le_rfl).abs fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [hsum'.tsum_eq_zero_add]
  have e2 : ∑' k : ℕ, (-1 : ℝ) ^ (k + 1) * Li₂ (4 / (((k + 1 : ℕ) : ℝ) + 2) ^ 2) =
      ∑' k : ℕ, (-1 : ℝ) ^ (k + 3) * Li₂ (4 / ((k : ℝ) + 3) ^ 2) := by
    refine tsum_congr fun k => ?_
    rw [show k + 3 = k + 1 + 2 by ring, pow_add (-1 : ℝ) (k + 1) 2]
    push_cast; ring_nf
  rw [e2, HSr.tsum_eq]
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add]
  rw [show (4 : ℝ) / 2 ^ 2 = 1 by norm_num, Li₂_one]
  ring

end ZetaF
