/-
# The Taylor recurrence of the bit-burst step (Appendix A.1)

If `Y(c) ∈ ℂ^D` satisfies `c Y'(c) = (B₀ + c B₁) Y(c)`, its Taylor coefficients `Y_l` at `c₀` satisfy
`c₀ (l+1) Y_{l+1} = (B₀ + c₀ B₁ - l) Y_l + B₁ Y_{l-1}`.
We prove this (as an equivalence) for formal power series in `h = c - c₀`: the system reads
`(c₀ + h) dY/dh = (B₀ + (c₀ + h) B₁) Y`.
-/
import ZetaF.Deps

open PowerSeries Finset

namespace ZetaF

variable {D : ℕ}

/-- A constant matrix acting on a vector of power series. -/
noncomputable def matApply (B : Matrix (Fin D) (Fin D) ℂ) (Y : Fin D → PowerSeries ℂ) :
    Fin D → PowerSeries ℂ :=
  fun i => ∑ j, C (B i j) * Y j

/-- The coefficient `Y_{l-1}`, with `Y_{-1} = 0`. -/
noncomputable def prevCoeff (n : ℕ) (f : PowerSeries ℂ) : ℂ := if n = 0 then 0 else coeff (n - 1) f

lemma coeff_X_mul' (n : ℕ) (f : PowerSeries ℂ) : coeff n (X * f) = prevCoeff n f := by
  cases n with
  | zero => simp [prevCoeff]
  | succ n => rw [coeff_succ_X_mul]; simp [prevCoeff]

lemma coeff_matApply (B : Matrix (Fin D) (Fin D) ℂ) (Y : Fin D → PowerSeries ℂ) (i : Fin D)
    (n : ℕ) : coeff n (matApply B Y i) = ∑ j, B i j * coeff n (Y j) := by
  simp [matApply, map_sum, coeff_C_mul]

lemma prevCoeff_matApply (B : Matrix (Fin D) (Fin D) ℂ) (Y : Fin D → PowerSeries ℂ) (i : Fin D)
    (n : ℕ) : prevCoeff n (matApply B Y i) = ∑ j, B i j * prevCoeff n (Y j) := by
  unfold prevCoeff
  split_ifs
  · simp
  · exact coeff_matApply B Y i (n - 1)

/-- **Taylor recurrence of `c Y' = (B₀ + c B₁) Y` at `c₀`.** -/
theorem taylor_rec_iff (c₀ : ℂ) (B₀ B₁ : Matrix (Fin D) (Fin D) ℂ) (Y : Fin D → PowerSeries ℂ) :
    (∀ i, (C c₀ + X) * d⁄dX (Y i) = matApply B₀ Y i + (C c₀ + X) * matApply B₁ Y i) ↔
    ∀ n i, c₀ * (n + 1) * coeff (n + 1) (Y i) =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * coeff n (Y j) - n * coeff n (Y i) +
        ∑ j, B₁ i j * prevCoeff n (Y j) := by
  have key : ∀ i n, coeff n ((C c₀ + X) * d⁄dX (Y i)) =
      c₀ * (n + 1) * coeff (n + 1) (Y i) + n * coeff n (Y i) := by
    intro i n
    rw [add_mul, map_add, coeff_C_mul, coeff_X_mul', coeff_derivative]
    unfold prevCoeff
    split_ifs with h
    · subst h; simp
    · rw [coeff_derivative, Nat.sub_add_cancel (Nat.pos_of_ne_zero h),
        Nat.cast_sub (Nat.pos_of_ne_zero h)]
      push_cast; ring
  have key2 : ∀ i n, coeff n (matApply B₀ Y i + (C c₀ + X) * matApply B₁ Y i) =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * coeff n (Y j) + ∑ j, B₁ i j * prevCoeff n (Y j) := by
    intro i n
    rw [map_add, add_mul, map_add, coeff_C_mul, coeff_X_mul', coeff_matApply, coeff_matApply,
      prevCoeff_matApply, mul_sum, ← add_assoc, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  constructor
  · intro h n i
    have := congrArg (coeff n) (h i)
    rw [key, key2] at this
    linear_combination this
  · intro h i
    ext n
    rw [key, key2, h n i]
    ring

/-! ### Radius of convergence

If the coefficients satisfy the recurrence, they grow at most like `t^l` for every `t > 1/|c₀|`;
hence the Taylor series converges for `|c - c₀| < |c₀|`, as stated in Appendix A.1. -/

lemma norm_sum_mul_le (M : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ) (i : Fin D) :
    ‖∑ j, M i j * v j‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := by
  calc ‖∑ j, M i j * v j‖ ≤ ∑ j, ‖M i j‖ * ‖v‖ := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
    _ = (∑ j, ‖M i j‖) * ‖v‖ := by rw [sum_mul]
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact single_le_sum (f := fun i => ∑ j, ‖M i j‖) (fun i _ => sum_nonneg fun j _ =>
          norm_nonneg _) (mem_univ i)

/-- **Growth of the Taylor coefficients.** -/
theorem taylor_rec_growth {c₀ : ℂ} (B₀ B₁ : Matrix (Fin D) (Fin D) ℂ) (Y : ℕ → Fin D → ℂ)
    (hrec : ∀ n i, c₀ * (n + 1) * Y (n + 1) i =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * Y n j - n * Y n i +
        ∑ j, B₁ i j * (if n = 0 then 0 else Y (n - 1) j))
    {t : ℝ} (ht : 1 < t * ‖c₀‖) : ∃ C, ∀ n, ‖Y n‖ ≤ C * t ^ n := by
  have hc0 : 0 < ‖c₀‖ := by
    rcases (norm_nonneg c₀).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at ht; linarith
  have ht0 : 0 < t := by
    by_contra h; push Not at h; nlinarith
  set K₀ := ∑ i, ∑ j, ‖B₀ i j + c₀ * B₁ i j‖
  set K₁ := ∑ i, ∑ j, ‖B₁ i j‖
  have hK₀ : 0 ≤ K₀ := sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  have hK₁ : 0 ≤ K₁ := sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  set ρ := 1 / (‖c₀‖ * t)
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by rw [div_lt_one (by positivity)]; linarith
  obtain ⟨L, hL⟩ := exists_nat_ge ((K₀ * ρ + K₁ * ρ / t) / (1 - ρ))
  set C := ∑ n ∈ range (L + 1), ‖Y n‖ / t ^ n
  have hC : 0 ≤ C := sum_nonneg fun _ _ => by positivity
  refine ⟨C, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n L with hn | hn
    · have : ‖Y n‖ / t ^ n ≤ C :=
        single_le_sum (f := fun n => ‖Y n‖ / t ^ n) (fun _ _ => by positivity)
          (mem_range.2 (by omega))
      rwa [div_le_iff₀ (by positivity)] at this
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hm := ih m (by omega)
      have hprev : ‖(fun j => if m = 0 then (0 : ℂ) else Y (m - 1) j)‖ ≤ C * t ^ m / t := by
        by_cases hm0 : m = 0
        · simp only [hm0, ite_true]
          rw [show (fun _ : Fin D => (0 : ℂ)) = 0 from rfl, norm_zero]; positivity
        · simp only [hm0, ite_false]
          have := ih (m - 1) (by omega)
          rw [show m = (m - 1) + 1 by omega, pow_succ]
          calc ‖fun j => Y (m - 1) j‖ = ‖Y (m - 1)‖ := rfl
            _ ≤ C * t ^ (m - 1) := this
            _ = C * (t ^ (m - 1) * t) / t := by field_simp
      have hden : 0 < ‖c₀ * ((m : ℂ) + 1)‖ := by
        rw [norm_mul]; exact mul_pos hc0 (by rw [show (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by
          push_cast; ring, Complex.norm_natCast]; positivity)
      have hnm : ‖c₀ * ((m : ℂ) + 1)‖ = ‖c₀‖ * ((m : ℝ) + 1) := by
        rw [norm_mul, show (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
          Complex.norm_natCast]; push_cast; ring
      have hbound : ∀ i, ‖Y (m + 1) i‖ ≤ C * t ^ (m + 1) := by
        intro i
        have hr := hrec m i
        have h1 : ‖c₀ * (m + 1) * Y (m + 1) i‖ ≤ (K₀ + m) * (C * t ^ m) + K₁ * (C * t ^ m / t) := by
          rw [hr]
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
          · have a1 := (norm_sum_mul_le (fun i j => B₀ i j + c₀ * B₁ i j) (Y m) i).trans
              (mul_le_mul_of_nonneg_left hm hK₀)
            have a2 : ‖(m : ℂ) * Y m i‖ ≤ m * (C * t ^ m) := by
              rw [norm_mul, Complex.norm_natCast]
              exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (Y m) i).trans hm)
                (Nat.cast_nonneg _)
            linarith
          · exact (norm_sum_mul_le B₁ _ i).trans (mul_le_mul_of_nonneg_left hprev hK₁)
        rw [norm_mul, hnm] at h1
        have hmL : ((K₀ * ρ + K₁ * ρ / t) / (1 - ρ)) ≤ (m : ℝ) + 1 := by
          have : (L : ℝ) ≤ m := by exact_mod_cast (by omega : L ≤ m)
          linarith
        rw [div_le_iff₀ (by linarith)] at hmL
        have hfin : (K₀ + m) * (C * t ^ m) + K₁ * (C * t ^ m / t) ≤
            ‖c₀‖ * ((m : ℝ) + 1) * (C * t ^ (m + 1)) := by
          have hct : ‖c₀‖ * t * ρ = 1 := by simp only [ρ]; field_simp
          have hCt : 0 ≤ C * t ^ m := by positivity
          have key : (K₀ + m) * ρ + K₁ * ρ / t ≤ (m : ℝ) + 1 := by nlinarith
          have : (K₀ + m) + K₁ / t ≤ ‖c₀‖ * t * ((m : ℝ) + 1) := by
            have h2 : ((K₀ + m) + K₁ / t) * ρ ≤ (m + 1) := by
              calc ((K₀ + m) + K₁ / t) * ρ = (K₀ + m) * ρ + K₁ * ρ / t := by ring
                _ ≤ _ := key
            calc (K₀ + m) + K₁ / t = ((K₀ + m) + K₁ / t) * ρ * (‖c₀‖ * t) := by
                  rw [mul_assoc, mul_comm ρ, hct, mul_one]
              _ ≤ (m + 1) * (‖c₀‖ * t) :=
                  mul_le_mul_of_nonneg_right h2 (by positivity)
              _ = _ := by ring
          calc (K₀ + m) * (C * t ^ m) + K₁ * (C * t ^ m / t)
              = ((K₀ + m) + K₁ / t) * (C * t ^ m) := by ring
            _ ≤ (‖c₀‖ * t * ((m : ℝ) + 1)) * (C * t ^ m) := mul_le_mul_of_nonneg_right this hCt
            _ = _ := by rw [pow_succ]; ring
        have := h1.trans hfin
        exact le_of_mul_le_mul_left (by linarith [this]) (by positivity : 0 < ‖c₀‖ * ((m : ℝ) + 1))
          |> fun h => by nlinarith [h1, hfin, norm_nonneg (Y (m + 1) i)]
      exact (pi_norm_le_iff_of_nonneg (by positivity)).2 hbound

/-- **Convergence of the Taylor series for `|c - c₀| < |c₀|`.** -/
theorem taylor_rec_summable {c₀ : ℂ} (B₀ B₁ : Matrix (Fin D) (Fin D) ℂ) (Y : ℕ → Fin D → ℂ)
    (hrec : ∀ n i, c₀ * (n + 1) * Y (n + 1) i =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * Y n j - n * Y n i +
        ∑ j, B₁ i j * (if n = 0 then 0 else Y (n - 1) j))
    {h : ℂ} (hh : ‖h‖ < ‖c₀‖) : Summable fun n => h ^ n • Y n := by
  rcases eq_or_ne h 0 with rfl | h0
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp at hn; simp [zero_pow hn]
  have hh0 : 0 < ‖h‖ := norm_pos_iff.2 h0
  set t := (1 / ‖h‖ + 1 / ‖c₀‖) / 2
  have hc0 : 0 < ‖c₀‖ := hh0.trans hh
  have ht1 : 1 < t * ‖c₀‖ := by
    simp only [t]
    rw [div_mul_eq_mul_div, lt_div_iff₀ two_pos, add_mul, one_div_mul_cancel hc0.ne']
    have : 1 < 1 / ‖h‖ * ‖c₀‖ := by rw [one_div_mul_eq_div, one_lt_div hh0]; exact hh
    linarith
  have ht2 : t * ‖h‖ < 1 := by
    simp only [t]
    rw [div_mul_eq_mul_div, div_lt_one two_pos, add_mul, one_div_mul_cancel hh0.ne']
    have : 1 / ‖c₀‖ * ‖h‖ < 1 := by rw [one_div_mul_eq_div, div_lt_one hc0]; exact hh
    linarith
  obtain ⟨C, hC⟩ := taylor_rec_growth B₀ B₁ Y hrec ht1
  have ht0 : 0 ≤ t * ‖h‖ := by positivity
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one ht0 ht2).mul_left C) fun n => ?_
  rw [norm_smul, norm_pow, mul_pow]
  calc ‖h‖ ^ n * ‖Y n‖ ≤ ‖h‖ ^ n * (C * t ^ n) := mul_le_mul_of_nonneg_left (hC n) (by positivity)
    _ = C * (t ^ n * ‖h‖ ^ n) := by ring

end ZetaF
