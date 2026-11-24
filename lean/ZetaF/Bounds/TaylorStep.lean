import ZetaF.Bounds.TaylorRec

open Finset

namespace ZetaF

/-- **Taylor step.** All solutions of the Taylor recurrence of `cY' = (B₀ + cB₁)Y` at `c₀` satisfy
`|h|^l ‖Y_l‖ ≤ (2θ)^l ‖Y_0‖` as soon as `|h| ‖B₀+c₀B₁‖ ≤ θ|c₀|`, `|h| ‖B₁‖ ≤ θ` and `|h| ≤ θ|c₀|`
(matrix norms: sums of absolute values of the entries). -/
theorem taylor_step_bound {D : ℕ} {c₀ h : ℂ} (B₀ B₁ : Matrix (Fin D) (Fin D) ℂ)
    (Y : ℕ → Fin D → ℂ)
    (hrec : ∀ n i, c₀ * (n + 1) * Y (n + 1) i =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * Y n j - n * Y n i +
        ∑ j, B₁ i j * (if n = 0 then 0 else Y (n - 1) j))
    (hc₀ : c₀ ≠ 0) {θ : ℝ}
    (h0 : ‖h‖ * (∑ i, ∑ j, ‖B₀ i j + c₀ * B₁ i j‖) ≤ θ * ‖c₀‖)
    (h1 : ‖h‖ * (∑ i, ∑ j, ‖B₁ i j‖) ≤ θ) (h2 : ‖h‖ ≤ θ * ‖c₀‖) (l : ℕ) :
    ‖h ^ l • Y l‖ ≤ (2 * θ) ^ l * ‖Y 0‖ := by
  have hc0 : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  have hθ : 0 ≤ θ := by
    have h3 : 0 ≤ θ * ‖c₀‖ := (norm_nonneg h).trans h2
    by_contra hneg; push Not at hneg; nlinarith
  set K₀ := ∑ i, ∑ j, ‖B₀ i j + c₀ * B₁ i j‖ with hK₀
  set K₁ := ∑ i, ∑ j, ‖B₁ i j‖ with hK₁
  have hK₁0 : 0 ≤ K₁ := sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  set a : ℕ → ℝ := fun n => ‖h‖ ^ n * ‖Y n‖ with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have ha_eq : ∀ n, ‖h ^ n • Y n‖ = a n := fun n => by rw [norm_smul, norm_pow]
  set pv : ℕ → ℝ := fun n => if n = 0 then 0 else ‖Y (n - 1)‖ with hpv
  have hprev : ∀ n, ‖(fun j => if n = 0 then (0 : ℂ) else Y (n - 1) j)‖ = pv n := by
    intro n
    simp only [hpv]
    split_ifs
    · exact (show (fun _ : Fin D => (0 : ℂ)) = 0 from rfl) ▸ norm_zero
    · rfl
  -- one step of the recurrence, unscaled
  have hstep : ∀ n : ℕ, ‖c₀‖ * ((n : ℝ) + 1) * ‖Y (n + 1)‖ ≤ (K₀ + n) * ‖Y n‖ + K₁ * pv n := by
    intro n
    have hnn : ‖(c₀ * ((n : ℂ) + 1))‖ = ‖c₀‖ * ((n : ℝ) + 1) := by
      rw [norm_mul, show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]; push_cast; ring
    have hpos : 0 < ‖c₀‖ * ((n : ℝ) + 1) := by positivity
    have hb : ∀ i, ‖Y (n + 1) i‖ ≤ ((K₀ + n) * ‖Y n‖ + K₁ * pv n) / (‖c₀‖ * ((n : ℝ) + 1)) := by
      intro i
      rw [le_div_iff₀ hpos]
      have hr := congrArg norm (hrec n i)
      rw [norm_mul, hnn] at hr
      rw [mul_comm, hr]
      refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
      · have a1 := norm_sum_mul_le (fun i j => B₀ i j + c₀ * B₁ i j) (Y n) i
        have a2 : ‖(n : ℂ) * Y n i‖ ≤ n * ‖Y n‖ := by
          rw [norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (Y n) i) (Nat.cast_nonneg _)
        have : (K₀ + n) * ‖Y n‖ = K₀ * ‖Y n‖ + n * ‖Y n‖ := by ring
        rw [this]; exact add_le_add a1 a2
      · have := norm_sum_mul_le B₁ (fun j => if n = 0 then (0 : ℂ) else Y (n - 1) j) i
        rwa [hprev n] at this
    have hK₀0 : 0 ≤ K₀ := sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
    have hpv0 : 0 ≤ pv n := by simp only [hpv]; split_ifs <;> positivity
    have hnum : 0 ≤ ((K₀ + n) * ‖Y n‖ + K₁ * pv n) / (‖c₀‖ * ((n : ℝ) + 1)) := by positivity
    have := (pi_norm_le_iff_of_nonneg hnum).2 hb
    rwa [le_div_iff₀ hpos, mul_comm] at this
  -- scaled step: a_{n+1} ≤ θ a_n + θ² a_{n-1}
  have hkey : ∀ n : ℕ, a (n + 1) ≤ θ * a n + θ ^ 2 * (if n = 0 then 0 else a (n - 1)) := by
    intro n
    set q : ℝ := if n = 0 then 0 else a (n - 1) with hq
    have hq0 : 0 ≤ q := by simp only [hq]; split_ifs <;> simp [ha0]
    have hpvh : ‖h‖ ^ (n + 1) * pv n = ‖h‖ ^ 2 * q := by
      simp only [hpv, hq, ha]
      split_ifs with hn
      · simp
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
    have hm := mul_le_mul_of_nonneg_left (hstep n) (pow_nonneg (norm_nonneg h) (n + 1))
    have e0 : ‖h‖ ^ (n + 1) * (‖c₀‖ * ((n : ℝ) + 1) * ‖Y (n + 1)‖) =
        ‖c₀‖ * ((n : ℝ) + 1) * a (n + 1) := by simp only [ha]; ring
    have e1 : ‖h‖ ^ (n + 1) * ((K₀ + n) * ‖Y n‖ + K₁ * pv n) =
        (‖h‖ * K₀ + n * ‖h‖) * a n + (‖h‖ * K₁) * ‖h‖ * q := by
      rw [mul_add, show ‖h‖ ^ (n + 1) * (K₁ * pv n) = K₁ * (‖h‖ ^ (n + 1) * pv n) by ring, hpvh]
      simp only [ha]; rw [pow_succ]; ring
    rw [e0, e1] at hm
    have hA : (‖h‖ * K₀ + n * ‖h‖) * a n ≤ (θ * ‖c₀‖ * ((n : ℝ) + 1)) * a n := by
      apply mul_le_mul_of_nonneg_right _ (ha0 n)
      have : (n : ℝ) * ‖h‖ ≤ n * (θ * ‖c₀‖) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      nlinarith
    have hB : (‖h‖ * K₁) * ‖h‖ * q ≤ (θ ^ 2 * ‖c₀‖) * q := by
      apply mul_le_mul_of_nonneg_right _ hq0
      calc (‖h‖ * K₁) * ‖h‖ ≤ θ * (θ * ‖c₀‖) :=
            mul_le_mul h1 h2 (norm_nonneg _) hθ
        _ = θ ^ 2 * ‖c₀‖ := by ring
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hfin : ‖c₀‖ * ((n : ℝ) + 1) * a (n + 1) ≤
        ‖c₀‖ * ((n : ℝ) + 1) * (θ * a n + θ ^ 2 * q) := by
      have : θ ^ 2 * ‖c₀‖ * q ≤ ‖c₀‖ * ((n : ℝ) + 1) * (θ ^ 2 * q) := by
        have : 0 ≤ θ ^ 2 * ‖c₀‖ * q := by positivity
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_left hfin (by positivity)
  -- induction: a_l ≤ (2θ)^l a_0
  have hind : ∀ n : ℕ, a n ≤ (2 * θ) ^ n * a 0 ∧ a (n + 1) ≤ (2 * θ) ^ (n + 1) * a 0 := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp, ?_⟩
      have := hkey 0
      simp only [zero_add, ite_true, mul_zero, add_zero] at this
      calc a 1 ≤ θ * a 0 := this
        _ ≤ (2 * θ) ^ 1 * a 0 := by nlinarith [ha0 0]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have := hkey (n + 1)
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false] at this
      have h0' := ha0 0
      calc a (n + 1 + 1) ≤ θ * a (n + 1) + θ ^ 2 * a n := this
        _ ≤ θ * ((2 * θ) ^ (n + 1) * a 0) + θ ^ 2 * ((2 * θ) ^ n * a 0) :=
            add_le_add (mul_le_mul_of_nonneg_left ih.2 hθ)
              (mul_le_mul_of_nonneg_left ih.1 (by positivity))
        _ = 3 * θ ^ 2 * (2 * θ) ^ n * a 0 := by ring
        _ ≤ 4 * θ ^ 2 * (2 * θ) ^ n * a 0 := by
            have : 0 ≤ θ ^ 2 * (2 * θ) ^ n * a 0 := by positivity
            nlinarith
        _ = (2 * θ) ^ (n + 1 + 1) * a 0 := by ring
  rw [ha_eq]
  have := (hind l).1
  simpa [ha] using this

/-- **Tail of a Taylor stage**: under the hypotheses of `taylor_step_bound` with `θ < 1/2`, the Taylor
series `∑ h^l Y_l` converges absolutely and its tail after `L` terms is at most
`(2θ)^L ‖Y_0‖/(1 - 2θ)`. -/
theorem taylor_step_tail {D : ℕ} {c₀ h : ℂ} (B₀ B₁ : Matrix (Fin D) (Fin D) ℂ)
    (Y : ℕ → Fin D → ℂ)
    (hrec : ∀ n i, c₀ * (n + 1) * Y (n + 1) i =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * Y n j - n * Y n i +
        ∑ j, B₁ i j * (if n = 0 then 0 else Y (n - 1) j))
    (hc₀ : c₀ ≠ 0) {θ : ℝ}
    (h0 : ‖h‖ * (∑ i, ∑ j, ‖B₀ i j + c₀ * B₁ i j‖) ≤ θ * ‖c₀‖)
    (h1 : ‖h‖ * (∑ i, ∑ j, ‖B₁ i j‖) ≤ θ) (h2 : ‖h‖ ≤ θ * ‖c₀‖) (hθ : θ < 1 / 2) (L : ℕ) :
    Summable (fun l => h ^ l • Y l) ∧
      ‖∑' l, h ^ (l + L) • Y (l + L)‖ ≤ (2 * θ) ^ L * ‖Y 0‖ / (1 - 2 * θ) := by
  have hθ0 : 0 ≤ θ := by
    have hc0 : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
    have h3 : 0 ≤ θ * ‖c₀‖ := (norm_nonneg h).trans h2
    by_contra hneg; push_neg at hneg; nlinarith
  have hr0 : 0 ≤ 2 * θ := by linarith
  have hr1 : 2 * θ < 1 := by linarith
  have hb := fun l => taylor_step_bound B₀ B₁ Y hrec hc₀ h0 h1 h2 l
  have hg : Summable fun l : ℕ => (2 * θ) ^ l * ‖Y 0‖ :=
    (summable_geometric_of_lt_one hr0 hr1).mul_right _
  have hs : Summable (fun l => h ^ l • Y l) := Summable.of_norm_bounded hg hb
  refine ⟨hs, ?_⟩
  have hgL : Summable fun l : ℕ => (2 * θ) ^ L * ‖Y 0‖ * (2 * θ) ^ l :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  calc ‖∑' l, h ^ (l + L) • Y (l + L)‖ ≤ ∑' l : ℕ, (2 * θ) ^ L * ‖Y 0‖ * (2 * θ) ^ l :=
        tsum_of_norm_bounded hgL.hasSum (fun l => (hb (l + L)).trans (le_of_eq (by ring)))
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; ring

end ZetaF
