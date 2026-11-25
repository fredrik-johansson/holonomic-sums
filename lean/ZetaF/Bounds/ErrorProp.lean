/-
# Error propagation (Appendix A.1 and Section 6.4.2)

* `error_propagation`: a chain of Lipschitz steps `x_{j+1} = f_j(x_j)`, computed with local errors
  `‖y_{j+1} - f_j(y_j)‖ ≤ ε_j`, has global error `∏ M_j ‖y_0 - x_0‖ + ∑ ε_j ∏_{i>j} M_i`.
  This is the error analysis of the bit-burst stages, where `f_j` is the transition matrix of
  `cY' = (B₀ + cB₁)Y` from `c_j` to `c_{j+1}` and `ε_j` is the truncation error of stage `j`.
* `tail_le_of_ratio`, `tail_le_two_mul`: "every tail is at most twice its first term" once the
  terms decrease by a factor `2`, the device used throughout the error bounds of Section 6.4.2 and Appendix A.
* `point_error_le`: the last item, evaluating at `c_ℓ` with `|c - c_ℓ| ≤ δ` costs `δ max|J'|`.
-/
import ZetaF.Deps

open Finset

namespace ZetaF

/-- **Global error of a chain of approximate steps.** -/
theorem error_propagation {E : Type*} [SeminormedAddCommGroup E] (f : ℕ → E → E) (M ε : ℕ → ℝ)
    (hM : ∀ j x y, ‖f j x - f j y‖ ≤ M j * ‖x - y‖) (hM0 : ∀ j, 0 ≤ M j)
    (x y : ℕ → E) (hx : ∀ j, x (j + 1) = f j (x j)) (hy : ∀ j, ‖y (j + 1) - f j (y j)‖ ≤ ε j)
    (n : ℕ) :
    ‖y n - x n‖ ≤ (∏ j ∈ range n, M j) * ‖y 0 - x 0‖ +
      ∑ j ∈ range n, ε j * ∏ i ∈ Ico (j + 1) n, M i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ‖y (n + 1) - x (n + 1)‖ ≤ ε n + M n * ‖y n - x n‖ := by
      rw [hx n]
      calc ‖y (n + 1) - f n (x n)‖ = ‖(y (n + 1) - f n (y n)) + (f n (y n) - f n (x n))‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := add_le_add (hy n) (hM n _ _)
    have h2 : ∑ j ∈ range (n + 1), ε j * ∏ i ∈ Ico (j + 1) (n + 1), M i =
        (∑ j ∈ range n, ε j * ∏ i ∈ Ico (j + 1) n, M i) * M n + ε n := by
      rw [sum_range_succ, Ico_self, prod_empty, mul_one, sum_mul]
      congr 1
      refine sum_congr rfl fun j hj => ?_
      rw [prod_Ico_succ_top (by simp at hj; omega), mul_assoc]
    rw [h2, prod_range_succ]
    calc ‖y (n + 1) - x (n + 1)‖ ≤ ε n + M n * ‖y n - x n‖ := h1
      _ ≤ ε n + M n * ((∏ j ∈ range n, M j) * ‖y 0 - x 0‖ +
          ∑ j ∈ range n, ε j * ∏ i ∈ Ico (j + 1) n, M i) :=
          add_le_add_right (mul_le_mul_of_nonneg_left ih (hM0 n)) _
      _ = _ := by ring

/-- **Uniform version**: with all Lipschitz constants `≤ M`, `M ≥ 1`, the error is at most
`M^n (‖y_0 - x_0‖ + ∑ ε_j)`. -/
theorem error_propagation_uniform {E : Type*} [SeminormedAddCommGroup E] (f : ℕ → E → E)
    {M : ℝ} (ε : ℕ → ℝ) (hM : ∀ j x y, ‖f j x - f j y‖ ≤ M * ‖x - y‖) (hM1 : 1 ≤ M)
    (x y : ℕ → E) (hx : ∀ j, x (j + 1) = f j (x j)) (hy : ∀ j, ‖y (j + 1) - f j (y j)‖ ≤ ε j)
    (n : ℕ) : ‖y n - x n‖ ≤ M ^ n * (‖y 0 - x 0‖ + ∑ j ∈ range n, ε j) := by
  have h := error_propagation f (fun _ => M) ε hM (fun _ => by linarith) x y hx hy n
  have hε : ∀ j, 0 ≤ ε j := fun j => (norm_nonneg _).trans (hy j)
  simp only [prod_const, card_range, Nat.card_Ico] at h
  refine h.trans ?_
  rw [mul_add, mul_sum]
  refine add_le_add le_rfl (sum_le_sum fun j _ => ?_)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 (by omega)) (hε j)

/-- Linear steps: the Lipschitz constant of a continuous linear map is its operator norm. -/
theorem error_propagation_linear {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (T : ℕ → E →L[𝕜] E) (ε : ℕ → ℝ)
    (x y : ℕ → E) (hx : ∀ j, x (j + 1) = T j (x j)) (hy : ∀ j, ‖y (j + 1) - T j (y j)‖ ≤ ε j)
    (n : ℕ) :
    ‖y n - x n‖ ≤ (∏ j ∈ range n, ‖T j‖) * ‖y 0 - x 0‖ +
      ∑ j ∈ range n, ε j * ∏ i ∈ Ico (j + 1) n, ‖T i‖ :=
  error_propagation (fun j => T j) (fun j => ‖T j‖) ε
    (fun j a b => by rw [← map_sub]; exact (T j).le_opNorm _) (fun _ => norm_nonneg _) x y hx hy n

/-- **Tails of ratio-bounded series.** -/
theorem tail_le_of_ratio {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (f : ℕ → E)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) (hf : ∀ n ≥ N, ‖f (n + 1)‖ ≤ r * ‖f n‖) :
    Summable (fun k => f (N + k)) ∧ ‖∑' k, f (N + k)‖ ≤ ‖f N‖ / (1 - r) := by
  have hk : ∀ k, ‖f (N + k)‖ ≤ ‖f N‖ * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc ‖f (N + (k + 1))‖ = ‖f ((N + k) + 1)‖ := rfl
        _ ≤ r * ‖f (N + k)‖ := hf _ (by omega)
        _ ≤ r * (‖f N‖ * r ^ k) := mul_le_mul_of_nonneg_left ih hr0
        _ = _ := by ring
  have hs : Summable fun k => ‖f N‖ * r ^ k := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine ⟨Summable.of_norm_bounded hs hk, ?_⟩
  calc ‖∑' k, f (N + k)‖ ≤ ∑' k, ‖f N‖ * r ^ k := tsum_of_norm_bounded hs.hasSum hk
    _ = ‖f N‖ / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- **"Every tail is at most twice its first term"** once the terms halve. -/
theorem tail_le_two_mul {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (f : ℕ → E)
    (N : ℕ) (hf : ∀ n ≥ N, ‖f (n + 1)‖ ≤ ‖f n‖ / 2) :
    Summable (fun k => f (N + k)) ∧ ‖∑' k, f (N + k)‖ ≤ 2 * ‖f N‖ := by
  have h := tail_le_of_ratio f (r := 1 / 2) (by norm_num) (by norm_num) N
    (fun n hn => by rw [one_div_mul_eq_div]; exact hf n hn)
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  ring

/-- **Error from the evaluation point**: `‖J(c) - J(c')‖ ≤ K |c - c'|` if `‖J'‖ ≤ K` on the segment. -/
theorem point_error_le {J : ℝ → ℝ} {K a b c c' : ℝ} (hJ : ∀ ξ ∈ Set.Icc a b, DifferentiableAt ℝ J ξ)
    (hK : ∀ ξ ∈ Set.Icc a b, ‖deriv J ξ‖ ≤ K) (hc : c ∈ Set.Icc a b) (hc' : c' ∈ Set.Icc a b) :
    ‖J c - J c'‖ ≤ K * ‖c - c'‖ :=
  (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hJ hK hc' hc

end ZetaF
