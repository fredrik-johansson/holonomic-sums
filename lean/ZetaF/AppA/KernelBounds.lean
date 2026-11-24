/-
# Appendix A (L4): uniform bounds for the kernel `h_s`, the `k`-terms and the dual terms

Paper, Appendix A, §"Uniformity and memory", paragraph "Truncation".  For `|a_n| ≤ C R^n`, `u₀ > 0`
and `|s| ≤ S` (`S ≥ 2`), with constants depending only on `C, R, u₀` (and `k₀`):

* `norm_kernel_le_far`: `|h_s(u)| ≤ e^{A S log S} e^{R² u}` for `u ≥ u₀` (the paper has the weaker
  `2^{O(p)} (1+u)² e^{R²u}`, which is `norm_kernel_le_far'`);
* `norm_kernel_le_near`: `|h_s(u)| ≤ e^{A S log S} u^{-S/2-1}` for `0 < u ≤ u₀`;
* `norm_kTerm_le_uniform`: `|I_k(s)| ≤ e^{A S log S} e^{-(k²-R²)u₀}` for `k ≥ k₀ > R`;
* `norm_dualTerm_le_uniform`: `|J_m(s)| ≤ e^{A S log S} e^{-π²m²/(2u₀)}` for `m ≥ 1`.

These hold for **every** `s` with `|s| ≤ S`, in particular for `Re s ≤ 1`: `kTerm (kernel a s)` and
`dualTerm (kernel a s)` are exactly the (entire) terms of `splitRHS`, the right-hand side of
Theorem 3.2 used for the continuation (`ZetaF/Continuation/Theorem.lean`).  This removes the
restriction `Re s + n₀ > 1` of `norm_tsum_dualTerm_tail_le` (`ZetaF/Bounds/Truncation.lean`).

The proof follows the paper, except that the `n`-sum of the kernel is split by parity, `n = 2m + ε`,
which turns it into the sums `∑_m (R²u)^m |1/Γ(σ_ε + m + 1)|` of (L5) with `σ_ε = (s+ε)/2 - 1`; the sharp
form of (L5) (with `max(1,x)^{-Re σ}`) makes the powers of `u` cancel for large `u`.
-/
import ZetaF.AppA.GammaSums
import ZetaF.Splitting.Kernel

open Finset Filter MeasureTheory Set
open scoped Real

namespace ZetaF.AppA

/-! ### Elementary inequalities -/

/-- `v^ρ ≤ L^T` if `L⁻¹ ≤ v ≤ L`, `L ≥ 1`, `|ρ| ≤ T`. -/
lemma rpow_le_of_mem_Icc {v L ρ T : ℝ} (hv : 0 < v) (hL : 1 ≤ L) (hvL : L⁻¹ ≤ v) (hvL' : v ≤ L)
    (hρ : |ρ| ≤ T) : v ^ ρ ≤ L ^ T := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  rw [Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hL0, Real.exp_le_exp]
  have h1 : Real.log v ≤ Real.log L := Real.log_le_log hv hvL'
  have h2 : -Real.log L ≤ Real.log v := by
    rw [← Real.log_inv]; exact Real.log_le_log (inv_pos.2 hL0) hvL
  have hlL : 0 ≤ Real.log L := Real.log_nonneg hL
  have h3 : |Real.log v| ≤ Real.log L := abs_le.2 ⟨h2, h1⟩
  calc Real.log v * ρ ≤ |Real.log v * ρ| := le_abs_self _
    _ = |Real.log v| * |ρ| := abs_mul _ _
    _ ≤ Real.log L * T := mul_le_mul h3 hρ (abs_nonneg _) hlL

/-- `t^α e^{-t} ≤ 1 + ⌈α⌉!` for `t > 0`, `α ≥ 0`. -/
lemma rpow_mul_exp_neg_le {t α : ℝ} (ht : 0 < t) (hα : 0 ≤ α) :
    t ^ α * Real.exp (-t) ≤ 1 + (⌈α⌉₊.factorial : ℝ) := by
  set n := ⌈α⌉₊
  rcases le_or_gt t 1 with ht1 | ht1
  · have h1 : t ^ α ≤ 1 := Real.rpow_le_one ht.le ht1 hα
    have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have : t ^ α * Real.exp (-t) ≤ 1 := by
      calc t ^ α * Real.exp (-t) ≤ 1 * 1 :=
            mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
    linarith [(Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ n.factorial)]
  · have h1 : t ^ α ≤ t ^ n := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le ht1.le (Nat.le_ceil α)
    have h2 := Real.pow_div_factorial_le_exp (x := t) ht.le n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [div_le_iff₀ hf] at h2
    have h3 : t ^ α * Real.exp (-t) ≤ n.factorial := by
      calc t ^ α * Real.exp (-t) ≤ t ^ n * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ ≤ Real.exp t * n.factorial * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = n.factorial := by
            rw [mul_comm, ← mul_assoc, ← Real.exp_add]; simp
    linarith

/-- `⌈α S + β⌉!` is `e^{O(S log S)}`. -/
lemma SLogBound.factorial_ceil {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    SLogBound fun S => ((⌈α * S + β⌉₊).factorial : ℝ) := by
  have h := SLogBound.pow_of_le (b := fun S => max 1 (⌈α * S + β⌉₊ : ℝ))
    (N := fun S => ⌈α * S + β⌉₊) (c := α + β + 2) (d := α) (e := β + 1)
    (by linarith) hα (by linarith) (fun S _ => le_max_left _ _) (fun S hS => ?_) (fun S hS => ?_)
  · refine h.of_le fun S hS => ?_
    calc ((⌈α * S + β⌉₊).factorial : ℝ) ≤ ((⌈α * S + β⌉₊ ^ ⌈α * S + β⌉₊ : ℕ) : ℝ) :=
          Nat.cast_le.2 (Nat.factorial_le_pow _)
      _ = (⌈α * S + β⌉₊ : ℝ) ^ ⌈α * S + β⌉₊ := by push_cast; ring
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) _
  · have := Nat.ceil_lt_add_one (show 0 ≤ α * S + β by positivity)
    apply max_le
    · nlinarith
    · nlinarith
  · have := Nat.ceil_lt_add_one (show 0 ≤ α * S + β by positivity)
    linarith

/-- (L5) with a nonnegative constant. -/
lemma exists_L5_nonneg :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ S : ℝ, 2 ≤ S → ∀ σ : ℂ, ‖σ‖ ≤ S → ∀ x : ℝ, 0 ≤ x →
      Summable (fun j : ℕ => x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖) ∧
      ∑' j : ℕ, x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ ≤
        Real.exp (A * S * Real.log S) * max 1 x ^ (-σ.re) * Real.exp x := by
  obtain ⟨A, hA⟩ := sum_pow_mul_norm_inv_Gamma_le_sharp
  refine ⟨max A 0, le_max_right _ _, fun S hS σ hσ x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hA S hS σ hσ x hx
  refine ⟨h1, h2.trans ?_⟩
  have : 0 ≤ max 1 x ^ (-σ.re) :=
    Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (exp_mono_A hS (le_max_left A 0)) this) (Real.exp_pos _).le

/-! ### The kernel, split by parity -/

variable {a : ℕ → ℂ} {C R : ℝ}

/-- The parity-`ε` part of the kernel: `∑_m |a_{2m+ε} u^{(s+2m+ε)/2-1}/Γ((s+2m+ε)/2)|` is at most
`C R^ε u^ρ e^{A(S+1)log(S+1)} max(1,R²u)^{-ρ} e^{R²u}`, `ρ = (Re s + ε)/2 - 1`. -/
lemma kernel_parity_le {A : ℝ}
    (hA : ∀ S : ℝ, 2 ≤ S → ∀ σ : ℂ, ‖σ‖ ≤ S → ∀ x : ℝ, 0 ≤ x →
      Summable (fun j : ℕ => x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖) ∧
      ∑' j : ℕ, x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ ≤
        Real.exp (A * S * Real.log S) * max 1 x ^ (-σ.re) * Real.exp x)
    (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) (hR : 0 ≤ R) {S : ℝ} (hS : 2 ≤ S) {s : ℂ} (hs : ‖s‖ ≤ S)
    (ε : ℕ) (hε : ε ≤ 1) {u : ℝ} (hu : 0 < u) :
    Summable (fun m : ℕ => ‖kernelTerm a s (2 * m + ε) u‖) ∧
      ∑' m : ℕ, ‖kernelTerm a s (2 * m + ε) u‖ ≤
        C * R ^ ε * u ^ ((s.re + ε) / 2 - 1) *
          (Real.exp (A * (S + 1) * Real.log (S + 1)) *
            max 1 (R ^ 2 * u) ^ (-((s.re + ε) / 2 - 1)) * Real.exp (R ^ 2 * u)) := by
  set σ : ℂ := (s + ε) / 2 - 1 with hσ
  have hσre : σ.re = (s.re + ε) / 2 - 1 := by simp [hσ]
  have hεR : (ε : ℝ) ≤ 1 := by exact_mod_cast hε
  have hσn : ‖σ‖ ≤ S + 1 := by
    calc ‖σ‖ ≤ ‖(s + ε) / 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖s‖ + ‖(ε : ℂ)‖) / 2 + 1 := by
          rw [norm_div, norm_one, Complex.norm_two]
          gcongr; exact norm_add_le _ _
      _ ≤ S + 1 := by rw [Complex.norm_natCast]; linarith
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (ha 0); simpa using this
  set x := R ^ 2 * u with hx
  have hx0 : 0 ≤ x := by positivity
  obtain ⟨h1, h2⟩ := hA (S + 1) (by linarith) σ hσn x hx0
  set K := C * R ^ ε * u ^ ((s.re + ε) / 2 - 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hle : ∀ m : ℕ, ‖kernelTerm a s (2 * m + ε) u‖ ≤
      K * (x ^ m * ‖(Complex.Gamma (σ + m + 1))⁻¹‖) := by
    intro m
    rw [norm_kernelTerm hu]
    have e1 : (s + ((2 * m + ε : ℕ) : ℂ)) / 2 = σ + m + 1 := by
      rw [hσ]; push_cast; ring
    have e2 : u ^ ((s.re + ((2 * m + ε : ℕ) : ℝ)) / 2 - 1) =
        u ^ ((s.re + ε) / 2 - 1) * u ^ m := by
      rw [← Real.rpow_natCast u m, ← Real.rpow_add hu]; congr 1; push_cast; ring
    rw [e1, e2]
    have ha' : ‖a (2 * m + ε)‖ ≤ C * R ^ ε * (R ^ 2) ^ m := by
      refine (ha _).trans (le_of_eq ?_)
      rw [← pow_mul, mul_assoc, ← pow_add]; ring_nf
    calc ‖a (2 * m + ε)‖ * ‖(Complex.Gamma (σ + m + 1))⁻¹‖ *
          (u ^ ((s.re + ε) / 2 - 1) * u ^ m)
        ≤ C * R ^ ε * (R ^ 2) ^ m * ‖(Complex.Gamma (σ + m + 1))⁻¹‖ *
          (u ^ ((s.re + ε) / 2 - 1) * u ^ m) := by gcongr
      _ = K * (x ^ m * ‖(Complex.Gamma (σ + m + 1))⁻¹‖) := by
          rw [hK, hx, mul_pow]; ring
  have hs' := h1.mul_left K
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs', ?_⟩
  calc ∑' m : ℕ, ‖kernelTerm a s (2 * m + ε) u‖
      ≤ ∑' m : ℕ, K * (x ^ m * ‖(Complex.Gamma (σ + m + 1))⁻¹‖) :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs') hs'
    _ = K * ∑' m : ℕ, x ^ m * ‖(Complex.Gamma (σ + m + 1))⁻¹‖ := tsum_mul_left
    _ ≤ K * (Real.exp (A * (S + 1) * Real.log (S + 1)) * max 1 x ^ (-σ.re) * Real.exp x) :=
        mul_le_mul_of_nonneg_left h2 hK0
    _ = _ := by rw [hσre]

/-- `|h_s(u)|` is at most the sum of the two parity bounds. -/
lemma norm_kernel_le_parity {A : ℝ}
    (hA : ∀ S : ℝ, 2 ≤ S → ∀ σ : ℂ, ‖σ‖ ≤ S → ∀ x : ℝ, 0 ≤ x →
      Summable (fun j : ℕ => x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖) ∧
      ∑' j : ℕ, x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ ≤
        Real.exp (A * S * Real.log S) * max 1 x ^ (-σ.re) * Real.exp x)
    (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) (hR : 0 ≤ R) {S : ℝ} (hS : 2 ≤ S) {s : ℂ} (hs : ‖s‖ ≤ S)
    {u : ℝ} (hu : 0 < u) {B : ℝ}
    (hB : ∀ ε : ℕ, ε ≤ 1 → C * R ^ ε * u ^ ((s.re + ε) / 2 - 1) *
          (Real.exp (A * (S + 1) * Real.log (S + 1)) *
            max 1 (R ^ 2 * u) ^ (-((s.re + ε) / 2 - 1)) * Real.exp (R ^ 2 * u)) ≤ B) :
    ‖kernel a s u‖ ≤ 2 * B := by
  obtain ⟨h01, h02⟩ := kernel_parity_le hA ha hR hS hs 0 (Nat.zero_le _) hu
  obtain ⟨h11, h12⟩ := kernel_parity_le hA ha hR hS hs 1 le_rfl hu
  have h0' : HasSum (fun m : ℕ => ‖kernelTerm a s (2 * m) u‖)
      (∑' m : ℕ, ‖kernelTerm a s (2 * m + 0) u‖) := h01.hasSum
  have hsum := HasSum.even_add_odd (f := fun n => ‖kernelTerm a s n u‖) h0' h11.hasSum
  refine (tsum_of_norm_bounded hsum fun n => le_rfl).trans ?_
  have e0 := h02.trans (hB 0 (Nat.zero_le _))
  have e1 := h12.trans (hB 1 le_rfl)
  linarith

/-! ### (L4): the kernel -/

/-- **(L4), far range.** For `|a_n| ≤ C R^n` and `u₀ > 0` there is `A` with
`|h_s(u)| ≤ e^{A S log S} e^{R²u}` for all `S ≥ 2`, `|s| ≤ S`, `u ≥ u₀`.
(Paper: `|h_s(u)| ≤ 2^{O(p)} (1+u)² e^{R²u}` for `u ≥ u₀`.) -/
theorem norm_kernel_le_far {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ u : ℝ, u₀ ≤ u →
      ‖kernel a s u‖ ≤ Real.exp (A * S * Real.log S) * Real.exp (R ^ 2 * u) := by
  obtain ⟨A₀, hA₀0, hA₀⟩ := exists_L5_nonneg
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (ha 0); simpa using this
  set L := max (max (R ^ 2) (R ^ 2)⁻¹) u₀⁻¹ with hL
  have hR2 : 0 < R ^ 2 := by positivity
  have hL1 : 1 ≤ L := by
    refine le_trans ?_ (le_max_left _ _)
    rcases le_total 1 (R ^ 2) with h | h
    · exact h.trans (le_max_left _ _)
    · exact (one_le_inv₀ hR2).2 h |>.trans (le_max_right _ _)
  set E : ℝ → ℝ := fun S => 2 * (C * max 1 R * L ^ (S + 1) *
    Real.exp (A₀ * (S + 1) * Real.log (S + 1))) with hE
  have hEb : SLogBound E := by
    have h1 : SLogBound fun S => L ^ (S + 1) := by
      refine (SLogBound.exp_lin (Real.log L) (Real.log L) 0).of_le fun S _ => le_of_eq ?_
      rw [Real.rpow_def_of_pos (by linarith)]; congr 1; ring
    refine ((((SLogBound.const (2 * (C * max 1 R))).mul h1 fun S _ => by positivity).mul
      (SLogBound.shift hA₀0) fun S _ => (Real.exp_pos _).le)).of_le fun S _ => le_of_eq ?_
    simp only [hE]; ring
  obtain ⟨A, hA⟩ := hEb
  refine ⟨A, fun S hS s hs u hu => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le hu₀ hu
  have hsre : |s.re| ≤ S := (Complex.abs_re_le_norm s).trans hs
  refine (norm_kernel_le_parity hA₀ ha hR.le hS hs hu0 (B := C * max 1 R * L ^ (S + 1) *
    Real.exp (A₀ * (S + 1) * Real.log (S + 1)) * Real.exp (R ^ 2 * u)) fun ε hε => ?_).trans ?_
  · set ρ := (s.re + ε) / 2 - 1 with hρ
    have hεR : (ε : ℝ) ≤ 1 := by exact_mod_cast hε
    have hρT : |ρ| ≤ S + 1 := by
      have := abs_le.1 hsre
      rw [abs_le]; constructor <;> [skip; skip] <;>
        (simp only [hρ]; have : (0 : ℝ) ≤ ε := Nat.cast_nonneg ε; linarith)
    have hRε : R ^ ε ≤ max 1 R := by
      interval_cases ε
      · simp
      · simp
    -- `u^ρ max(1,R²u)^{-ρ} ≤ L^{S+1}`
    have hkey : u ^ ρ * max 1 (R ^ 2 * u) ^ (-ρ) ≤ L ^ (S + 1) := by
      rcases le_or_gt 1 (R ^ 2 * u) with h1 | h1
      · rw [max_eq_right h1, Real.mul_rpow hR2.le hu0.le, Real.rpow_neg hu0.le,
          mul_left_comm, mul_inv_cancel₀ (Real.rpow_pos_of_pos hu0 ρ).ne', mul_one]
        refine rpow_le_of_mem_Icc hR2 hL1 ?_ ?_ (by rwa [abs_neg])
        · calc L⁻¹ ≤ ((R ^ 2)⁻¹)⁻¹ :=
                inv_anti₀ (inv_pos.2 hR2) ((le_max_right _ _).trans (le_max_left _ _))
            _ = R ^ 2 := inv_inv _
        · exact (le_max_left _ _).trans (le_max_left _ _)
      · rw [max_eq_left h1.le, Real.one_rpow, mul_one]
        refine rpow_le_of_mem_Icc hu0 hL1 ?_ ?_ hρT
        · calc L⁻¹ ≤ (u₀⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hu₀) (le_max_right _ _)
            _ = u₀ := inv_inv u₀
            _ ≤ u := hu
        · have : u ≤ (R ^ 2)⁻¹ := by
            rw [inv_eq_one_div, le_div_iff₀ hR2]; linarith [mul_comm (R ^ 2) u]
          exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
    have hex := Real.exp_pos (A₀ * (S + 1) * Real.log (S + 1))
    have hex' := Real.exp_pos (R ^ 2 * u)
    calc C * R ^ ε * u ^ ρ * (Real.exp (A₀ * (S + 1) * Real.log (S + 1)) *
          max 1 (R ^ 2 * u) ^ (-ρ) * Real.exp (R ^ 2 * u))
        = C * R ^ ε * (u ^ ρ * max 1 (R ^ 2 * u) ^ (-ρ)) *
          Real.exp (A₀ * (S + 1) * Real.log (S + 1)) * Real.exp (R ^ 2 * u) := by ring
      _ ≤ C * max 1 R * L ^ (S + 1) *
          Real.exp (A₀ * (S + 1) * Real.log (S + 1)) * Real.exp (R ^ 2 * u) := by
          gcongr
  · have := hA S hS
    simp only [hE] at this
    calc 2 * (C * max 1 R * L ^ (S + 1) * Real.exp (A₀ * (S + 1) * Real.log (S + 1)) *
          Real.exp (R ^ 2 * u))
        = 2 * (C * max 1 R * L ^ (S + 1) * Real.exp (A₀ * (S + 1) * Real.log (S + 1))) *
          Real.exp (R ^ 2 * u) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-- **(L4), far range**, in the plan's (weaker) form with the factor `(1+u)²` of the paper. -/
theorem norm_kernel_le_far' {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ u : ℝ, u₀ ≤ u →
      ‖kernel a s u‖ ≤ Real.exp (A * S * Real.log S) * (1 + u) ^ 2 * Real.exp (R ^ 2 * u) := by
  obtain ⟨A, hA⟩ := norm_kernel_le_far hR ha hu₀
  refine ⟨A, fun S hS s hs u hu => (hA S hS s hs u hu).trans ?_⟩
  have h1 : 1 ≤ (1 + u) ^ 2 := one_le_pow₀ (by linarith)
  have := Real.exp_pos (A * S * Real.log S)
  have := Real.exp_pos (R ^ 2 * u)
  calc Real.exp (A * S * Real.log S) * Real.exp (R ^ 2 * u)
      = Real.exp (A * S * Real.log S) * 1 * Real.exp (R ^ 2 * u) := by ring
    _ ≤ _ := by gcongr

/-- **(L4), near range.** For `|a_n| ≤ C R^n` and `u₀ > 0` there is `A` with
`|h_s(u)| ≤ e^{A S log S} u^{-S/2-1}` for all `S ≥ 2`, `|s| ≤ S`, `0 < u ≤ u₀`. -/
theorem norm_kernel_le_near {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ u : ℝ, 0 < u → u ≤ u₀ →
      ‖kernel a s u‖ ≤ Real.exp (A * S * Real.log S) * u ^ (-(S / 2) - 1) := by
  obtain ⟨A₀, hA₀0, hA₀⟩ := exists_L5_nonneg
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (ha 0); simpa using this
  set M := max 1 (R ^ 2 * u₀) with hM
  set P := max 1 u₀ with hP
  have hM1 : 1 ≤ M := le_max_left _ _
  have hP1 : 1 ≤ P := le_max_left _ _
  set E : ℝ → ℝ := fun S => 2 * (C * max 1 R * P ^ (S + 1) * M ^ (S + 1) *
    Real.exp (A₀ * (S + 1) * Real.log (S + 1)) * Real.exp (R ^ 2 * u₀)) with hE
  have hEb : SLogBound E := by
    have hpow : ∀ L : ℝ, 1 ≤ L → SLogBound fun S => L ^ (S + 1) := fun L hL =>
      (SLogBound.exp_lin (Real.log L) (Real.log L) 0).of_le fun S _ => le_of_eq (by
        rw [Real.rpow_def_of_pos (by linarith)]; congr 1; ring)
    refine (((((SLogBound.const (2 * (C * max 1 R) * Real.exp (R ^ 2 * u₀))).mul (hpow P hP1)
      fun S _ => by positivity).mul (hpow M hM1) fun S _ => by positivity).mul
      (SLogBound.shift hA₀0) fun S _ => (Real.exp_pos _).le)).of_le fun S _ => le_of_eq ?_
    simp only [hE]; ring
  obtain ⟨A, hA⟩ := hEb
  refine ⟨A, fun S hS s hs u hu hu' => ?_⟩
  have hsre : |s.re| ≤ S := (Complex.abs_re_le_norm s).trans hs
  have hupos : 0 < u ^ (-(S / 2) - 1) := Real.rpow_pos_of_pos hu _
  refine (norm_kernel_le_parity hA₀ ha hR.le hS hs hu (B := C * max 1 R * P ^ (S + 1) *
    M ^ (S + 1) * Real.exp (A₀ * (S + 1) * Real.log (S + 1)) * Real.exp (R ^ 2 * u₀) *
      u ^ (-(S / 2) - 1)) fun ε hε => ?_).trans ?_
  · set ρ := (s.re + ε) / 2 - 1 with hρ
    have hεR : (ε : ℝ) ≤ 1 := by exact_mod_cast hε
    have hε0 : (0 : ℝ) ≤ ε := Nat.cast_nonneg ε
    have hsre' := abs_le.1 hsre
    have hρT : |ρ| ≤ S + 1 := by
      rw [abs_le]; constructor <;> (simp only [hρ]; linarith)
    have hRε : R ^ ε ≤ max 1 R := by
      interval_cases ε
      · simp
      · simp
    -- `u^ρ ≤ P^{S+1} u^{-S/2-1}`
    have hu1 : u ^ ρ ≤ P ^ (S + 1) * u ^ (-(S / 2) - 1) := by
      have he0 : 0 ≤ ρ + S / 2 + 1 := by simp only [hρ]; linarith
      have he1 : ρ + S / 2 + 1 ≤ S + 1 := by simp only [hρ]; linarith
      have : u ^ ρ = u ^ (ρ + S / 2 + 1) * u ^ (-(S / 2) - 1) := by
        rw [← Real.rpow_add hu]; congr 1; ring
      rw [this]
      gcongr
      calc u ^ (ρ + S / 2 + 1) ≤ u₀ ^ (ρ + S / 2 + 1) := Real.rpow_le_rpow hu.le hu' he0
        _ ≤ P ^ (ρ + S / 2 + 1) := Real.rpow_le_rpow hu₀.le (le_max_right _ _) he0
        _ ≤ P ^ (S + 1) := Real.rpow_le_rpow_of_exponent_le hP1 he1
    have hu2 : max 1 (R ^ 2 * u) ^ (-ρ) ≤ M ^ (S + 1) := by
      refine rpow_le_of_mem_Icc (lt_of_lt_of_le one_pos (le_max_left _ _)) hM1 ?_ ?_
        (by rwa [abs_neg])
      · exact (inv_le_one_of_one_le₀ hM1).trans (le_max_left _ _)
      · exact max_le_max le_rfl (by gcongr)
    have hu3 : Real.exp (R ^ 2 * u) ≤ Real.exp (R ^ 2 * u₀) := by gcongr
    have hex := Real.exp_pos (A₀ * (S + 1) * Real.log (S + 1))
    have hm0 : 0 ≤ max 1 (R ^ 2 * u) ^ (-ρ) :=
      Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
    calc C * R ^ ε * u ^ ρ * (Real.exp (A₀ * (S + 1) * Real.log (S + 1)) *
          max 1 (R ^ 2 * u) ^ (-ρ) * Real.exp (R ^ 2 * u))
        ≤ C * max 1 R * (P ^ (S + 1) * u ^ (-(S / 2) - 1)) *
          (Real.exp (A₀ * (S + 1) * Real.log (S + 1)) * M ^ (S + 1) * Real.exp (R ^ 2 * u₀)) := by
          gcongr
      _ = _ := by ring
  · have := hA S hS
    simp only [hE] at this
    calc 2 * (C * max 1 R * P ^ (S + 1) * M ^ (S + 1) *
          Real.exp (A₀ * (S + 1) * Real.log (S + 1)) * Real.exp (R ^ 2 * u₀) * u ^ (-(S / 2) - 1))
        = 2 * (C * max 1 R * P ^ (S + 1) * M ^ (S + 1) *
          Real.exp (A₀ * (S + 1) * Real.log (S + 1)) * Real.exp (R ^ 2 * u₀)) *
            u ^ (-(S / 2) - 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hupos.le

/-! ### (L4): `k`-terms and dual terms -/

/-- **(L4), `k`-terms.** For `k ≥ k₀ > R`: `|I_k(s)| ≤ e^{A S log S} e^{-(k²-R²)u₀}`, uniformly
in `|s| ≤ S`, `S ≥ 2`, where `I_k(s) = ∫_{u₀}^∞ e^{-k²u} h_s(u) du` (`kTerm`, entire in `s`). -/
theorem norm_kTerm_le_uniform {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n)
    {u₀ : ℝ} (hu₀ : 0 < u₀) {k₀ : ℕ} (hk₀ : R < k₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ k : ℕ, k₀ ≤ k →
      ‖kTerm (kernel a s) u₀ k‖ ≤
        Real.exp (A * S * Real.log S) * Real.exp (-(((k : ℝ) ^ 2 - R ^ 2) * u₀)) := by
  obtain ⟨A₁, hA₁⟩ := norm_kernel_le_far hR ha hu₀
  set δ := (k₀ : ℝ) ^ 2 - R ^ 2 with hδ
  have hδ0 : 0 < δ := by
    have : R ^ 2 < (k₀ : ℝ) ^ 2 := by gcongr
    linarith
  obtain ⟨A, hA⟩ := (SLogBound.const δ⁻¹).mul
    (show SLogBound fun S => Real.exp (A₁ * S * Real.log S) from ⟨A₁, fun _ _ => le_rfl⟩)
    fun _ _ => (Real.exp_pos _).le
  refine ⟨A, fun S hS s hs k hk => ?_⟩
  set c := (k : ℝ) ^ 2 - R ^ 2 with hc
  have hcδ : δ ≤ c := by
    have : (k₀ : ℝ) ≤ k := Nat.cast_le.2 hk
    have : (k₀ : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by gcongr
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le hδ0 hcδ
  set E := Real.exp (A₁ * S * Real.log S) with hE
  set g : ℝ → ℝ := fun u => E * Real.exp (-c * u) with hg
  have hgi : IntegrableOn g (Ioi u₀) :=
    (integrableOn_exp_mul_Ioi (by linarith : -c < 0) u₀).const_mul _
  have hbound : ∀ u ∈ Ioi u₀, ‖(Real.exp (-((k : ℝ) ^ 2 * u)) : ℂ) * kernel a s u‖ ≤ g u := by
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-((k : ℝ) ^ 2 * u)) * ‖kernel a s u‖
        ≤ Real.exp (-((k : ℝ) ^ 2 * u)) * (E * Real.exp (R ^ 2 * u)) :=
          mul_le_mul_of_nonneg_left (hA₁ S hS s hs u (le_of_lt hu)) (Real.exp_pos _).le
      _ = g u := by
          simp only [hg]; rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hint : ‖kTerm (kernel a s) u₀ k‖ ≤ E * Real.exp (-c * u₀) / c := by
    unfold kTerm
    refine (norm_integral_le_of_norm_le hgi
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbound))).trans (le_of_eq ?_)
    simp only [hg]
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) u₀, neg_div_neg_eq, mul_div_assoc]
  refine hint.trans ?_
  have h1 : E * Real.exp (-c * u₀) / c ≤ δ⁻¹ * E * Real.exp (-c * u₀) := by
    rw [div_eq_mul_inv, mul_comm _ c⁻¹, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (inv_anti₀ hδ0 hcδ)
      (Real.exp_pos _).le) (Real.exp_pos _).le
  refine h1.trans ?_
  rw [neg_mul]
  exact mul_le_mul_of_nonneg_right (hA S hS) (Real.exp_pos _).le

/-- **(L4), dual terms.** For `m ≥ 1`: `|J_m(s)| ≤ e^{A S log S} e^{-π²m²/(2u₀)}`, uniformly in
`|s| ≤ S`, `S ≥ 2` — for every such `s`, including `Re s ≤ 1`.  Here
`J_m(s) = ∫₀^{u₀} u^{-1/2} e^{-π²m²/u} h_s(u) du` (`dualTerm`, entire in `s`).  As in the paper:
`e^{-π²m²/u} ≤ e^{-π²m²/(2u₀)} e^{-1/u}` and `u^{-(S+3)/2} e^{-1/u} ≤ 1 + ⌈(S+3)/2⌉!`. -/
theorem norm_dualTerm_le_uniform {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R)
    (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ m : ℕ, 1 ≤ m →
      ‖dualTerm (kernel a s) u₀ m‖ ≤
        Real.exp (A * S * Real.log S) * Real.exp (-(π ^ 2 * (m : ℝ) ^ 2 / (2 * u₀))) := by
  obtain ⟨A₂, hA₂⟩ := norm_kernel_le_near hR ha hu₀
  obtain ⟨A, hA⟩ := ((SLogBound.const u₀).mul
    ((show SLogBound fun S => Real.exp (A₂ * S * Real.log S) from ⟨A₂, fun _ _ => le_rfl⟩).mul
      ((SLogBound.const 1).add (SLogBound.factorial_ceil (α := 1 / 2) (β := 3 / 2)
        (by norm_num) (by norm_num))) fun _ _ => by positivity)
    fun _ _ => by positivity)
  refine ⟨A, fun S hS s hs m hm => ?_⟩
  set α := 1 / 2 * S + 3 / 2 with hα
  have hα0 : 0 ≤ α := by linarith
  set E := Real.exp (A₂ * S * Real.log S) with hE
  set F := 1 + ((⌈α⌉₊).factorial : ℝ) with hF
  set X := π ^ 2 * (m : ℝ) ^ 2 with hX
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hX2 : 2 ≤ X := by
    have : 1 ≤ (m : ℝ) ^ 2 := one_le_pow₀ hm1
    have : 2 ≤ π := Real.two_le_pi
    nlinarith
  have hbound : ∀ u ∈ Ioc 0 u₀,
      ‖(((u ^ (-(1 / 2 : ℝ)) * Real.exp (-(π ^ 2 * (m : ℝ) ^ 2 / u)) : ℝ)) : ℂ) * kernel a s u‖ ≤
        E * F * Real.exp (-(X / (2 * u₀))) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hk := hA₂ S hS s hs u hu0 hu.2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← hX]
    -- `e^{-X/u} ≤ e^{-X/(2u₀)} e^{-1/u}`
    have hexp : Real.exp (-(X / u)) ≤ Real.exp (-(X / (2 * u₀))) * Real.exp (-u⁻¹) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : (X - 1) / u₀ ≤ (X - 1) / u :=
        div_le_div_of_nonneg_left (by linarith) hu0 hu.2
      have h2 : X / (2 * u₀) ≤ (X - 1) / u₀ := by
        rw [div_le_div_iff₀ (by positivity) hu₀]; nlinarith
      have h3 : X / u = (X - 1) / u + u⁻¹ := by field_simp; ring
      linarith
    -- `u^{-1/2} u^{-S/2-1} = (1/u)^α`
    have hpow : u ^ (-(1 / 2 : ℝ)) * u ^ (-(S / 2) - 1) = (u⁻¹) ^ α := by
      rw [← Real.rpow_add hu0, Real.inv_rpow hu0.le, ← Real.rpow_neg hu0.le]; congr 1; ring
    have hmain := rpow_mul_exp_neg_le (inv_pos.2 hu0) hα0
    calc u ^ (-(1 / 2 : ℝ)) * Real.exp (-(X / u)) * ‖kernel a s u‖
        ≤ u ^ (-(1 / 2 : ℝ)) * (Real.exp (-(X / (2 * u₀))) * Real.exp (-u⁻¹)) *
          (E * u ^ (-(S / 2) - 1)) := by gcongr
      _ = E * ((u⁻¹) ^ α * Real.exp (-u⁻¹)) * Real.exp (-(X / (2 * u₀))) := by
          rw [← hpow]; ring
      _ ≤ E * F * Real.exp (-(X / (2 * u₀))) := by gcongr
  have hint := norm_setIntegral_le_of_norm_le_const
    (measure_Ioc_lt_top (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := u₀)) hbound
  rw [Real.volume_real_Ioc_of_le hu₀.le, sub_zero] at hint
  unfold dualTerm
  refine hint.trans ?_
  have := hA S hS
  calc E * F * Real.exp (-(X / (2 * u₀))) * u₀
      = (u₀ * (E * (1 + ((⌈1 / 2 * S + 3 / 2⌉₊).factorial : ℝ)))) *
          Real.exp (-(X / (2 * u₀))) := by rw [hF, hα]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

end ZetaF.AppA
