/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Exact recovery of `B_n(b/f)` (Appendix A, lemma L7; proof of Corollary 5.5)

Corollary 5.5 computes the rational number `B_n(x)`, `x = b/f`, from a numerical approximation of
`L(1-n, 1_{b+fℤ})` (`ZetaF.Bernoulli.bernoulli_eq_LFunction`). This file supplies the arithmetic:

* **denominator**: `D = f^n · (n+1)#` clears the denominator of `B_n(b/f)` (`isInt_den_mul_bernoulli_eval`),
  by the von Staudt–Clausen theorem (`(n+1)# ≤ 4^{n+1}`, `primorial_le_4_pow`);
* **size**: `|B_n(x)| ≤ 4e · n!` on `[0, 1]` (`abs_bernoulli_eval_le`), from `|B_j| ≤ 4 j!`
  (`ζ(2k) ≤ ζ(2)` and Euler's formula `hasSum_zeta_nat`);
* **rounding**: a real `y` with `|y - B_n(x)| < 1/(2D)` determines `B_n(x) = round(D y)/D`
  (`eq_round_div_of_approx`).

So `log₂ n! + n log₂ f + O(n)` bits of `L(1-n, ·)` suffice.
-/
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

open Finset Real
open scoped Nat

namespace ZetaF.AppA

/-- `q` is an integer. -/
def IsIntQ (q : ℚ) : Prop := ∃ z : ℤ, q = z

lemma IsIntQ.add {a b : ℚ} (ha : IsIntQ a) (hb : IsIntQ b) : IsIntQ (a + b) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x + y, by push_cast; ring⟩

lemma IsIntQ.mul {a b : ℚ} (ha : IsIntQ a) (hb : IsIntQ b) : IsIntQ (a * b) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x * y, by push_cast; ring⟩

lemma IsIntQ.sub {a b : ℚ} (ha : IsIntQ a) (hb : IsIntQ b) : IsIntQ (a - b) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x - y, by push_cast; ring⟩

lemma isIntQ_natCast (n : ℕ) : IsIntQ n := ⟨n, by push_cast; rfl⟩

lemma isIntQ_sum {ι : Type*} (s : Finset ι) {f : ι → ℚ} (h : ∀ i ∈ s, IsIntQ (f i)) :
    IsIntQ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

lemma prime_dvd_primorial {p N : ℕ} (hp : p.Prime) (hpN : p ≤ N) : p ∣ primorial N :=
  dvd_prod_of_mem _ (mem_filter.2 ⟨mem_range.2 (by omega), hp⟩)

lemma isIntQ_primorial_div {p N : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    IsIntQ ((primorial N : ℚ) * (1 / p)) := by
  obtain ⟨m, hm⟩ := prime_dvd_primorial hp hpN
  refine ⟨m, ?_⟩
  rw [hm]; push_cast
  have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp

/-- **`N# · B_i` is an integer for `i < N`** (von Staudt–Clausen). -/
theorem isIntQ_primorial_mul_bernoulli {N i : ℕ} (hi : i + 1 ≤ N) :
    IsIntQ ((primorial N : ℚ) * bernoulli i) := by
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | hodd
  · -- `i = 2k`
    rw [show i = 2 * k by omega]
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    have hB : bernoulli (2 * k) = z - ∑ p ∈ range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k,
        (1 : ℚ) / p := by rw [hz]; ring
    rw [hB, mul_sub, Finset.mul_sum]
    have h1 : IsIntQ ((primorial N : ℚ) * z) := ⟨primorial N * z, by push_cast; ring⟩
    refine h1.sub (isIntQ_sum _ fun p hp => ?_)
    simp only [mem_filter, mem_range] at hp
    exact isIntQ_primorial_div hp.2.1 (by omega)
  · rcases Nat.lt_or_ge 1 i with h1 | h1
    · rw [bernoulli_eq_zero_of_odd hodd h1, mul_zero]; exact ⟨0, by simp⟩
    · -- `i = 1`, `B₁ = -1/2`, and `2 ∣ N#` since `N ≥ 2`
      obtain rfl : i = 1 := by obtain ⟨m, hm⟩ := hodd; omega
      rw [bernoulli_one]
      obtain ⟨z, hz⟩ := isIntQ_primorial_div (N := N) Nat.prime_two (by omega)
      refine ⟨-z, ?_⟩
      push_cast at hz ⊢
      linarith

/-- **Denominator of `B_n(b/f)`**: `f^n (n+1)# B_n(b/f)` is an integer. -/
theorem isInt_den_mul_bernoulli_eval (n b f : ℕ) (hf : 0 < f) :
    IsIntQ (((f : ℚ) ^ n * primorial (n + 1)) * (Polynomial.bernoulli n).eval ((b : ℚ) / f)) := by
  rw [Polynomial.bernoulli_def, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine isIntQ_sum _ fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [Polynomial.eval_monomial]
  have hf0 : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  have e : (f : ℚ) ^ n * primorial (n + 1) * (bernoulli (n - i) * (n.choose i) * ((b : ℚ) / f) ^ i) =
      ((primorial (n + 1) : ℚ) * bernoulli (n - i)) * ((n.choose i : ℚ) * (b : ℚ) ^ i * (f : ℚ) ^ (n - i)) := by
    rw [div_pow]
    have : (f : ℚ) ^ n = (f : ℚ) ^ i * (f : ℚ) ^ (n - i) := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  rw [e]
  refine (isIntQ_primorial_mul_bernoulli (by omega)).mul ⟨n.choose i * b ^ i * f ^ (n - i), ?_⟩
  push_cast; ring

/-- `|B_j| ≤ 4 · j!`. -/
theorem abs_bernoulli_le (j : ℕ) : |(bernoulli j : ℝ)| ≤ 4 * j ! := by
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | hodd
  · rw [show j = 2 * k by omega]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    have hS := hasSum_zeta_nat (k := k) hk0.ne'
    have hle : ∀ n : ℕ, 1 / (n : ℝ) ^ (2 * k) ≤ 1 / (n : ℝ) ^ 2 := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [zero_pow (by omega : 2 * k ≠ 0)]
      · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 (by omega))
    have hZ : (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)! ≤
        π ^ 2 / 6 := hasSum_le hle hS hasSum_zeta_two
    have hpi : π ^ 2 / 6 ≤ 2 := by nlinarith [pi_lt_d2, pi_pos]
    have hf : (0 : ℝ) < ((2 * k)! : ℝ) := by positivity
    have hP : (1 : ℝ) ≤ 2 ^ (2 * k - 1) * π ^ (2 * k) := by
      have h1 : (1 : ℝ) ≤ 2 ^ (2 * k - 1) := one_le_pow₀ (by norm_num)
      have h2 : (1 : ℝ) ≤ π ^ (2 * k) := one_le_pow₀ (by linarith [pi_gt_three])
      nlinarith
    -- the sum is positive, so it equals its absolute value
    have hS0 : 0 ≤ (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)! :=
      hS.nonneg fun n => by positivity
    have habs : |(bernoulli (2 * k) : ℝ)| * (2 ^ (2 * k - 1) * π ^ (2 * k)) / (2 * k)! ≤ 2 := by
      have e : |(bernoulli (2 * k) : ℝ)| * (2 ^ (2 * k - 1) * π ^ (2 * k)) / (2 * k)! =
          |(-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / (2 * k)!| := by
        rw [abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (2 * k - 1)),
          abs_of_pos (by positivity : (0 : ℝ) < π ^ (2 * k)), abs_of_pos hf]
        ring
      rw [e, abs_of_nonneg hS0]; linarith
    rw [div_le_iff₀ hf] at habs
    nlinarith [abs_nonneg (bernoulli (2 * k) : ℝ)]
  · rcases Nat.lt_or_ge 1 j with h1 | h1
    · rw [bernoulli_eq_zero_of_odd hodd h1]; simp
    · obtain rfl : j = 1 := by obtain ⟨m, hm⟩ := hodd; omega
      rw [bernoulli_one]; norm_num [abs_of_pos]

/-- **`|B_n(x)| ≤ 4e · n!` on `[0, 1]`.** -/
theorem abs_bernoulli_eval_le (n : ℕ) {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(((Polynomial.bernoulli n).eval x : ℚ) : ℝ)| ≤ 4 * Real.exp 1 * n ! := by
  rw [Polynomial.bernoulli_def, Polynomial.eval_finsetSum]
  push_cast
  have hx0' : (0 : ℝ) ≤ x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) ≤ 1 := by exact_mod_cast hx1
  have hterm : ∀ i ∈ range (n + 1), |((Polynomial.eval (x : ℚ) (Polynomial.monomial i
      (bernoulli (n - i) * (n.choose i : ℚ))) : ℚ) : ℝ)| ≤ 4 * (n ! : ℝ) * (1 / (i ! : ℝ)) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [Polynomial.eval_monomial]; push_cast
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hx0', Nat.abs_cast]
    have hB := abs_bernoulli_le (n - i)
    have hxi : (x : ℝ) ^ i ≤ 1 := pow_le_one₀ hx0' hx1'
    have hch : ((n.choose i : ℕ) : ℝ) * ((n - i)! : ℝ) = (n ! : ℝ) / (i ! : ℝ) := by
      rw [eq_div_iff (by positivity)]
      have := Nat.choose_mul_factorial_mul_factorial hin
      exact_mod_cast (by rw [← this]; ring)
    calc |(bernoulli (n - i) : ℝ)| * ((n.choose i : ℕ) : ℝ) * (x : ℝ) ^ i
        ≤ (4 * ((n - i)! : ℝ)) * ((n.choose i : ℕ) : ℝ) * 1 := by gcongr
      _ = 4 * (n ! : ℝ) * (1 / (i ! : ℝ)) := by
        rw [mul_one, show (4 * ((n - i)! : ℝ)) * ((n.choose i : ℕ) : ℝ) =
          4 * (((n.choose i : ℕ) : ℝ) * ((n - i)! : ℝ)) by ring, hch]
        ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have he : ∑ i ∈ range (n + 1), 1 / (i ! : ℝ) ≤ Real.exp 1 := by
    have := Real.sum_le_exp_of_nonneg (x := 1) zero_le_one (n + 1)
    simpa using this
  have h4 : (0 : ℝ) ≤ 4 * (n ! : ℝ) := by positivity
  calc 4 * (n ! : ℝ) * ∑ i ∈ range (n + 1), 1 / (i ! : ℝ) ≤ 4 * (n ! : ℝ) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left he h4
    _ = _ := by ring

/-- **Rounding**: if `D q` is an integer and `|y - q| < 1/(2D)` then `q = round(D y)/D`. -/
theorem eq_round_div_of_approx {q : ℚ} {D : ℕ} (hD : 0 < D) (hq : IsIntQ ((D : ℚ) * q))
    {y : ℝ} (hy : |y - q| < 1 / (2 * D)) : q = (round ((D : ℝ) * y) : ℚ) / D := by
  obtain ⟨z, hz⟩ := hq
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hDq : ((D : ℚ) * q : ℚ) = (z : ℚ) := hz
  have hzR : (D : ℝ) * (q : ℝ) = z := by exact_mod_cast hDq
  have hclose : |(D : ℝ) * y - z| < 1 / 2 := by
    rw [← hzR, ← mul_sub, abs_mul, abs_of_pos hD']
    calc (D : ℝ) * |y - q| < D * (1 / (2 * D)) := mul_lt_mul_of_pos_left hy hD'
      _ = 1 / 2 := by field_simp
  have hround : round ((D : ℝ) * y) = z := by
    rw [round_eq, Int.floor_eq_iff]
    rw [abs_lt] at hclose
    constructor <;> linarith [hclose.1, hclose.2]
  rw [hround, ← hDq]
  have : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp

/-- **Corollary 5.5, the arithmetic step**: with `D = f^n (n+1)#`, any real `y` with
`|y - B_n(b/f)| < 1/(2D)` gives `B_n(b/f) = round(D y)/D`. -/
theorem bernoulli_eval_eq_round {n b f : ℕ} (hf : 0 < f) {y : ℝ}
    (hy : |y - (((Polynomial.bernoulli n).eval ((b : ℚ) / f) : ℚ) : ℝ)| <
      1 / (2 * ((f ^ n * primorial (n + 1) : ℕ) : ℝ))) :
    (Polynomial.bernoulli n).eval ((b : ℚ) / f) =
      (round (((f ^ n * primorial (n + 1) : ℕ) : ℝ) * y) : ℚ) / ((f ^ n * primorial (n + 1) : ℕ) : ℚ) := by
  have hD : 0 < f ^ n * primorial (n + 1) :=
    Nat.mul_pos (pow_pos hf n) (prod_pos fun p hp => (mem_filter.1 hp).2.pos)
  refine eq_round_div_of_approx hD ?_ hy
  have := isInt_den_mul_bernoulli_eval n b f hf
  push_cast; exact this

end ZetaF.AppA
