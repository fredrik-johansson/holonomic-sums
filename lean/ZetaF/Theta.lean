/-
# The theta transformation in the form used by the splitting

`Θ(u) = ∑_{k ≥ 1} e^{-k²u} = ½√(π/u) - ½ + √(π/u) ∑_{m ≥ 1} e^{-π²m²/u}`  (paper, §3, proof of Thm 3.2).
-/
import ZetaF.Deps

open Real Finset

namespace ZetaF

lemma summable_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => rexp (-(c * (n : ℝ) ^ 2)) := by
  have hg : Summable fun n : ℕ => rexp (-c * n) := by
    simpa using summable_pow_mul_exp_neg_nat_mul 0 hc
  refine Summable.of_nonneg_of_le (fun _ => (exp_pos _).le) (fun n => ?_) hg
  rw [exp_le_exp]
  have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  nlinarith

lemma summable_exp_neg_mul_sq_succ {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => rexp (-(c * ((n : ℝ) + 1) ^ 2)) := by
  have := (summable_nat_add_iff 1).2 (summable_exp_neg_mul_sq hc)
  simpa using this

lemma summable_int_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => rexp (-(c * (n : ℝ) ^ 2)) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa using summable_exp_neg_mul_sq hc
  · refine (summable_exp_neg_mul_sq_succ hc).congr fun n => ?_
    push_cast; ring_nf

/-- For an even summable `f : ℤ → ℝ`, `∑_{n ∈ ℤ} f n = f 0 + 2 ∑_{n ≥ 1} f n`. -/
lemma tsum_int_of_even {f : ℤ → ℝ} (hf : Summable f) (he : ∀ n, f (-n) = f n) :
    ∑' n : ℤ, f n = f 0 + 2 * ∑' n : ℕ, f ((n : ℤ) + 1) := by
  have h1 : Summable fun n : ℕ => f n := hf.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ => f (-((n : ℤ) + 1)) :=
    hf.comp_injective (fun a b h => by simpa using h)
  rw [tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_eq_zero_add]
  simp only [he]
  push_cast
  ring

/-- `Θ(u) = ∑_{k ≥ 1} e^{-k² u}`. -/
noncomputable def theta1 (u : ℝ) : ℝ := ∑' k : ℕ, rexp (-(((k : ℝ) + 1) ^ 2 * u))

/-- The dual series `∑_{m ≥ 1} e^{-π² m²/u}`. -/
noncomputable def thetaDual (u : ℝ) : ℝ := ∑' m : ℕ, rexp (-(π ^ 2 * ((m : ℝ) + 1) ^ 2 / u))

lemma summable_theta1 {u : ℝ} (hu : 0 < u) :
    Summable fun k : ℕ => rexp (-(((k : ℝ) + 1) ^ 2 * u)) :=
  (summable_exp_neg_mul_sq_succ hu).congr fun k => by ring_nf

lemma summable_thetaDual {u : ℝ} (hu : 0 < u) :
    Summable fun m : ℕ => rexp (-(π ^ 2 * ((m : ℝ) + 1) ^ 2 / u)) :=
  (summable_exp_neg_mul_sq_succ (c := π ^ 2 / u) (by positivity)).congr fun k => by ring_nf

/-- **Theta transformation**: `Θ(u) = ½√(π/u) - ½ + √(π/u) ∑_{m ≥ 1} e^{-π²m²/u}`. -/
theorem theta1_eq {u : ℝ} (hu : 0 < u) :
    theta1 u = 1 / 2 * √(π / u) - 1 / 2 + √(π / u) * thetaDual u := by
  have hπ := pi_pos
  have key := Real.tsum_exp_neg_mul_int_sq (a := u / π) (by positivity)
  have e1 : ∀ n : ℤ, rexp (-π * (u / π) * (n : ℝ) ^ 2) = rexp (-(u * (n : ℝ) ^ 2)) := by
    intro n; congr 1; field_simp
  have e2 : ∀ n : ℤ, rexp (-π / (u / π) * (n : ℝ) ^ 2) = rexp (-(π ^ 2 / u * (n : ℝ) ^ 2)) := by
    intro n; congr 1; field_simp
  simp only [e1, e2] at key
  rw [tsum_int_of_even (summable_int_exp_neg_mul_sq hu) (fun n => by simp),
    tsum_int_of_even (summable_int_exp_neg_mul_sq (c := π ^ 2 / u) (by positivity))
      (fun n => by simp)] at key
  have hs : (1 : ℝ) / (u / π) ^ (1 / 2 : ℝ) = √(π / u) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ hπ.le, Real.sqrt_div' _ hu.le,
      one_div_div]
  rw [hs] at key
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    neg_zero, exp_zero, Int.cast_add, Int.cast_natCast, Int.cast_one] at key
  have h1 : theta1 u = ∑' n : ℕ, rexp (-(u * ((n : ℝ) + 1) ^ 2)) :=
    tsum_congr fun n => by ring_nf
  have h2 : thetaDual u = ∑' n : ℕ, rexp (-(π ^ 2 / u * ((n : ℝ) + 1) ^ 2)) :=
    tsum_congr fun n => by ring_nf
  rw [h1, h2]
  linarith

lemma theta1_nonneg (u : ℝ) : 0 ≤ theta1 u :=
  tsum_nonneg fun _ => (exp_pos _).le

lemma thetaDual_nonneg (u : ℝ) : 0 ≤ thetaDual u :=
  tsum_nonneg fun _ => (exp_pos _).le

/-- `thetaDual` is nonincreasing in `1/u`: for `0 < u ≤ u₀`, `thetaDual u ≤ thetaDual u₀`. -/
lemma thetaDual_le {u u₀ : ℝ} (hu : 0 < u) (huu₀ : u ≤ u₀) : thetaDual u ≤ thetaDual u₀ := by
  apply Summable.tsum_le_tsum _ (summable_thetaDual hu) (summable_thetaDual (hu.trans_le huu₀))
  intro m
  rw [exp_le_exp, neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (by positivity) hu huu₀

/-- `Θ(u) ≤ C/√u` on `(0, u₀]`. -/
lemma theta1_le {u u₀ : ℝ} (hu : 0 < u) (huu₀ : u ≤ u₀) :
    theta1 u ≤ (1 / 2 + thetaDual u₀) * √π / √u := by
  rw [theta1_eq hu, Real.sqrt_div' _ hu.le]
  have := thetaDual_le hu huu₀
  have hsu : 0 < √u := Real.sqrt_pos.2 hu
  have : 0 ≤ √π / √u := by positivity
  calc 1 / 2 * (√π / √u) - 1 / 2 + √π / √u * thetaDual u
      ≤ 1 / 2 * (√π / √u) + √π / √u * thetaDual u₀ := by nlinarith
    _ = (1 / 2 + thetaDual u₀) * √π / √u := by ring

end ZetaF
