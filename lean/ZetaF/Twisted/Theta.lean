/-
# Theta transformation with a periodic weight (Remark 3.7, `δ = 0`)

For `χ` of period `q`, `θ_χ(u) = ∑_{k ∈ ℤ} χ(k) e^{-k²u} = (1/q)√(π/u) ∑_{n ∈ ℤ} χ̂(n) e^{-π²n²/(q²u)}`
with the Gauss sums `χ̂(n) = ∑_{a=0}^{q-1} χ(a) e^{2πian/q}`; for even `χ` also `χ̂` is even.
-/
import ZetaF.Theta

open Real Complex Finset

namespace ZetaF

/-- Poisson summation over the residue class `a + qℤ`:
`∑_j e^{-(a+qj)²u} = (1/q)√(π/u) ∑_n e^{2πina/q} e^{-π²n²/(q²u)}`. -/
theorem tsum_exp_shifted_sq {q : ℕ} (hq : 0 < q) (a : ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' j : ℤ, (rexp (-((a + q * j) ^ 2 * u)) : ℂ) =
      (1 / q * √(π / u) : ℝ) * ∑' n : ℤ, cexp (2 * π * I * n * a / q) *
        (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
  have hπ := Real.pi_pos
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set A : ℂ := ((q ^ 2 * u / π : ℝ) : ℂ) with hA
  set B : ℂ := ((-(a * q * u / π) : ℝ) : ℂ) with hB
  have hAre : 0 < A.re := by rw [hA, Complex.ofReal_re]; positivity
  have key := Complex.tsum_exp_neg_quadratic hAre B
  have hE : cexp ((a ^ 2 * u : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  -- left-hand side
  have hL : ∀ j : ℤ, cexp (-π * A * j ^ 2 + 2 * π * B * j) =
      cexp ((a ^ 2 * u : ℝ) : ℂ) * (rexp (-((a + q * j) ^ 2 * u)) : ℂ) := by
    intro j
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hA, hB]; push_cast; field_simp; ring
  -- right-hand side
  have hR : ∀ n : ℤ, cexp (-π / A * (n + I * B) ^ 2) =
      cexp ((a ^ 2 * u : ℝ) : ℂ) * (cexp (2 * π * I * n * a / q) *
        (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ)) := by
    intro n
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hA, hB]; push_cast
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hπ.ne'
    have : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
    have : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
    field_simp
    ring_nf
    rw [Complex.I_sq]; ring
  have hsq : (1 : ℂ) / A ^ (1 / 2 : ℂ) = ((1 / q * √(π / u) : ℝ) : ℂ) := by
    rw [hA, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]
    rw [Real.sqrt_div' _ hπ.le, Real.sqrt_mul' _ hu.le, Real.sqrt_sq hq'.le,
      Real.sqrt_div' _ hu.le]
    push_cast
    have : (√π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hπ).ne'
    have : (√u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
    have : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
    field_simp
  simp only [hL, hR, tsum_mul_left, hsq] at key
  rw [mul_left_comm] at key
  exact mul_left_cancel₀ hE key

/-- Gauss sums `χ̂(n) = ∑_{a=0}^{q-1} χ(a) e^{2πian/q}`. -/
noncomputable def gaussSum (q : ℕ) (χ : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑ a ∈ range q, χ a * cexp (2 * π * I * n * (a : ℝ) / q)

lemma periodic_bound {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q) (k : ℤ) :
    ‖χ k‖ ≤ ∑ a ∈ range q, ‖χ a‖ := by
  have hk : χ k = χ ((k % q).toNat) := by
    have h0 : 0 ≤ k % q := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    rw [Int.toNat_of_nonneg h0]
    conv_lhs => rw [← Int.ediv_mul_add_emod k q]
    rw [add_comm]
    exact hper.int_mul (k / q) (k % q)
  rw [hk]
  apply single_le_sum (f := fun a : ℕ => ‖χ a‖) (fun _ _ => norm_nonneg _)
  rw [mem_range]
  have := Int.emod_lt_of_pos k (by exact_mod_cast hq : (0 : ℤ) < q)
  have h0 : 0 ≤ k % q := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  omega

/-- **Theta transformation with a periodic weight**:
`∑_{k∈ℤ} χ(k) e^{-k²u} = (1/q)√(π/u) ∑_{n∈ℤ} χ̂(n) e^{-π²n²/(q²u)}`. -/
theorem tsum_char_theta {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    {u : ℝ} (hu : 0 < u) :
    ∑' k : ℤ, χ k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) =
      (1 / q * √(π / u) : ℝ) * ∑' n : ℤ, gaussSum q χ n *
        (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
  have : NeZero q := ⟨hq.ne'⟩
  set f : ℤ → ℂ := fun k => χ k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded ((summable_int_exp_neg_mul_sq hu).mul_left
      (∑ a ∈ range q, ‖χ a‖)) fun k => ?_
    rw [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_right (periodic_bound hq hper k) (Real.exp_pos _).le).trans
      (le_of_eq (by ring_nf))
  set e : Fin q × ℤ ≃ ℤ := (Equiv.prodComm (Fin q) ℤ).trans (Int.divModEquiv q).symm with he
  have he_apply : ∀ p : Fin q × ℤ, e p = p.2 * q + p.1 := fun p => by
    simp [he, Int.divModEquiv]
  have hG : ∀ n : ℤ, Summable fun n : ℤ => (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
    intro _
    have := Complex.summable_ofReal.2
      (summable_int_exp_neg_mul_sq (c := π ^ 2 / (q ^ 2 * u)) (by positivity))
    refine this.congr fun n => ?_
    congr 2; ring
  have h2 : Summable (f ∘ e) := e.summable_iff.2 hfs
  show ∑' k, f k = _
  rw [← e.tsum_eq f, show (fun c => f (e c)) = f ∘ e from rfl, h2.tsum_prod, tsum_fintype]
  set C : ℂ := ((1 / q * √(π / u) : ℝ) : ℂ)
  set G : ℤ → ℂ := fun n => (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) with hGdef
  have hrow : ∀ r : Fin q, ∑' j : ℤ, (f ∘ e) (r, j) = χ r * (C *
      ∑' n : ℤ, cexp (2 * π * I * n * ((r : ℕ) : ℝ) / q) * G n) := by
    intro r
    rw [← tsum_exp_shifted_sq hq ((r : ℕ) : ℝ) hu, ← tsum_mul_left]
    congr 1; funext j
    rw [Function.comp_apply, he_apply, hf]
    simp only
    congr 1
    · have := hper.int_mul j ((r : ℕ) : ℤ)
      rw [show ((j * q + ((r : ℕ) : ℤ) : ℤ)) = ((r : ℕ) : ℤ) + j * q by ring]
      exact this
    · congr 3; push_cast; ring
  simp only [hrow]
  rw [Fin.sum_univ_eq_sum_range (fun r => χ r * (C *
      ∑' n : ℤ, cexp (2 * π * I * n * (r : ℝ) / q) * G n)) q]
  have hS : ∀ r : ℕ, Summable fun n : ℤ => cexp (2 * π * I * n * (r : ℝ) / q) * G n := by
    intro r
    refine Summable.of_norm_bounded (hG 0).norm fun n => le_of_eq ?_
    rw [norm_mul, mul_eq_right₀ (norm_ne_zero_iff.2 (by simp [G, hGdef, Complex.exp_ne_zero]))]
    rw [show 2 * π * I * n * (r : ℝ) / q = ((2 * π * n * r / q : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsum := hasSum_sum (s := range q) fun r _ => ((hS r).hasSum.mul_left (χ r * C))
  calc ∑ r ∈ range q, χ r * (C * ∑' n : ℤ, cexp (2 * π * I * n * (r : ℝ) / q) * G n)
      = ∑ r ∈ range q, χ r * C * ∑' n : ℤ, cexp (2 * π * I * n * (r : ℝ) / q) * G n :=
        sum_congr rfl fun r _ => by ring
    _ = ∑' n : ℤ, ∑ r ∈ range q, χ r * C * (cexp (2 * π * I * n * (r : ℝ) / q) * G n) :=
        hsum.tsum_eq.symm
    _ = C * ∑' n : ℤ, gaussSum q χ n * G n := by
        rw [← tsum_mul_left]
        congr 1; funext n
        unfold gaussSum
        rw [Finset.sum_mul, Finset.mul_sum]
        exact sum_congr rfl fun r _ => by ring

/-- For `g` of period `q`, `∑_{a<q} g(-a) = ∑_{a<q} g(a)`. -/
lemma sum_range_periodic_neg {q : ℕ} {g : ℤ → ℂ} (hper : Function.Periodic g q) :
    ∑ a ∈ range q, g (-(a : ℤ)) = ∑ a ∈ range q, g a := by
  have h1 : ∀ a : ℕ, g (-(a : ℤ)) = g ((q : ℤ) - a) := fun a => by
    rw [show (q : ℤ) - a = -(a : ℤ) + q by ring, hper]
  simp only [h1]
  have h2 := sum_range_reflect (fun j => g ((j : ℤ) + 1)) q
  have h3 : ∀ j ∈ range q, g ((((q - 1 - j : ℕ) : ℤ)) + 1) = g ((q : ℤ) - j) := fun j hj => by
    simp only [mem_range] at hj
    congr 1; omega
  rw [sum_congr rfl h3] at h2
  rw [h2]
  have h4 := sum_range_succ (fun j : ℕ => g (j : ℤ)) q
  have h5 := sum_range_succ' (fun j : ℕ => g (j : ℤ)) q
  have h6 : g (q : ℤ) = g 0 := by simpa using hper 0
  push_cast at h4 h5
  rw [h6] at h4
  linear_combination h5.symm.trans h4 |>.symm.symm

/-- For even `χ`, the Gauss sums are even: `χ̂(-n) = χ̂(n)` ("the terms `±n` are equal"). -/
theorem gaussSum_neg {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (heven : ∀ k, χ (-k) = χ k) (n : ℤ) : gaussSum q χ (-n) = gaussSum q χ n := by
  set g : ℤ → ℂ := fun a => χ a * cexp (2 * π * I * (-n : ℤ) * (a : ℝ) / q) with hg
  have hgper : Function.Periodic g q := by
    intro a
    simp only [hg, hper a]
    congr 1
    have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
    rw [show 2 * π * I * ((-n : ℤ) : ℂ) * (((a + q : ℤ) : ℝ) : ℂ) / q =
      2 * π * I * ((-n : ℤ) : ℂ) * ((a : ℝ) : ℂ) / q + ((-n : ℤ) : ℂ) * (2 * π * I) by
        push_cast; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have := sum_range_periodic_neg hgper
  unfold gaussSum
  rw [← show ∑ a ∈ range q, g a = ∑ a ∈ range q, χ a * cexp (2 * π * I * (-n : ℤ) * (a : ℝ) / q)
    from sum_congr rfl fun a _ => by simp [hg]]
  rw [← this]
  refine sum_congr rfl fun a _ => ?_
  simp only [hg, heven]
  congr 2; push_cast; ring

/-- `∑_{n ∈ ℤ} f n = f 0 + 2 ∑_{n ≥ 1} f n` for even summable `f : ℤ → ℂ`. -/
lemma tsum_int_of_even_complex {f : ℤ → ℂ} (hf : Summable f) (he : ∀ n, f (-n) = f n) :
    ∑' n : ℤ, f n = f 0 + 2 * ∑' n : ℕ, f ((n : ℤ) + 1) := by
  have h1 : Summable fun n : ℕ => f n := hf.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ => f (-((n : ℤ) + 1)) :=
    hf.comp_injective (fun a b h => by simpa using h)
  rw [tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_eq_zero_add]
  simp only [he]
  push_cast
  ring

/-- **Remark 3.7 (`δ = 0`), theta side**: for `χ` even of period `q`,
`∑_{k ≥ 1} χ(k) e^{-k²u} = ½ c₀ χ̂(0) u^{-1/2} - ½ χ(0) + c₀ u^{-1/2} ∑_{n ≥ 1} χ̂(n) e^{-π²n²/(q²u)}`
with `c₀ = √π/q`. -/
theorem tsum_char_theta_half {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (heven : ∀ k, χ (-k) = χ k) {u : ℝ} (hu : 0 < u) :
    ∑' k : ℕ, χ ((k : ℤ) + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      (1 / 2 * (√π / q) * u ^ (-(1 / 2 : ℝ)) : ℝ) * gaussSum q χ 0 - 1 / 2 * χ 0 +
        ((√π / q) * u ^ (-(1 / 2 : ℝ)) : ℝ) * ∑' n : ℕ, gaussSum q χ ((n : ℤ) + 1) *
          (rexp (-(π ^ 2 * ((n : ℝ) + 1) ^ 2 / (q ^ 2 * u))) : ℂ) := by
  have hth := tsum_char_theta hq hper hu
  set Bχ := ∑ a ∈ range q, ‖χ a‖
  have hsL : Summable fun k : ℤ => χ k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) :=
    Summable.of_norm_bounded ((summable_int_exp_neg_mul_sq hu).mul_left Bχ) fun k => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_right (periodic_bound hq hper k) (Real.exp_pos _).le).trans
        (le_of_eq (by simp only [Bχ]; ring))
  have hgb : ∀ n, ‖gaussSum q χ n‖ ≤ Bχ := fun n => by
    unfold gaussSum
    refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _) (le_of_eq _)
    rw [show 2 * π * I * (n : ℂ) * ((a : ℝ) : ℂ) / q = ((2 * π * n * a / q : ℝ) : ℂ) * I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsR : Summable fun n : ℤ => gaussSum q χ n *
      (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) :=
    Summable.of_norm_bounded ((summable_int_exp_neg_mul_sq (c := π ^ 2 / (q ^ 2 * u))
      (by positivity)).mul_left Bχ) fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_right (hgb n) (Real.exp_pos _).le).trans
        (le_of_eq (by simp only [Bχ]; ring))
  rw [tsum_int_of_even_complex hsL (fun k => by simp [heven]),
    tsum_int_of_even_complex hsR (fun n => by simp [gaussSum_neg hq hper heven])] at hth
  have hsq : √(π / u) = √π * u ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div' _ hu.le, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_mul, zero_div, neg_zero, Real.exp_zero, Complex.ofReal_one,
    mul_one, Int.cast_add, Int.cast_natCast, Int.cast_one] at hth
  rw [hsq] at hth
  push_cast at hth ⊢
  linear_combination hth / 2

end ZetaF
