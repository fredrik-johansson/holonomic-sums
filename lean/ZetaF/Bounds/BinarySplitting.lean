/-
# Size bounds for binary splitting (Appendix A.1, "Binary splitting")

A full formalization of the bit complexity (multitape Turing machines) is out of reach, so we prove the
combinatorial core of the cost analysis in a simple cost model.  The product of `2^d` natural numbers
`x_0, …, x_{2^d-1}` is formed by a balanced product tree; the node `(j, i)` holds the product of the
block `[i 2^j, (i+1) 2^j)`.  With `size = Nat.size` (number of bits) we show:

* every level of the tree holds at most `S = ∑ size x_k` bits (`sum_size_level_le`);
* if one multiplication of an `a`-bit by a `b`-bit number costs `M(a + b)` with `M` monotone and
  superadditive (`M a + M b ≤ M (a + b)`, implied by "`M(n)/n` nondecreasing"), the whole tree costs at
  most `d · M(S)` (`treeCost_le`); with `N = 2^d = O(p)` leaves of `O(log p)` bits this is the paper's
  `O(M(p log p) log p)`.

For matrices of fixed size the same argument applies entrywise up to `O(1)` extra bits per level.
-/
import ZetaF.Deps
import Mathlib.Data.Nat.Size

open Finset

namespace ZetaF.BinarySplitting

/-- Number of bits of the product of two numbers. -/
lemma size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · calc a * b < 2 ^ Nat.size a * b := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) hb
      _ ≤ 2 ^ Nat.size a * 2 ^ Nat.size b :=
          Nat.mul_le_mul_left _ (Nat.lt_size_self b).le

lemma size_prod_le (x : ℕ → ℕ) (s : Finset ℕ) (hs : s.Nonempty) :
    Nat.size (∏ k ∈ s, x k) ≤ ∑ k ∈ s, Nat.size (x k) := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs (by simp)
  | cons a s ha ih =>
    rw [prod_cons, sum_cons]
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · exact (size_mul_le _ _).trans (Nat.add_le_add_left (ih hne) _)

/-- Node `(j, i)` of the product tree: the product over the block `[i 2^j, (i+1) 2^j)`. -/
def node (x : ℕ → ℕ) (j i : ℕ) : ℕ := ∏ k ∈ Ico (i * 2 ^ j) ((i + 1) * 2 ^ j), x k

lemma node_zero (x : ℕ → ℕ) (i : ℕ) : node x 0 i = x i := by
  simp [node, Nat.Ico_succ_singleton]

lemma node_succ (x : ℕ → ℕ) (j i : ℕ) :
    node x (j + 1) i = node x j (2 * i) * node x j (2 * i + 1) := by
  unfold node
  rw [prod_Ico_consecutive]
  · congr 1 <;> ring
  · nlinarith [pow_pos (show 0 < 2 by norm_num) j]
  · nlinarith [pow_pos (show 0 < 2 by norm_num) j]

/-- The root of a tree of depth `d` is the product of all leaves. -/
lemma node_root (x : ℕ → ℕ) (d : ℕ) : node x d 0 = ∏ k ∈ range (2 ^ d), x k := by
  unfold node; rw [zero_mul, zero_add, one_mul, range_eq_Ico]

lemma sum_blocks (f : ℕ → ℕ) (m n : ℕ) :
    ∑ i ∈ range n, ∑ k ∈ Ico (i * m) ((i + 1) * m), f k = ∑ k ∈ range (n * m), f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, range_eq_Ico, range_eq_Ico, sum_Ico_consecutive]
    · nlinarith
    · nlinarith

lemma sum_pairs (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range n, (f (2 * i) + f (2 * i + 1)) = ∑ k ∈ range (2 * n), f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ,
      sum_range_succ]
    ring

/-- **Each level of the tree holds at most `S = ∑ size x_k` bits.** -/
theorem sum_size_level_le (x : ℕ → ℕ) {d j : ℕ} (hj : j ≤ d) :
    ∑ i ∈ range (2 ^ (d - j)), Nat.size (node x j i) ≤ ∑ k ∈ range (2 ^ d), Nat.size (x k) := by
  calc ∑ i ∈ range (2 ^ (d - j)), Nat.size (node x j i)
      ≤ ∑ i ∈ range (2 ^ (d - j)), ∑ k ∈ Ico (i * 2 ^ j) ((i + 1) * 2 ^ j), Nat.size (x k) := by
        apply sum_le_sum; intro i _
        apply size_prod_le
        rw [nonempty_Ico]; nlinarith [pow_pos (show 0 < 2 by norm_num) j]
    _ = ∑ k ∈ range (2 ^ d), Nat.size (x k) := by
        rw [sum_blocks, ← pow_add, Nat.sub_add_cancel hj]

/-- Total number of bits stored in the tree: at most `(d + 1) S`. -/
theorem total_bits_le (x : ℕ → ℕ) (d : ℕ) :
    ∑ j ∈ range (d + 1), ∑ i ∈ range (2 ^ (d - j)), Nat.size (node x j i) ≤
      (d + 1) * ∑ k ∈ range (2 ^ d), Nat.size (x k) := by
  calc _ ≤ ∑ j ∈ range (d + 1), ∑ k ∈ range (2 ^ d), Nat.size (x k) := by
        apply sum_le_sum; intro j hj
        exact sum_size_level_le x (by simp at hj; omega)
    _ = _ := by simp

/-- Cost of the product tree of depth `d` when multiplying an `a`-bit and a `b`-bit number costs
`M (a + b)`. -/
def treeCost (M : ℕ → ℕ) (x : ℕ → ℕ) (d : ℕ) : ℕ :=
  ∑ j ∈ range d, ∑ i ∈ range (2 ^ (d - 1 - j)),
    M (Nat.size (node x j (2 * i)) + Nat.size (node x j (2 * i + 1)))

lemma sum_le_of_superadditive {M : ℕ → ℕ} (hsup : ∀ a b, M a + M b ≤ M (a + b))
    (s : Finset ℕ) (f : ℕ → ℕ) : ∑ i ∈ s, M (f i) ≤ M (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [sum_cons, sum_cons]
    exact (Nat.add_le_add_left ih _).trans (hsup _ _)

/-- **Binary splitting cost bound**: a product tree of depth `d` costs at most `d · M(S)`,
`S = ∑ size x_k`. -/
theorem treeCost_le {M : ℕ → ℕ} (hmono : Monotone M) (hsup : ∀ a b, M a + M b ≤ M (a + b))
    (x : ℕ → ℕ) (d : ℕ) :
    treeCost M x d ≤ d * M (∑ k ∈ range (2 ^ d), Nat.size (x k)) := by
  unfold treeCost
  calc _ ≤ ∑ j ∈ range d, M (∑ k ∈ range (2 ^ d), Nat.size (x k)) := by
        apply sum_le_sum; intro j hj
        simp only [mem_range] at hj
        refine (sum_le_of_superadditive hsup _ _).trans (hmono ?_)
        rw [sum_pairs (fun i => Nat.size (node x j i))]
        have : 2 * 2 ^ (d - 1 - j) = 2 ^ (d - j) := by
          rw [← pow_succ']; congr 1; omega
        rw [this]
        exact sum_size_level_le x hj.le
    _ = _ := by simp

/-- With leaves of at most `b` bits: cost `≤ d · M(2^d b)`. -/
theorem treeCost_le_of_size_le {M : ℕ → ℕ} (hmono : Monotone M)
    (hsup : ∀ a b, M a + M b ≤ M (a + b)) (x : ℕ → ℕ) (d b : ℕ)
    (hb : ∀ k, Nat.size (x k) ≤ b) : treeCost M x d ≤ d * M (2 ^ d * b) := by
  refine (treeCost_le hmono hsup x d).trans (Nat.mul_le_mul_left _ (hmono ?_))
  calc ∑ k ∈ range (2 ^ d), Nat.size (x k) ≤ ∑ k ∈ range (2 ^ d), b := sum_le_sum fun k _ => hb k
    _ = 2 ^ d * b := by simp

/-- Superadditivity follows from "`M(n)/n` nondecreasing", the regularity condition used in the paper
(§5, `M(p)/p` nondecreasing). -/
lemma superadditive_of_div_mono {M : ℕ → ℕ} (hM0 : M 0 = 0)
    (h : ∀ a b, 0 < a → a ≤ b → M a * b ≤ M b * a) (a b : ℕ) : M a + M b ≤ M (a + b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [hM0]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [hM0]
  have h1 := h a (a + b) ha (by omega)
  have h2 := h b (a + b) hb (by omega)
  have : (M a + M b) * (a + b) ≤ M (a + b) * (a + b) := by nlinarith
  exact Nat.le_of_mul_le_mul_right this (by omega)

end ZetaF.BinarySplitting
