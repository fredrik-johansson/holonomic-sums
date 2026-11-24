/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Product trees in a monoid (Appendix A, lemma L2)

Binary splitting multiplies `2^d` matrices `[[A_n, 0], [B_n, q_n]]` in a balanced product tree. The
product is noncommutative and sizes are only *quasi*-subadditive: an entry of a product of two
`D × D` integer matrices has at most `size A + size B + size D` bits. This file generalizes
`ZetaF.BinarySplitting.treeCost_le` (natural numbers) to any monoid with a size function satisfying
`size (a * b) ≤ size a + size b + κ`:

* every level of the tree holds at most `S + κ 2^d` size units, `S = ∑ size x_k` (`sum_sizeL_level_le`);
* the tree costs at most `d · M(S + κ 2^d)` if one product of sizes `a`, `b` costs `M(a + b)` with `M`
  monotone and superadditive (`treeCostL_le`);
* for integer matrices, `κ = size D` (`matSize_mul_le`).

For matrices over the ring of integers of a number field (in coordinates on an integral basis) the
multiplication table has fixed height, so the same holds with `κ = O(1)`.
-/
import ZetaF.Bounds.BinarySplitting
import Mathlib.Data.Matrix.Mul

open Finset

namespace ZetaF.AppA

/-- Node `(j, i)` of the ordered product tree: the product of the block `[i 2^j, (i+1) 2^j)`. -/
def nodeL {α : Type*} [Monoid α] (x : ℕ → α) (j i : ℕ) : α :=
  ((List.range' (i * 2 ^ j) (2 ^ j)).map x).prod

lemma nodeL_zero {α : Type*} [Monoid α] (x : ℕ → α) (i : ℕ) : nodeL x 0 i = x i := by
  simp [nodeL]

lemma nodeL_succ {α : Type*} [Monoid α] (x : ℕ → α) (j i : ℕ) :
    nodeL x (j + 1) i = nodeL x j (2 * i) * nodeL x j (2 * i + 1) := by
  unfold nodeL
  rw [show i * 2 ^ (j + 1) = 2 * i * 2 ^ j by ring, show 2 ^ (j + 1) = 2 ^ j + 2 ^ j by ring,
    ← List.range'_append, List.map_append, List.prod_append]
  congr 3; ring

/-- The root is the ordered product of all leaves. -/
lemma nodeL_root {α : Type*} [Monoid α] (x : ℕ → α) (d : ℕ) :
    nodeL x d 0 = ((List.range (2 ^ d)).map x).prod := by
  simp [nodeL, List.range_eq_range']

variable {α : Type*} [Monoid α] (size : α → ℕ) (κ : ℕ)

/-- The size of a node: at most the sizes of its leaves plus `κ` per internal product. -/
lemma sizeL_node_le (hsize : ∀ a b, size (a * b) ≤ size a + size b + κ) (x : ℕ → α) (j i : ℕ) :
    size (nodeL x j i) + κ ≤ ∑ k ∈ Ico (i * 2 ^ j) ((i + 1) * 2 ^ j), size (x k) + κ * 2 ^ j := by
  induction j generalizing i with
  | zero => simp [nodeL_zero, Nat.Ico_succ_singleton]
  | succ j ih =>
    rw [nodeL_succ]
    have h1 := ih (2 * i)
    have h2 := ih (2 * i + 1)
    have hsplit : ∑ k ∈ Ico (i * 2 ^ (j + 1)) ((i + 1) * 2 ^ (j + 1)), size (x k) =
        ∑ k ∈ Ico (2 * i * 2 ^ j) ((2 * i + 1) * 2 ^ j), size (x k) +
          ∑ k ∈ Ico ((2 * i + 1) * 2 ^ j) ((2 * i + 1 + 1) * 2 ^ j), size (x k) := by
      rw [sum_Ico_consecutive]
      · congr 1 <;> ring
      · nlinarith [pow_pos (show 0 < 2 by norm_num) j]
      · nlinarith [pow_pos (show 0 < 2 by norm_num) j]
    rw [hsplit, pow_succ]
    have := hsize (nodeL x j (2 * i)) (nodeL x j (2 * i + 1))
    linarith

/-- **Each level holds at most `S + κ 2^d` size units.** -/
theorem sum_sizeL_level_le (hsize : ∀ a b, size (a * b) ≤ size a + size b + κ) (x : ℕ → α)
    {d j : ℕ} (hj : j ≤ d) :
    ∑ i ∈ range (2 ^ (d - j)), size (nodeL x j i) ≤ ∑ k ∈ range (2 ^ d), size (x k) + κ * 2 ^ d := by
  have h : ∀ i ∈ range (2 ^ (d - j)), size (nodeL x j i) ≤
      ∑ k ∈ Ico (i * 2 ^ j) ((i + 1) * 2 ^ j), size (x k) + κ * 2 ^ j := fun i _ => by
    have := sizeL_node_le size κ hsize x j i; omega
  calc ∑ i ∈ range (2 ^ (d - j)), size (nodeL x j i)
      ≤ ∑ i ∈ range (2 ^ (d - j)), (∑ k ∈ Ico (i * 2 ^ j) ((i + 1) * 2 ^ j), size (x k) + κ * 2 ^ j) :=
        sum_le_sum h
    _ = ∑ k ∈ range (2 ^ d), size (x k) + κ * 2 ^ d := by
        rw [sum_add_distrib, BinarySplitting.sum_blocks, sum_const, card_range, smul_eq_mul,
          ← pow_add, Nat.sub_add_cancel hj, mul_left_comm, ← pow_add, Nat.sub_add_cancel hj]

/-- Cost of the ordered product tree when a product of sizes `a`, `b` costs `M (a + b)`. -/
def treeCostL (M : ℕ → ℕ) (x : ℕ → α) (d : ℕ) : ℕ :=
  ∑ j ∈ range d, ∑ i ∈ range (2 ^ (d - 1 - j)),
    M (size (nodeL x j (2 * i)) + size (nodeL x j (2 * i + 1)))

/-- **Binary splitting cost in a monoid**: `treeCostL ≤ d · M(S + κ 2^d)`. -/
theorem treeCostL_le (hsize : ∀ a b, size (a * b) ≤ size a + size b + κ)
    {M : ℕ → ℕ} (hmono : Monotone M) (hsup : ∀ a b, M a + M b ≤ M (a + b)) (x : ℕ → α) (d : ℕ) :
    treeCostL size M x d ≤ d * M (∑ k ∈ range (2 ^ d), size (x k) + κ * 2 ^ d) := by
  unfold treeCostL
  calc _ ≤ ∑ j ∈ range d, M (∑ k ∈ range (2 ^ d), size (x k) + κ * 2 ^ d) := by
        apply sum_le_sum; intro j hj
        simp only [mem_range] at hj
        refine (BinarySplitting.sum_le_of_superadditive hsup _ _).trans (hmono ?_)
        rw [BinarySplitting.sum_pairs (fun i => size (nodeL x j i))]
        have : 2 * 2 ^ (d - 1 - j) = 2 ^ (d - j) := by
          rw [← pow_succ']; congr 1; omega
        rw [this]
        exact sum_sizeL_level_le size κ hsize x hj.le
    _ = _ := by simp

/-! ### Integer matrices -/

/-- The entry size of an integer matrix (bits of the largest entry). -/
def matSize {D : ℕ} (A : Matrix (Fin D) (Fin D) ℤ) : ℕ :=
  univ.sup fun ij : Fin D × Fin D => Nat.size (A ij.1 ij.2).natAbs

lemma natAbs_lt_of_matSize {D : ℕ} (A : Matrix (Fin D) (Fin D) ℤ) (i j : Fin D) :
    (A i j).natAbs < 2 ^ matSize A := by
  rw [← Nat.size_le]
  exact le_sup (f := fun ij : Fin D × Fin D => Nat.size (A ij.1 ij.2).natAbs) (mem_univ (i, j))

/-- **Entries of a product of `D × D` integer matrices have at most `size A + size B + size D`
bits.** -/
theorem matSize_mul_le {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℤ) :
    matSize (A * B) ≤ matSize A + matSize B + Nat.size D := by
  unfold matSize
  refine Finset.sup_le fun ij _ => ?_
  rw [Nat.size_le]
  have hD : D < 2 ^ Nat.size D := Nat.lt_size_self D
  have hterm : ∀ k : Fin D, (A ij.1 k * B k ij.2).natAbs < 2 ^ (matSize A + matSize B) := by
    intro k
    rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_lt_mul'' (natAbs_lt_of_matSize A _ _) (natAbs_lt_of_matSize B _ _)
  calc ((A * B) ij.1 ij.2).natAbs = (∑ k, A ij.1 k * B k ij.2).natAbs := by
        rw [Matrix.mul_apply]
    _ ≤ ∑ k, (A ij.1 k * B k ij.2).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k : Fin D, (2 ^ (matSize A + matSize B) - 1) :=
        sum_le_sum fun k _ => Nat.le_sub_one_of_lt (hterm k)
    _ = D * (2 ^ (matSize A + matSize B) - 1) := by simp
    _ < 2 ^ (matSize A + matSize B + Nat.size D) := by
        have hP : 0 < 2 ^ (matSize A + matSize B) := by positivity
        calc D * (2 ^ (matSize A + matSize B) - 1) ≤ D * 2 ^ (matSize A + matSize B) :=
              Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ < 2 ^ Nat.size D * 2 ^ (matSize A + matSize B) := Nat.mul_lt_mul_of_pos_right hD hP
          _ = _ := by rw [← pow_add, add_comm (Nat.size D)]

/-- **Binary splitting with integer matrices**: a product tree of `2^d` matrices of entry size at
most `b` costs at most `d · M(2^d (b + size D))`. -/
theorem treeCost_matrix_le {D : ℕ} {M : ℕ → ℕ} (hmono : Monotone M)
    (hsup : ∀ a b, M a + M b ≤ M (a + b)) (x : ℕ → Matrix (Fin D) (Fin D) ℤ) (d b : ℕ)
    (hb : ∀ k, matSize (x k) ≤ b) :
    treeCostL matSize M x d ≤ d * M (2 ^ d * (b + Nat.size D)) := by
  refine (treeCostL_le matSize (Nat.size D) matSize_mul_le hmono hsup x d).trans
    (Nat.mul_le_mul_left _ (hmono ?_))
  calc ∑ k ∈ range (2 ^ d), matSize (x k) + Nat.size D * 2 ^ d
      ≤ ∑ _k ∈ range (2 ^ d), b + Nat.size D * 2 ^ d :=
        Nat.add_le_add_right (sum_le_sum fun k _ => hb k) _
    _ = 2 ^ d * (b + Nat.size D) := by simp; ring

end ZetaF.AppA
