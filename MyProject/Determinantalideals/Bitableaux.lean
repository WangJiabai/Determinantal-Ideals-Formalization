/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib
import MyProject.Determinantalideals.Basic
import MyProject.Determinantalideals.MinorTerms
import MyProject.Determinantalideals.Ideal
import MyProject.Determinantalideals.DiagonalOrder
import MyProject.Determinantalideals.Finite
import MyProject.Determinantalideals.Sturmfels_lemma

namespace Determinantal

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Young bitableaux -/

structure YoungBitableau (m n : ℕ) where
  v : ℕ
  size : Fin v → ℕ
  size_pos : ∀ a : Fin v, 0 < size a
  minorindex : ∀ a : Fin v, MinorIndex m n (size a)
  shape_antitone :
    ∀ a b : Fin v, a ≤ b → size b ≤ size a

namespace YoungBitableau

/-- The empty bitableau. Its associated polynomial is `1`. -/
noncomputable def empty (m n : ℕ) : YoungBitableau m n where
  v := 0
  size := Fin.elim0
  size_pos := by
    intro a
    exact Fin.elim0 a
  minorindex := fun a => Fin.elim0 a
  shape_antitone := by
    intro a
    exact Fin.elim0 a

/-- The `1 × 1` minor selecting the matrix entry indexed by `p`. -/
def oneByOneMinorIndex {m n : ℕ} (p : Fin m × Fin n) : MinorIndex m n 1 where
  row :=
    OrderEmbedding.ofStrictMono
      (fun _ : Fin 1 => p.1)
      (by
        intro i j h
        fin_cases i
        fin_cases j
        simp at h)
  col :=
    OrderEmbedding.ofStrictMono
      (fun _ : Fin 1 => p.2)
      (by
        intro i j h
        fin_cases i
        fin_cases j
        simp at h)

@[simp] lemma oneByOneMinorIndex_row_zero {m n : ℕ} (p : Fin m × Fin n) :
    (oneByOneMinorIndex p).row 0 = p.1 := by
  rfl

@[simp] lemma oneByOneMinorIndex_col_zero {m n : ℕ} (p : Fin m × Fin n) :
    (oneByOneMinorIndex p).col 0 = p.2 := by
  rfl

noncomputable def toPolynomial (k : Type*) [CommRing k] {m n}
    (B : YoungBitableau m n) :
    MvPolynomial (Fin m × Fin n) k :=
  ∏ a : Fin B.v, genericMinor k (B.minorindex a)

@[simp] lemma toPolynomial_empty {m n : ℕ}
    (k : Type*) [CommRing k] :
    toPolynomial k (empty m n) = 1 := by
  simp [empty, toPolynomial]

@[simp] lemma genericMinor_oneByOneMinorIndex {m n : ℕ}
    {k : Type*} [CommRing k] (p : Fin m × Fin n) :
    genericMinor k (oneByOneMinorIndex p) = MvPolynomial.X p := by
  simp [genericMinor, oneByOneMinorIndex]

@[simp] lemma genericMinor_cast_congrArg {m n t u : ℕ}
    {k : Type*} [CommRing k]
    (h : t = u) (I : MinorIndex m n t) :
    genericMinor k
        (cast (congrArg (MinorIndex m n) h) I : MinorIndex m n u) =
      genericMinor k I := by
  cases h
  rfl

def length
    {m n : ℕ}
    (B : YoungBitableau m n) : ℕ := Finset.univ.sup B.size

lemma size_le_length {m n : ℕ} (B : YoungBitableau m n) :
  ∀ a : Fin B.v, B.size a ≤ B.length := by
  intro a
  unfold length
  exact Finset.le_sup (Finset.mem_univ a)

theorem length_eq_size_zero
    {m n : ℕ}
    (B : YoungBitableau m n)
    (hv : 0 < B.v) :
    length B = B.size ⟨0, hv⟩ := by
  apply le_antisymm
  · unfold length
    apply Finset.sup_le
    intro a ha
    exact B.shape_antitone ⟨0, hv⟩ a (left_eq_inf.mp rfl)
  · exact size_le_length B ⟨0, hv⟩

def degree
    {m n : ℕ}
    (B : YoungBitableau m n) : ℕ :=
  ∑ a : Fin B.v, B.size a

lemma toPolynomial_isHomogeneous
    {m n : ℕ}
    (k : Type*) [CommRing k]
    (B : YoungBitableau m n) :
    (toPolynomial k B).IsHomogeneous B.degree := by
  rw [toPolynomial, degree]
  convert MvPolynomial.IsHomogeneous.prod
      (Finset.univ : Finset (Fin B.v))
      (fun a => genericMinor k (B.minorindex a))
      B.size
      (fun a _ => genericMinor_isHomogeneous k (B.minorindex a)) using 1

def IsStandard
    {m n : ℕ}
    (B : YoungBitableau m n) : Prop :=
  ∀ (a b : Fin B.v) (hnext : a.val + 1 = b.val),
    ∀ (j : Fin (B.size b)),
      (B.minorindex a).row
          ⟨j.val,
            lt_of_lt_of_le j.isLt
              (B.shape_antitone a b (by grind))⟩
        ≤ (B.minorindex b).row j
      ∧
      (B.minorindex a).col
          ⟨j.val,
            lt_of_lt_of_le j.isLt
              (B.shape_antitone a b (by grind))⟩
        ≤ (B.minorindex b).col j

/-- A bitableau whose factors are all `1 × 1` minors. -/
def oneMinorVec {m n : ℕ} (v : ℕ) (f : Fin v → Fin m × Fin n) :
    YoungBitableau m n where
  v := v
  size := fun _ => 1
  size_pos := by
    intro a
    decide
  minorindex := fun a => oneByOneMinorIndex (f a)
  shape_antitone := by
    intro a b h
    simp

@[simp] lemma toPolynomial_oneMinorVec {m n : ℕ}
    (k : Type*) [CommRing k]
    (v : ℕ) (f : Fin v → Fin m × Fin n) :
    toPolynomial k (oneMinorVec v f) =
      ∏ a : Fin v, MvPolynomial.X (f a) := by
  simp [oneMinorVec, toPolynomial]

lemma toPolynomial_oneMinorVec_snoc {m n : ℕ}
    (k : Type*) [CommRing k]
    (v : ℕ) (f : Fin v → Fin m × Fin n) (p : Fin m × Fin n) :
    toPolynomial k
        (oneMinorVec (v + 1) (Fin.snoc f p)) =
      toPolynomial k (oneMinorVec v f) * MvPolynomial.X p := by
  rw [toPolynomial_oneMinorVec, toPolynomial_oneMinorVec, Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Append a `1 × 1` minor at the end of a bitableau. -/
noncomputable def snocOneMinor {m n : ℕ}
    (B : YoungBitableau m n) (p : Fin m × Fin n) :
    YoungBitableau m n where
  v := B.v + 1
  size := Fin.snoc (fun a : Fin B.v => B.size a) 1
  size_pos := by
    intro a
    cases a using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast a => simpa [Fin.snoc_castSucc] using B.size_pos a
  minorindex :=
    fun a => by
      cases a using Fin.lastCases with
      | last =>
        simpa [Fin.snoc_last] using oneByOneMinorIndex p
      | cast a =>
        simpa [Fin.snoc_castSucc] using B.minorindex a
  shape_antitone := by
    intro a b h
    cases b using Fin.lastCases with
    | last =>
      cases a using Fin.lastCases with
      | last => simp [Fin.snoc_last]
      | cast a => simpa [Fin.snoc_castSucc, Fin.snoc_last] using B.size_pos a
    | cast b =>
      cases a using Fin.lastCases with
      | last =>
        have hval : (Fin.last B.v).val ≤ (Fin.castSucc b).val := h
        exact False.elim ((not_le_of_gt b.isLt) hval)
      | cast a =>
        have hab : a ≤ b := h
        simpa [Fin.snoc_castSucc] using B.shape_antitone a b hab

@[simp] lemma toPolynomial_snocOneMinor {m n : ℕ}
    (k : Type*) [CommRing k]
    (B : YoungBitableau m n) (p : Fin m × Fin n) :
    toPolynomial k (snocOneMinor B p) =
      toPolynomial k B * MvPolynomial.X p := by
  rw [toPolynomial]
  change
    (∏ a : Fin (B.v + 1),
        genericMinor k ((snocOneMinor B p).minorindex a)) =
      toPolynomial k B * MvPolynomial.X p
  rw [Fin.prod_univ_castSucc]
  simp [snocOneMinor, toPolynomial]

lemma length_le_length_snocOneMinor {m n : ℕ}
    (B : YoungBitableau m n) (p : Fin m × Fin n) :
    B.length ≤ (snocOneMinor B p).length := by
  unfold length
  apply Finset.sup_le
  intro a _ha
  have h := size_le_length (snocOneMinor B p) (Fin.castSucc a)
  simpa [snocOneMinor, Fin.snoc_castSucc] using h

/-- A bitableau consisting of a single minor. -/
noncomputable def oneMinor {m n t : ℕ}
    (ht : 0 < t) (I : MinorIndex m n t) :
    YoungBitableau m n where
  v := 1
  size := fun _ => t
  size_pos := by
    intro _
    exact ht
  minorindex := fun _ => I
  shape_antitone := by
    intro a b h
    fin_cases a
    fin_cases b
    rfl

@[simp] lemma toPolynomial_oneMinor {m n t : ℕ}
    (k : Type*) [CommRing k]
    (ht : 0 < t) (I : MinorIndex m n t) :
    toPolynomial k (oneMinor ht I) =
      genericMinor k I := by
  simp [oneMinor, toPolynomial]

@[simp] lemma length_oneMinor {m n t : ℕ}
    (ht : 0 < t) (I : MinorIndex m n t) :
    length (oneMinor ht I) = t := by
  simp [length, oneMinor]

end YoungBitableau

/-! ## Generalized permutations and monomial width -/

/-- Sort a list of matrix indices in row-column order.

This is the word of the generalized permutation attached to the input list.
-/
def generalizedPermutation
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    List (Fin m × Fin n) :=
  ((xs.map toLex).insertionSort (fun x y : Fin m ×ₗ Fin n => x ≤ y)).map ofLex

namespace generalizedPermutation

theorem generalizedPermutation_sorted
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    (generalizedPermutation xs).Pairwise (fun x y => toLex x ≤ toLex y) := by
  unfold generalizedPermutation
  simpa [List.pairwise_map] using
    (List.pairwise_insertionSort
      (fun x y : Fin m ×ₗ Fin n => x ≤ y)
      (xs.map toLex))

/-- The generalized permutation word contains exactly the same indices as the input list. -/
theorem generalizedPermutation_perm
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    (generalizedPermutation xs).Perm xs := by
  unfold generalizedPermutation
  simpa [Function.comp_def] using
    ((List.perm_insertionSort
      (fun x y : Fin m ×ₗ Fin n => x ≤ y)
      (xs.map toLex)).map ofLex)

theorem generalizedPermutation_unique
    {m n : ℕ}
    {xs w₁ w₂ : List (Fin m × Fin n)}
    (h₁perm : w₁.Perm xs)
    (h₁sorted : w₁.Pairwise (fun x y => toLex x ≤ toLex y))
    (h₂perm : w₂.Perm xs)
    (h₂sorted : w₂.Pairwise (fun x y => toLex x ≤ toLex y)) :
    w₁ = w₂ := by
  have h₁sortedLex :
      (w₁.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n)).Pairwise
        (fun x y => x ≤ y) := by
    simpa [List.pairwise_map] using h₁sorted
  have h₂sortedLex :
      (w₂.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n)).Pairwise
        (fun x y => x ≤ y) := by
    simpa [List.pairwise_map] using h₂sorted
  have hpermLex :
      (w₁.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n)).Perm
        (w₂.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n)) :=
    (h₁perm.map toLex).trans (h₂perm.map toLex).symm
  have hmap :
      w₁.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n) =
        w₂.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n) :=
    hpermLex.eq_of_pairwise' h₁sortedLex h₂sortedLex
  exact (toLex : (Fin m × Fin n) ≃ Fin m ×ₗ Fin n).injective.list_map hmap

/-- The upper row of the generalized permutation. -/
def upperWord
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    List (Fin m) :=
  (generalizedPermutation xs).map fun x => x.1

/-- The lower row of the generalized permutation. This is the row used to define width. -/
def lowerWord
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    List (Fin n) :=
  (generalizedPermutation xs).map fun x => x.2

lemma lowerWord_length
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    (lowerWord xs).length = xs.length := by
  unfold lowerWord
  rw [List.length_map]
  exact (generalizedPermutation_perm xs).length_eq

lemma lowerWord_ne_nil_of_ne_nil
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (hxs : xs ≠ []) :
    lowerWord xs ≠ [] := by
  intro h
  have hlen : xs.length = 0 := by
    have hlen' := lowerWord_length xs
    rw [h] at hlen'
    exact hlen'.symm
  apply hxs
  cases xs with
  | nil =>
      rfl
  | cons x xs =>
      simp at hlen

/-- Width of a monomial-index list.

Given a list of matrix indices, first form the generalized permutation,
then take the lower row, and finally take the maximal length of a strictly
decreasing subsequence of that lower row.
-/
def width {m n : ℕ}
    (xs : List (Fin m × Fin n)) : ℕ :=
  (((lowerWord xs).sublists.filter
    (fun s : List (Fin n) =>
      (s.zip s.tail).all (fun p => decide (p.1 > p.2)))))
    |>.foldl (fun acc s => max acc s.length) 0

lemma foldl_max_length_ge_acc
    {α : Type*}
    (L : List (List α))
    (acc : ℕ) :
    acc ≤ L.foldl (fun acc s => max acc s.length) acc := by
  induction L generalizing acc with
  | nil =>
      rfl
  | cons s L ih =>
      simpa using
        le_trans
          (Nat.le_max_left acc s.length)
          (ih (max acc s.length))

lemma length_le_foldl_max_length_of_mem_aux
    {α : Type*}
    {s : List α}
    (L : List (List α))
    (acc : ℕ)
    (hs : s ∈ L) :
    s.length ≤ L.foldl (fun acc t => max acc t.length) acc := by
  induction L generalizing acc with
  | nil =>
      simp at hs
  | cons t L ih =>
      simp only [List.mem_cons] at hs
      cases hs with
      | inl h =>
          rw [h]
          exact
            le_trans
              (Nat.le_max_right acc t.length)
              (foldl_max_length_ge_acc L (max acc t.length))
      | inr h =>
          exact ih (max acc t.length) h

lemma length_le_foldl_max_length_of_mem
    {α : Type*}
    {L : List (List α)}
    {s : List α}
    (hs : s ∈ L) :
    s.length ≤ L.foldl (fun acc t => max acc t.length) 0 := by
  exact length_le_foldl_max_length_of_mem_aux L 0 hs

lemma length_le_width_of_mem_filtered_sublists
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {s : List (Fin n)}
    (hs :
      s ∈ ((lowerWord xs).sublists.filter
        (fun s : List (Fin n) =>
          (s.zip s.tail).all (fun p => decide (p.1 > p.2))))) :
    s.length ≤ width xs := by
  unfold width
  exact length_le_foldl_max_length_of_mem hs

lemma one_le_width_of_lowerWord_ne_nil
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (h : lowerWord xs ≠ []) :
    1 ≤ width xs := by
  unfold width
  cases hW : lowerWord xs with
  | nil =>
      exact False.elim (h hW)
  | cons a t =>
      have hmem :
          [a] ∈ (((a :: t).sublists.filter
            (fun s : List (Fin n) =>
              (s.zip s.tail).all (fun p => decide (p.1 > p.2))))) := by
        simp
      simpa [hW] using
        (length_le_foldl_max_length_of_mem
          (L := ((a :: t).sublists.filter
            (fun s : List (Fin n) =>
              (s.zip s.tail).all (fun p => decide (p.1 > p.2)))))
          (s := [a])
          hmem)

lemma two_le_width_of_desc_pair_sublist
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {a b : Fin n}
    (hsub : List.Sublist [a, b] (lowerWord xs))
    (hab : a > b) :
    2 ≤ width xs := by
  apply length_le_width_of_mem_filtered_sublists
    (xs := xs)
    (s := [a, b])
  have hmem_sub : [a, b] ∈ (lowerWord xs).sublists := by
    exact (List.mem_sublists).2 hsub
  simp [hmem_sub, hab]

lemma not_desc_pair_sublist_of_width_eq_one
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (hw : width xs = 1)
    {a b : Fin n}
    (hsub : List.Sublist [a, b] (lowerWord xs)) :
    ¬ a > b := by
  intro hab
  have h2 : 2 ≤ width xs :=
    two_le_width_of_desc_pair_sublist
      (xs := xs) hsub hab
  omega

lemma foldl_max_length_le
    {α : Type*}
    (L : List (List α))
    (B acc : ℕ)
    (hacc : acc ≤ B)
    (hL : ∀ s ∈ L, s.length ≤ B) :
    L.foldl (fun acc s => max acc s.length) acc ≤ B := by
  induction L generalizing acc with
  | nil =>
      simpa using hacc
  | cons s L ih =>
      simp only [List.mem_cons] at hL
      have hs : s.length ≤ B := hL s (Or.inl rfl)
      have htail : ∀ t ∈ L, t.length ≤ B := by
        intro t ht
        exact hL t (Or.inr ht)
      exact ih (max acc s.length) (max_le hacc hs) htail

lemma width_le_one_of_lowerWord_pairwise_le
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (hmono : (lowerWord xs).Pairwise (fun a b => a ≤ b)) :
    width xs ≤ 1 := by
  unfold width
  apply foldl_max_length_le
  · exact Nat.zero_le 1
  · intro s hs
    have hs_mem :
        s ∈ (lowerWord xs).sublists := by
      exact (List.mem_filter.mp hs).1
    have hs_dec :
        (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true := by
      exact (List.mem_filter.mp hs).2
    have hsub : List.Sublist s (lowerWord xs) := by
      exact (List.mem_sublists).1 hs_mem
    have hs_mono : s.Pairwise (fun a b => a ≤ b) := by
      exact hmono.sublist hsub
    cases s with
    | nil =>
        simp
    | cons a s' =>
        cases s' with
        | nil =>
            simp
        | cons b t =>
            have hgt : a > b := by
              have h := hs_dec
              simp only [List.tail_cons, List.zip_cons_cons, gt_iff_lt, List.all_cons,
                Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Prod.forall] at h
              exact h.1
            have hle : a ≤ b := by
              have h := hs_mono
              simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
              exact h.1.1
            exact False.elim ((not_lt_of_ge hle) hgt)

lemma pairwise_le_of_no_desc_pair_sublist
    {n : ℕ}
    {l : List (Fin n)}
    (hno :
      ∀ a b : Fin n,
        List.Sublist [a, b] l → ¬ a > b) :
    l.Pairwise (fun a b => a ≤ b) := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      simp only [List.pairwise_cons]
      constructor
      · intro b hb
        have hsub_tail : List.Sublist [b] t := by
          exact (List.singleton_sublist).2 hb
        have hsub : List.Sublist [a, b] (a :: t) := by
          simpa using hsub_tail.cons₂ a
        exact le_of_not_gt (hno a b hsub)
      · apply ih
        intro a' b' hsub'
        exact hno a' b' (hsub'.cons a)

lemma width_eq_one_iff_lowerWord_pairwise_le
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (hxs : lowerWord xs ≠ []) :
    width xs = 1 ↔
      (lowerWord xs).Pairwise (fun a b => a ≤ b) := by
  constructor
  · intro hw
    apply pairwise_le_of_no_desc_pair_sublist
    intro a b hsub
    exact
      not_desc_pair_sublist_of_width_eq_one
        (xs := xs) hw hsub
  · intro hmono
    apply le_antisymm
    · exact width_le_one_of_lowerWord_pairwise_le
        (xs := xs) hmono
    · exact one_le_width_of_lowerWord_ne_nil
        (xs := xs) hxs

/-- Expand a monomial exponent vector into the list of all matrix-variable indices.

The index `(i,j)` appears exactly `E (i,j)` times.
-/
def indicesOfMonomialExp {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) :
    List (Fin m × Fin n) :=
  List.flatMap
    (fun i : Fin m =>
      List.flatMap
        (fun j : Fin n =>
          List.replicate (E (i, j)) (i, j))
        (List.finRange n))
    (List.finRange m)

lemma count_indicesOfMonomialExp
    {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ)
    (p : Fin m × Fin n) :
    (indicesOfMonomialExp E).count p = E p := by
  classical
  rcases p with ⟨pi, pj⟩
  rw [indicesOfMonomialExp]
  rw [List.count_flatMap]
  calc
    (List.map
        (List.count (pi, pj) ∘
          fun i => List.flatMap (fun j => List.replicate (E (i, j)) (i, j))
            (List.finRange n))
        (List.finRange m)).sum
        =
      ∑ i : Fin m,
        List.count (pi, pj)
          (List.flatMap (fun j => List.replicate (E (i, j)) (i, j))
            (List.finRange n)) := by
        simpa [Function.comp_def] using
          (Fin.sum_univ_def
            (fun i : Fin m =>
              List.count (pi, pj)
                (List.flatMap (fun j => List.replicate (E (i, j)) (i, j))
                  (List.finRange n)))).symm
    _ =
      ∑ i : Fin m, ∑ j : Fin n,
        List.count (pi, pj) (List.replicate (E (i, j)) (i, j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [List.count_flatMap]
        simpa [Function.comp_def] using
          (Fin.sum_univ_def
            (fun j : Fin n =>
              List.count (pi, pj) (List.replicate (E (i, j)) (i, j)))).symm
    _ =
      ∑ i : Fin m, ∑ j : Fin n,
        if (i, j) = (pi, pj) then E (i, j) else 0 := by
        simp [List.count_replicate, beq_iff_eq]
    _ = E (pi, pj) := by
        rw [Finset.sum_eq_single (s := Finset.univ) (a := pi)
          (f := fun i : Fin m => ∑ j : Fin n,
            if (i, j) = (pi, pj) then E (i, j) else 0)]
        · simp
        · intro i _ hi
          simp [hi]
        · intro hi
          exact False.elim (hi (Finset.mem_univ pi))

end generalizedPermutation

/-- The paper's width of a monomial, with monomials represented by exponent vectors. -/
def monomialWidth {m n : ℕ} (E : (Fin m × Fin n) →₀ ℕ) : ℕ :=
  generalizedPermutation.width
    (generalizedPermutation.indicesOfMonomialExp E)

lemma antidiagExp_apply'
    {m n t : ℕ}
    (I : MinorIndex m n t) (a : Fin m) (b : Fin n) :
    antidiagExp I (a, b) =
      if ∃ i : Fin t, I.row i = a ∧ I.col i.rev = b then 1 else 0 := by
  classical
  by_cases h : ∃ i : Fin t, I.row i = a ∧ I.col i.rev = b
  · rcases h with ⟨i, hrow, hcol⟩
    have hpair :
        ∀ j : Fin t, ((I.row j, I.col j.rev) = (a, b)) ↔ j = i := by
      intro j
      constructor
      · intro hj
        have hjrow : I.row j = I.row i := by
          calc
            I.row j = a := by simpa using congrArg Prod.fst hj
            _ = I.row i := hrow.symm
        exact I.row.injective hjrow
      · intro hj
        subst hj
        simp [hrow, hcol]
    simp [antidiagExp, Finsupp.single_apply, hpair]
    subst hrow hcol
    simp_all only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, exists_eq]
  · have hpairFalse :
        ∀ j : Fin t, (I.row j, I.col j.rev) ≠ (a, b) := by
      intro j hj
      exact h ⟨j, by simpa using congrArg Prod.fst hj, by simpa using congrArg Prod.snd hj⟩
    simp [antidiagExp, h, hpairFalse]

/-- The list of anti-diagonal variables in a minor, in increasing row order. -/
abbrev antidiagIndexList {m n t : ℕ} (I : MinorIndex m n t) :
    List (Fin m × Fin n) :=
  List.ofFn fun i : Fin t => (I.row i, I.col i.rev)

lemma count_antidiagIndexList
    {m n t : ℕ}
    (I : MinorIndex m n t)
    (p : Fin m × Fin n) :
    (antidiagIndexList I).count p = antidiagExp I p := by
  classical
  rcases p with ⟨a, b⟩
  rw [antidiagExp_apply']
  by_cases h : ∃ i : Fin t, I.row i = a ∧ I.col i.rev = b
  · rcases h with ⟨i, hirow, hicol⟩
    have hex : ∃ i : Fin t, I.row i = a ∧ I.col i.rev = b := ⟨i, hirow, hicol⟩
    have hcount : (antidiagIndexList I).count (a, b) = 1 := by
      have hnodup : (antidiagIndexList I).Nodup := by
        rw [antidiagIndexList, List.nodup_ofFn]
        intro x y hxy
        have hrow : I.row x = I.row y := by
          simpa using congrArg Prod.fst hxy
        exact I.row.injective hrow
      have hmem : (a, b) ∈ antidiagIndexList I := by
        rw [antidiagIndexList, List.mem_ofFn']
        exact ⟨i, by simp [hirow, hicol]⟩
      exact List.count_eq_one_of_mem hnodup hmem
    simp [hex, hcount]
  · have hnotmem : (a, b) ∉ antidiagIndexList I := by
      simp [antidiagIndexList, h]
    have hcount : (antidiagIndexList I).count (a, b) = 0 :=
      List.count_eq_zero_of_not_mem hnotmem
    simp [h, hcount]

lemma antidiagIndexList_pairwise_lex
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    (antidiagIndexList I).Pairwise (fun x y => toLex x ≤ toLex y) := by
  rw [antidiagIndexList, List.pairwise_ofFn]
  intro i j hij
  exact Prod.Lex.toLex_le_toLex.2
    (Or.inl (I.row.strictMono hij))

lemma antidiagIndexList_nodup
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    (antidiagIndexList I).Nodup := by
  rw [antidiagIndexList, List.nodup_ofFn]
  intro x y hxy
  have hrow : I.row x = I.row y := by
    simpa using congrArg Prod.fst hxy
  exact I.row.injective hrow

lemma mem_indicesOfMonomialExp_of_pos
    {m n : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    {p : Fin m × Fin n}
    (hp : 0 < E p) :
    p ∈ generalizedPermutation.indicesOfMonomialExp E := by
  rw [← List.count_pos_iff]
  simpa [generalizedPermutation.count_indicesOfMonomialExp] using hp

lemma antidiagExp_pos_of_mem_antidiagIndexList
    {m n t : ℕ}
    {I : MinorIndex m n t}
    {p : Fin m × Fin n}
    (hp : p ∈ antidiagIndexList I) :
    0 < antidiagExp I p := by
  rcases p with ⟨a, b⟩
  rw [antidiagExp_apply']
  rw [antidiagIndexList, List.mem_ofFn'] at hp
  rcases hp with ⟨i, hi⟩
  have hrow : I.row i = a := by
    simpa using congrArg Prod.fst hi
  have hcol : I.col i.rev = b := by
    simpa using congrArg Prod.snd hi
  rw [if_pos ⟨i, hrow, hcol⟩]
  norm_num

lemma antidiagIndexList_subperm_indicesOfMonomialExp_of_antidiagExp_le
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hle : antidiagExp I ≤ E) :
    List.Subperm (antidiagIndexList I)
      (generalizedPermutation.indicesOfMonomialExp E) := by
  exact (antidiagIndexList_nodup I).subperm fun p hp =>
    mem_indicesOfMonomialExp_of_pos
      (lt_of_lt_of_le (antidiagExp_pos_of_mem_antidiagIndexList hp) (hle p))

lemma antidiagIndexList_sublist_generalizedPermutation_of_antidiagExp_le
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hle : antidiagExp I ≤ E) :
    List.Sublist (antidiagIndexList I)
      (generalizedPermutation
        (generalizedPermutation.indicesOfMonomialExp E)) := by
  classical
  haveI :
      Std.Antisymm (fun x y : Fin m × Fin n => toLex x ≤ toLex y) :=
    ⟨fun _ _ hxy hyx => (toLex : Fin m × Fin n ≃ Fin m ×ₗ Fin n).injective
      (le_antisymm hxy hyx)⟩
  refine List.sublist_of_subperm_of_pairwise
    (r := fun x y : Fin m × Fin n => toLex x ≤ toLex y)
    ?_ ?_ ?_
  · exact (antidiagIndexList_subperm_indicesOfMonomialExp_of_antidiagExp_le
      (E := E) I hle).trans
      ((generalizedPermutation.generalizedPermutation_perm
        (generalizedPermutation.indicesOfMonomialExp E)).symm.subperm)
  · exact antidiagIndexList_pairwise_lex I
  · exact generalizedPermutation.generalizedPermutation_sorted
      (generalizedPermutation.indicesOfMonomialExp E)

lemma antidiagIndexList_map_snd
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    (antidiagIndexList I).map Prod.snd =
      List.ofFn (fun i : Fin t => I.col i.rev) := by
  simp [antidiagIndexList, List.map_ofFn, Function.comp_def]

lemma antidiagIndexList_lowerWord_sublist_of_antidiagExp_le
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hle : antidiagExp I ≤ E) :
    List.Sublist
      (List.ofFn (fun i : Fin t => I.col i.rev))
      (generalizedPermutation.lowerWord
        (generalizedPermutation.indicesOfMonomialExp E)) := by
  have hsub :=
    (antidiagIndexList_sublist_generalizedPermutation_of_antidiagExp_le
      (E := E) I hle).map Prod.snd
  simpa [generalizedPermutation.lowerWord, antidiagIndexList_map_snd, Function.comp_def] using hsub

lemma antidiagLower_pairwise_gt
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    (List.ofFn (fun i : Fin t => I.col i.rev)).Pairwise (fun a b => a > b) := by
  rw [List.pairwise_ofFn]
  intro i j hij
  exact I.col.strictMono (Fin.rev_lt_rev.mpr hij)

lemma zip_tail_all_gt_of_pairwise_gt
    {n : ℕ}
    {s : List (Fin n)}
    (hs : s.Pairwise (fun a b => a > b)) :
    (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true := by
  induction s with
  | nil =>
      simp
  | cons a s ih =>
      cases s with
      | nil =>
          simp
      | cons b t =>
          have hs' :
              (∀ x ∈ b :: t, a > x) ∧
                (b :: t).Pairwise (fun a b => a > b) := by
            simpa [List.pairwise_cons] using hs
          have hab : a > b := hs'.1 b (by simp)
          have htail : (b :: t).Pairwise (fun a b => a > b) := hs'.2
          simp only [List.tail_cons, List.zip_cons_cons, List.all_cons,
            Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hab, ih htail⟩

lemma length_le_width_of_lowerWord_sublist_pairwise_gt
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {s : List (Fin n)}
    (hsub : List.Sublist s (generalizedPermutation.lowerWord xs))
    (hpair : s.Pairwise (fun a b => a > b)) :
    s.length ≤ generalizedPermutation.width xs := by
  apply generalizedPermutation.length_le_width_of_mem_filtered_sublists
    (xs := xs) (s := s)
  have hs_mem : s ∈ (generalizedPermutation.lowerWord xs).sublists :=
    (List.mem_sublists).2 hsub
  have hall :
      (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true :=
    zip_tail_all_gt_of_pairwise_gt hpair
  simp [hs_mem, hall]

/-!
The generalized-permutation namespace is reopened here for list-width
existence lemmas used in Lemma 6.
-/

namespace generalizedPermutation

lemma exists_mem_of_pos_le_foldl_max_length_aux
    {α : Type*}
    {L : List (List α)}
    {acc t : ℕ}
    (hacc : acc < t)
    (h : t ≤ L.foldl (fun acc s => max acc s.length) acc) :
    ∃ s ∈ L, t ≤ s.length := by
  induction L generalizing acc with
  | nil =>
      simp at h
      omega
  | cons s L ih =>
      simp only [List.foldl_cons] at h
      by_cases hs : t ≤ s.length
      · exact ⟨s, by simp, hs⟩
      · have hmax_lt : max acc s.length < t := by
          rw [Nat.max_lt]
          exact ⟨hacc, Nat.lt_of_not_ge hs⟩
        rcases ih hmax_lt h with ⟨u, huL, htu⟩
        exact ⟨u, by simp [huL], htu⟩

lemma exists_mem_of_pos_le_foldl_max_length
    {α : Type*}
    {L : List (List α)}
    {t : ℕ}
    (ht : 0 < t)
    (h : t ≤ L.foldl (fun acc s => max acc s.length) 0) :
    ∃ s ∈ L, t ≤ s.length :=
  exists_mem_of_pos_le_foldl_max_length_aux ht h

lemma exists_decreasing_sublist_of_le_width
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {t : ℕ}
    (ht : 0 < t)
    (h : t ≤ width xs) :
    ∃ s : List (Fin n),
      List.Sublist s (lowerWord xs) ∧
      (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true ∧
      t ≤ s.length := by
  unfold width at h
  rcases exists_mem_of_pos_le_foldl_max_length (L :=
      (lowerWord xs).sublists.filter
        (fun s : List (Fin n) =>
          (s.zip s.tail).all (fun p => decide (p.1 > p.2)))) ht h with
    ⟨s, hs, hlen⟩
  simp only [List.mem_filter] at hs
  exact ⟨s, (List.mem_sublists).1 hs.1, hs.2, hlen⟩

lemma isChain_gt_of_zip_tail_all_gt
    {n : ℕ}
    {s : List (Fin n)}
    (hall : (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true) :
    s.IsChain (fun a b => a > b) := by
  induction s with
  | nil =>
      simp
  | cons a s ih =>
      cases s with
      | nil =>
          simp
      | cons b t =>
          simp only [List.tail_cons, List.zip_cons_cons, List.all_cons,
            Bool.and_eq_true, decide_eq_true_eq] at hall
          exact List.isChain_cons_cons.2 ⟨hall.1, ih hall.2⟩

lemma pairwise_gt_of_zip_tail_all_gt
    {n : ℕ}
    {s : List (Fin n)}
    (hall : (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true) :
    s.Pairwise (fun a b => a > b) := by
  exact (List.sortedGT_iff_isChain.2
    (isChain_gt_of_zip_tail_all_gt hall)).pairwise

lemma exists_decreasing_sublistLen_of_le_width
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {t : ℕ}
    (ht : 0 < t)
    (h : t ≤ width xs) :
    ∃ s : List (Fin n),
      s.length = t ∧
      List.Sublist s (lowerWord xs) ∧
      s.Pairwise (fun a b => a > b) := by
  rcases exists_decreasing_sublist_of_le_width (xs := xs) ht h with
    ⟨s, hsub, hall, hlen⟩
  refine ⟨s.take t, ?_, ?_, ?_⟩
  · simp [Nat.min_eq_left hlen]
  · exact (List.take_sublist t s).trans hsub
  · exact (pairwise_gt_of_zip_tail_all_gt hall).sublist (List.take_sublist t s)

end generalizedPermutation

lemma exists_antidiagIndexList_sublist_generalizedPermutation_of_le_monomialWidth
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (ht : 0 < t)
    (hwidth : t ≤ monomialWidth E) :
    ∃ I : MinorIndex m n t,
      List.Sublist (antidiagIndexList I)
        (generalizedPermutation
          (generalizedPermutation.indicesOfMonomialExp E)) := by
  classical
  let xs := generalizedPermutation.indicesOfMonomialExp E
  let w := generalizedPermutation xs
  rcases generalizedPermutation.exists_decreasing_sublistLen_of_le_width
      (xs := xs) ht (by simpa [monomialWidth, xs] using hwidth) with
    ⟨s, hs_len, hs_sub, hs_pair⟩
  have hs_sub_map :
      s.Sublist (w.map Prod.snd) := by
    simpa [generalizedPermutation.lowerWord, w, xs] using hs_sub
  rcases List.sublist_map_iff.mp hs_sub_map with ⟨ys, hys_sub, hs_map⟩
  have hys_len : ys.length = t := by
    have hlen := congrArg List.length hs_map
    simpa [hs_len] using hlen.symm
  have hys_sorted : ys.Pairwise (fun x y => toLex x ≤ toLex y) := by
    exact (generalizedPermutation.generalizedPermutation_sorted xs).sublist (by
      simpa [w] using hys_sub)
  have hys_cols_pair :
      ys.Pairwise (fun x y : Fin m × Fin n => x.2 > y.2) := by
    have hmap_pair :
        (ys.map Prod.snd).Pairwise (fun a b => a > b) := by
      simpa [← hs_map] using hs_pair
    simpa [List.pairwise_map] using hmap_pair
  let rowFun : Fin t → Fin m :=
    fun i => (ys.get (i.cast hys_len.symm)).1
  let colFun : Fin t → Fin n :=
    fun i => (ys.get (i.rev.cast hys_len.symm)).2
  have hrow_strict : StrictMono rowFun := by
    intro i j hij
    have hij' : i.cast hys_len.symm < j.cast hys_len.symm := by
      simpa using hij
    have hlex := hys_sorted.rel_get_of_lt hij'
    have hcolgt := hys_cols_pair.rel_get_of_lt hij'
    rcases Prod.Lex.toLex_le_toLex.1 hlex with hrow | hsame
    · simpa [rowFun] using hrow
    · rcases hsame with ⟨_hroweq, hcolle⟩
      exact False.elim ((not_lt_of_ge hcolle) hcolgt)
  have hcol_strict : StrictMono colFun := by
    intro i j hij
    have hrev : j.rev.cast hys_len.symm < i.rev.cast hys_len.symm := by
      simpa using (Fin.rev_lt_rev.mpr hij)
    have hcolgt := hys_cols_pair.rel_get_of_lt hrev
    simpa [colFun] using hcolgt
  let I : MinorIndex m n t :=
    { row := OrderEmbedding.ofStrictMono rowFun hrow_strict
      col := OrderEmbedding.ofStrictMono colFun hcol_strict }
  refine ⟨I, ?_⟩
  have hanti_eq : antidiagIndexList I = ys := by
    apply List.ext_get
    · simp [antidiagIndexList, hys_len]
    · intro i hi₁ hi₂
      have hidx : t - (t - (i + 1) + 1) = i := by
        omega
      simp [antidiagIndexList, I, rowFun, colFun, hidx]
  simpa [hanti_eq, w] using hys_sub

lemma antidiagExp_le_of_antidiagIndexList_sublist_generalizedPermutation
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hsub : List.Sublist (antidiagIndexList I)
      (generalizedPermutation
        (generalizedPermutation.indicesOfMonomialExp E))) :
    antidiagExp I ≤ E := by
  intro p
  have hsubperm :
      List.Subperm (antidiagIndexList I)
        (generalizedPermutation.indicesOfMonomialExp E) :=
    hsub.subperm.trans
      ((generalizedPermutation.generalizedPermutation_perm
        (generalizedPermutation.indicesOfMonomialExp E)).subperm)
  have hcount :
      (antidiagIndexList I).count p ≤
        (generalizedPermutation.indicesOfMonomialExp E).count p :=
    hsubperm.count_le p
  rw [count_antidiagIndexList I p,
    generalizedPermutation.count_indicesOfMonomialExp] at hcount
  exact hcount

lemma antidiagExp_le_monomialWidth
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hle : antidiagExp I ≤ E) :
    t ≤ monomialWidth E := by
  have hsub :=
    antidiagIndexList_lowerWord_sublist_of_antidiagExp_le
      (E := E) I hle
  have hpair := antidiagLower_pairwise_gt I
  have hlen :
      (List.ofFn (fun i : Fin t => I.col i.rev)).length = t := by
    simp
  simpa [monomialWidth, hlen] using
    length_le_width_of_lowerWord_sublist_pairwise_gt
      (xs := generalizedPermutation.indicesOfMonomialExp E)
      hsub hpair

lemma lemma6_forward_exists_antidiagExp_le_width
    {m n r : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (h : ∃ I : MinorIndex m n (r + 1), antidiagExp I ≤ E) :
    r + 1 ≤ monomialWidth E := by
  rcases h with ⟨I, hI⟩
  exact antidiagExp_le_monomialWidth I hI

/-!
This final generalized-permutation block connects exponent vectors to
`1 × 1`-minor bitableaux for the KRS and Hilbert-function arguments.
-/

namespace generalizedPermutation

/-- The `1 × 1`-minor bitableau attached to a monomial exponent vector. -/
noncomputable def bitableauOfMonomialExp {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) :
    YoungBitableau m n :=
  let w := generalizedPermutation (indicesOfMonomialExp E)
  { v := w.length
    size := fun _ => 1
    size_pos := by
      intro a
      decide
    minorindex := fun a =>
      { row :=
          OrderEmbedding.ofStrictMono
            (fun _ : Fin 1 => (w.get a).1)
            (by
              intro i j h
              fin_cases i
              fin_cases j
              simp at h)
        col :=
          OrderEmbedding.ofStrictMono
            (fun _ : Fin 1 => (w.get a).2)
            (by
              intro i j h
              fin_cases i
              fin_cases j
              simp at h) }
    shape_antitone := by
      intro a b h
      simp }

lemma width_indicesOfMonomialExp_eq_one_iff_bitableauOfMonomialExp_isStandard
    {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ)
    (hE : indicesOfMonomialExp E ≠ []) :
    width (indicesOfMonomialExp E) = 1
      ↔
    YoungBitableau.IsStandard
        (bitableauOfMonomialExp E) := by
  rw [width_eq_one_iff_lowerWord_pairwise_le (lowerWord_ne_nil_of_ne_nil hE)]
  constructor
  · intro hlower a b hnext j
    fin_cases j
    let xs := indicesOfMonomialExp E
    let w := generalizedPermutation xs
    have hab : a < b := by
      rw [Fin.lt_def]
      omega
    have hlex :
        toLex (w.get a) ≤ toLex (w.get b) := by
      simpa [xs, w, bitableauOfMonomialExp] using
        (generalizedPermutation_sorted xs).rel_get_of_lt hab
    have hrow : (w.get a).1 ≤ (w.get b).1 :=
      (Prod.Lex.toLex_le_toLex'.mp hlex).1
    have hcol : (w.get a).2 ≤ (w.get b).2 := by
      have ha_w : a.val < w.length := by
        simp [xs, w, bitableauOfMonomialExp]
      have hb_w : b.val < w.length := by
        simp [xs, w, bitableauOfMonomialExp]
      let a' : Fin (w.map fun x => x.2).length :=
        ⟨a.val, by rw [List.length_map]; exact ha_w⟩
      let b' : Fin (w.map fun x => x.2).length :=
        ⟨b.val, by rw [List.length_map]; exact hb_w⟩
      have hab' : a' < b' := by
        rw [Fin.lt_def]
        exact Fin.lt_def.mp hab
      have hget :
          (w.map fun x => x.2).get a' ≤
            (w.map fun x => x.2).get b' := by
        have hlower' :
            (w.map fun x => x.2).Pairwise (fun a b => a ≤ b) := by
          simpa [lowerWord, xs, w] using hlower
        exact hlower'.rel_get_of_lt hab'
      simpa only [a', b', List.get_eq_getElem, List.getElem_map] using hget
    simpa [bitableauOfMonomialExp, xs, w] using And.intro hrow hcol
  · intro hstandard
    rw [← List.isChain_iff_pairwise]
    rw [List.isChain_iff_getElem]
    intro i hi
    let xs := indicesOfMonomialExp E
    let w := generalizedPermutation xs
    have hi_w : i + 1 < w.length := by
      have hi_xs : i + 1 < xs.length := by
        have hlen :
            (lowerWord (indicesOfMonomialExp E)).length = xs.length := by
          simpa [xs] using lowerWord_length (indicesOfMonomialExp E)
        rwa [hlen] at hi
      have hwlen : w.length = xs.length := by
        simpa [w] using (generalizedPermutation_perm xs).length_eq
      simpa [hwlen] using hi_xs
    let a : Fin (bitableauOfMonomialExp E).v := by
      refine ⟨i, ?_⟩
      simpa [bitableauOfMonomialExp, xs, w] using Nat.lt_of_succ_lt hi_w
    let b : Fin (bitableauOfMonomialExp E).v := by
      refine ⟨i + 1, ?_⟩
      simpa [bitableauOfMonomialExp, xs, w] using hi_w
    have hnext : a.val + 1 = b.val := rfl
    have hcol := (hstandard a b hnext ⟨0, (bitableauOfMonomialExp E).size_pos b⟩).2
    simpa [bitableauOfMonomialExp, xs, w, lowerWord, a, b, List.get_eq_getElem] using hcol

end generalizedPermutation

/-! ## Minor-index order and content for straightening -/

namespace MinorIndex

/-- The partial order on minor indices used in the straightening law:
`I ≤ J` means `I` has at least as many rows/columns as `J`, and its first
`J` entries are componentwise no larger. -/
def PairLE {m n p q : ℕ} (I : MinorIndex m n p) (J : MinorIndex m n q) : Prop :=
  ∃ hpq : q ≤ p,
    ∀ j : Fin q,
      I.row ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.row j ∧
      I.col ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.col j

/-- Strict version of the straightening-law order on minor indices. -/
def PairLT {m n p q : ℕ} (I : MinorIndex m n p) (J : MinorIndex m n q) : Prop :=
  PairLE I J ∧ ¬ PairLE J I

lemma PairLE.of_components {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hpq : q ≤ p)
    (h :
      ∀ j : Fin q,
        I.row ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.row j ∧
        I.col ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.col j) :
    PairLE I J :=
  ⟨hpq, h⟩

lemma PairLE.refl {m n p : ℕ} (I : MinorIndex m n p) : PairLE I I := by
  refine ⟨le_rfl, ?_⟩
  intro j
  constructor <;> rfl

lemma PairLE.size_le {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (h : PairLE I J) : q ≤ p :=
  h.1

lemma PairLE.row_le {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (h : PairLE I J) (j : Fin q) :
    I.row ⟨j.val, lt_of_lt_of_le j.isLt h.size_le⟩ ≤ J.row j :=
  (h.2 j).1

lemma PairLE.col_le {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (h : PairLE I J) (j : Fin q) :
    I.col ⟨j.val, lt_of_lt_of_le j.isLt h.size_le⟩ ≤ J.col j :=
  (h.2 j).2

lemma PairLE.trans {m n p q r : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q} {K : MinorIndex m n r}
    (hIJ : PairLE I J) (hJK : PairLE J K) : PairLE I K := by
  refine ⟨le_trans hJK.size_le hIJ.size_le, ?_⟩
  intro x
  have hrowIJ := hIJ.row_le ⟨x.val, lt_of_lt_of_le x.isLt hJK.size_le⟩
  have hrowJK := hJK.row_le x
  have hcolIJ := hIJ.col_le ⟨x.val, lt_of_lt_of_le x.isLt hJK.size_le⟩
  have hcolJK := hJK.col_le x
  constructor
  · exact le_trans (by simpa using hrowIJ) hrowJK
  · exact le_trans (by simpa using hcolIJ) hcolJK

lemma PairLT.pairLE {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (h : PairLT I J) : PairLE I J :=
  h.1

lemma PairLT.not_pairLE_symm {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (h : PairLT I J) : ¬ PairLE J I :=
  h.2

lemma PairLT.of_pairLE_not_symm {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hIJ : PairLE I J) (hJI : ¬ PairLE J I) : PairLT I J :=
  ⟨hIJ, hJI⟩

lemma PairLT.irrefl {m n p : ℕ} (I : MinorIndex m n p) : ¬ PairLT I I := by
  intro h
  exact h.not_pairLE_symm (PairLE.refl I)

lemma PairLT.trans {m n p q r : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q} {K : MinorIndex m n r}
    (hIJ : PairLT I J) (hJK : PairLT J K) : PairLT I K := by
  refine ⟨PairLE.trans hIJ.pairLE hJK.pairLE, ?_⟩
  intro hKI
  exact hJK.not_pairLE_symm (PairLE.trans hKI hIJ.pairLE)

lemma not_pairLE_of_size_lt {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hpq : p < q) : ¬ PairLE I J := by
  intro h
  exact not_le_of_gt hpq h.size_le

lemma not_pairLE_of_violation {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hpq : q ≤ p) (j : Fin q)
    (hj :
      ¬
        (I.row ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.row j ∧
         I.col ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.col j)) :
    ¬ PairLE I J := by
  intro h
  have hhpq : h.size_le = hpq := Subsingleton.elim _ _
  cases hhpq
  exact hj (h.2 j)

lemma not_pairLE_iff {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    ¬ PairLE I J ↔
      p < q ∨
        ∃ (hpq : q ≤ p) (j : Fin q),
          ¬
            (I.row ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.row j ∧
             I.col ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.col j) := by
  constructor
  · intro h
    by_cases hpq : q ≤ p
    · right
      by_contra hbad
      push_neg at hbad
      exact h ⟨hpq, hbad hpq⟩
    · left
      omega
  · rintro (hpq | hbad)
    · exact not_pairLE_of_size_lt hpq
    · rcases hbad with ⟨hpq, j, hj⟩
      exact not_pairLE_of_violation hpq j hj

lemma exists_violation_of_not_pairLE_of_size_le {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hpq : q ≤ p) (h : ¬ PairLE I J) :
    ∃ j : Fin q,
      ¬
        (I.row ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.row j ∧
         I.col ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.col j) := by
  by_contra hbad
  push_neg at hbad
  exact h ⟨hpq, hbad⟩

lemma not_pairLE_or_violation {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (h : ¬ PairLE I J) :
    p < q ∨
      ∃ (hpq : q ≤ p) (j : Fin q),
        ¬
          (I.row ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.row j ∧
           I.col ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.col j) :=
  (not_pairLE_iff I J).mp h

lemma incomparable_pairLE_cases {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hIJ : ¬ PairLE I J) (hJI : ¬ PairLE J I) :
    (p < q ∨
      ∃ (hpq : q ≤ p) (j : Fin q),
        ¬
          (I.row ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.row j ∧
           I.col ⟨j.val, lt_of_lt_of_le j.isLt hpq⟩ ≤ J.col j))
      ∧
    (q < p ∨
      ∃ (hqp : p ≤ q) (i : Fin p),
        ¬
          (J.row ⟨i.val, lt_of_lt_of_le i.isLt hqp⟩ ≤ I.row i ∧
           J.col ⟨i.val, lt_of_lt_of_le i.isLt hqp⟩ ≤ I.col i)) := by
  exact ⟨not_pairLE_or_violation hIJ, not_pairLE_or_violation hJI⟩

end MinorIndex

/-- Standard Young bitableaux, as used in Proposition 2 and the straightening law. -/
abbrev StandardYoungBitableau (m n : ℕ) :=
  { B : YoungBitableau m n // YoungBitableau.IsStandard B }

/-- Standard Young bitableaux of length at most `r`. -/
abbrev StandardYoungBitableauOfLengthLE (m n r : ℕ) :=
  { B : StandardYoungBitableau m n // YoungBitableau.length B.1 ≤ r }

/-! ## Raw two-minor reshuffles and Swan-Laplace infrastructure -/

namespace SwanLaplace

/-- The alternating minor map obtained by restricting row vectors to an
ordered set of column slots. -/
noncomputable def coordinateMinorAlternating
    {R : Type*} [CommRing R] {N r : ℕ}
    (s : Finset (Fin N)) (hcard : s.card = r) :
    (Fin N → R) [⋀^Fin r]→ₗ[R] R :=
  Matrix.detRowAlternating.compLinearMap
    (LinearMap.pi fun i : Fin r => LinearMap.proj (s.orderEmbOfFin hcard i))

lemma coordinateMinorAlternating_apply
    {R : Type*} [CommRing R] {N r : ℕ}
    (s : Finset (Fin N)) (hcard : s.card = r)
    (v : Fin r → Fin N → R) :
    coordinateMinorAlternating s hcard v =
      Matrix.det (fun i j => v i (s.orderEmbOfFin hcard j)) := by
  rfl

/-- Exterior-product form of the generalized Laplace expansion along a fixed
set of column slots. -/
noncomputable def coordinateLaplaceAlternating
    {R : Type*} [CommRing R] {N r : ℕ}
    (s : Finset (Fin N)) (hcard : s.card = r) :
    (Fin N → R) [⋀^Sum (Fin r) (Fin (N - r))]→ₗ[R] R :=
  (LinearMap.mul' R R).compAlternatingMap
    ((coordinateMinorAlternating s hcard).domCoprod
      (coordinateMinorAlternating sᶜ (by
        rw [Finset.card_compl, Fintype.card_fin, hcard])))

lemma coordinateLaplaceAlternating_apply
    {R : Type*} [CommRing R] {N r : ℕ}
    (s : Finset (Fin N)) (hcard : s.card = r)
    (v : Sum (Fin r) (Fin (N - r)) → Fin N → R) :
    coordinateLaplaceAlternating s hcard v =
      ∑ σ : Equiv.Perm.ModSumCongr (Fin r) (Fin (N - r)),
        (LinearMap.mul' R R)
          (AlternatingMap.domCoprod.summand
            (coordinateMinorAlternating s hcard)
            (coordinateMinorAlternating sᶜ (by
              rw [Finset.card_compl, Fintype.card_fin, hcard]))
            σ v) := by
  simp [coordinateLaplaceAlternating, AlternatingMap.domCoprod_apply,
    map_sum]

end SwanLaplace

namespace RawMinorPair

/-- A redistribution of all row/column slots of a raw two-minor product into
new left/right factors.  The new left factor has size `r`; the new right factor
has the complementary size.  The equivalence is the bookkeeping that every old
slot is used exactly once. -/
structure Reshuffle {m n : ℕ} (P : RawMinorPair m n) where
  r : ℕ
  hle : r ≤ P.p + P.q
  equiv :
    Sum (Fin r) (Fin (P.p + P.q - r)) ≃
      Sum (Fin P.p) (Fin P.q)

namespace Reshuffle

noncomputable def id {m n : ℕ} (P : RawMinorPair m n) :
    Reshuffle P where
  r := P.p
  hle := Nat.le_add_right P.p P.q
  equiv :=
    let h : P.p + P.q - P.p = P.q := by omega
    Equiv.sumCongr (Equiv.refl (Fin P.p)) (Equiv.cast (by rw [h]))

def toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : Reshuffle P) : RawMinorPair m n where
  p := E.r
  q := P.p + P.q - E.r
  left :=
    { row := fun i => P.slotRow (E.equiv (Sum.inl i))
      col := fun i => P.slotCol (E.equiv (Sum.inl i)) }
  right :=
    { row := fun j => P.slotRow (E.equiv (Sum.inr j))
      col := fun j => P.slotCol (E.equiv (Sum.inr j)) }

lemma rowContent_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : Reshuffle P) :
    RawMinorPair.rowContent E.toPair = RawMinorPair.rowContent P := by
  classical
  rw [RawMinorPair.rowContent_eq_sum_slots,
    RawMinorPair.rowContent_eq_sum_slots]
  have hleft :
      (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          Finsupp.single (E.toPair.slotRow s) 1) =
        ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          Finsupp.single (P.slotRow (E.equiv s)) 1 := by
    apply Finset.sum_congr rfl
    intro s _hs
    cases s <;> rfl
  calc
    (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        Finsupp.single (E.toPair.slotRow s) 1)
        =
      ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        Finsupp.single (P.slotRow (E.equiv s)) 1 := hleft
    _ =
      ∑ s : Sum (Fin P.p) (Fin P.q),
        Finsupp.single (P.slotRow s) 1 := by
        simpa using
          (Fintype.sum_equiv E.equiv
            (fun s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)) =>
              Finsupp.single (P.slotRow (E.equiv s)) 1)
            (fun s : Sum (Fin P.p) (Fin P.q) =>
              Finsupp.single (P.slotRow s) 1)
            (by intro s; rfl))

lemma colContent_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : Reshuffle P) :
    RawMinorPair.colContent E.toPair = RawMinorPair.colContent P := by
  classical
  rw [RawMinorPair.colContent_eq_sum_slots,
    RawMinorPair.colContent_eq_sum_slots]
  have hleft :
      (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          Finsupp.single (E.toPair.slotCol s) 1) =
        ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          Finsupp.single (P.slotCol (E.equiv s)) 1 := by
    apply Finset.sum_congr rfl
    intro s _hs
    cases s <;> rfl
  calc
    (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        Finsupp.single (E.toPair.slotCol s) 1)
        =
      ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        Finsupp.single (P.slotCol (E.equiv s)) 1 := hleft
    _ =
      ∑ s : Sum (Fin P.p) (Fin P.q),
        Finsupp.single (P.slotCol s) 1 := by
        simpa using
          (Fintype.sum_equiv E.equiv
            (fun s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)) =>
              Finsupp.single (P.slotCol (E.equiv s)) 1)
            (fun s : Sum (Fin P.p) (Fin P.q) =>
              Finsupp.single (P.slotCol s) 1)
            (by intro s; rfl))

lemma id_toPair_left_row {m n : ℕ} (P : RawMinorPair m n) :
    (Reshuffle.id P).toPair.left.row = P.left.row := by
  funext i
  rfl

lemma id_toPair_left_col {m n : ℕ} (P : RawMinorPair m n) :
    (Reshuffle.id P).toPair.left.col = P.left.col := by
  funext i
  rfl

noncomputable def code {m n : ℕ} {P : RawMinorPair m n}
    (E : Reshuffle P) :
    Sigma (fun r : Fin (P.p + P.q + 1) =>
      Sum (Fin r.1) (Fin (P.p + P.q - r.1)) ≃
        Sum (Fin P.p) (Fin P.q)) :=
  ⟨⟨E.r, Nat.lt_succ_of_le E.hle⟩, E.equiv⟩

lemma code_injective {m n : ℕ} {P : RawMinorPair m n} :
    Function.Injective (Reshuffle.code (P := P)) := by
  intro E E' h
  cases E with
  | mk r hle equiv =>
      cases E' with
      | mk r' hle' equiv' =>
          simp only [code, Sigma.mk.injEq, Fin.mk.injEq] at h
          rcases h with ⟨hr, hequiv⟩
          subst hr
          cases hequiv
          rfl

instance instFinite {m n : ℕ} {P : RawMinorPair m n} :
    Finite (Reshuffle P) := by
  classical
  exact Finite.of_injective (Reshuffle.code (P := P)) Reshuffle.code_injective

noncomputable instance instFintype {m n : ℕ} {P : RawMinorPair m n} :
    Fintype (Reshuffle P) := by
  classical
  exact Fintype.ofFinite (Reshuffle P)

end Reshuffle

/-- A two-sided redistribution of a raw two-minor product.

For Swan's Laplace relations the new row split and the new column split vary
independently.  This is why `BiReshuffle` has separate equivalences for row
slots and column slots, unlike `Reshuffle` above. -/
structure BiReshuffle {m n : ℕ} (P : RawMinorPair m n) where
  r : ℕ
  hle : r ≤ P.p + P.q
  rowEquiv :
    Sum (Fin r) (Fin (P.p + P.q - r)) ≃
      Sum (Fin P.p) (Fin P.q)
  colEquiv :
    Sum (Fin r) (Fin (P.p + P.q - r)) ≃
      Sum (Fin P.p) (Fin P.q)

namespace BiReshuffle

noncomputable def equivPermSign
    {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) : R :=
  (((Equiv.Perm.sign e : ℤˣ) : ℤ) : R)

@[simp] lemma equivPermSign_one
    {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α] :
    equivPermSign (R := R) (1 : Equiv.Perm α) = 1 := by
  simp [equivPermSign]

@[simp] lemma equivPermSign_trans
    {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α]
    (e f : Equiv.Perm α) :
    equivPermSign (R := R) (e.trans f) =
      equivPermSign (R := R) f * equivPermSign (R := R) e := by
  simp [equivPermSign, Equiv.Perm.sign_trans]

@[simp] lemma equivPermSign_symm
    {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) :
    equivPermSign (R := R) e.symm = equivPermSign (R := R) e := by
  simp [equivPermSign, Equiv.Perm.sign_symm]

@[simp] lemma equivPermSign_sumCongr
    {R : Type*} [CommRing R]
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : Equiv.Perm α) (f : Equiv.Perm β) :
    equivPermSign (R := R) (e.sumCongr f) =
      equivPermSign (R := R) e * equivPermSign (R := R) f := by
  simp [equivPermSign, Equiv.Perm.sign_sumCongr]

lemma equivPermSign_mul_self
    {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) :
    equivPermSign (R := R) e * equivPermSign (R := R) e = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;>
    simp [equivPermSign, h]

noncomputable def finSumFinEquivToTotal (N r : ℕ) (hle : r ≤ N) :
    Fin r ⊕ Fin (N - r) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hle))

noncomputable def id {m n : ℕ} (P : RawMinorPair m n) :
    BiReshuffle P where
  r := P.p
  hle := Nat.le_add_right P.p P.q
  rowEquiv :=
    let h : P.p + P.q - P.p = P.q := by omega
    Equiv.sumCongr (Equiv.refl (Fin P.p)) (Equiv.cast (by rw [h]))
  colEquiv :=
    let h : P.p + P.q - P.p = P.q := by omega
    Equiv.sumCongr (Equiv.refl (Fin P.p)) (Equiv.cast (by rw [h]))

/-- The canonical bi-reshuffle attached to two equally sized sets of row and
column slots.  The selected slots form the new left factor; their complements
form the new right factor.  Both blocks are enumerated in the ambient slot
order, so this construction does not introduce the block-permutation
multiplicities present in an arbitrary `BiReshuffle`. -/
noncomputable def ofFinsets {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) :
    BiReshuffle P where
  r := rowSlots.card
  hle := by
    simpa using Finset.card_le_univ rowSlots
  rowEquiv :=
    (finSumEquivOfFinset rfl (by
      rw [Finset.card_compl, Fintype.card_fin])).trans finSumFinEquiv.symm
  colEquiv :=
    (finSumEquivOfFinset hcard.symm (by
      rw [Finset.card_compl, Fintype.card_fin, hcard])).trans finSumFinEquiv.symm

@[simp] lemma ofFinsets_r {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) :
    (ofFinsets P rowSlots colSlots hcard).r = rowSlots.card := rfl

@[simp] lemma ofFinsets_rowEquiv_inl {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) (i : Fin rowSlots.card) :
    (ofFinsets P rowSlots colSlots hcard).rowEquiv (Sum.inl i) =
      finSumFinEquiv.symm (rowSlots.orderEmbOfFin rfl i) := by
  simp [ofFinsets]

@[simp] lemma ofFinsets_colEquiv_inl {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) (i : Fin rowSlots.card) :
    (ofFinsets P rowSlots colSlots hcard).colEquiv (Sum.inl i) =
      finSumFinEquiv.symm (colSlots.orderEmbOfFin hcard.symm i) := by
  simp [ofFinsets]

@[simp] lemma ofFinsets_rowEquiv_inr {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card)
    (i : Fin (P.p + P.q - rowSlots.card)) :
    (ofFinsets P rowSlots colSlots hcard).rowEquiv (Sum.inr i) =
      finSumFinEquiv.symm
        (rowSlotsᶜ.orderEmbOfFin (by
          rw [Finset.card_compl, Fintype.card_fin]) i) := by
  simp [ofFinsets]

@[simp] lemma ofFinsets_colEquiv_inr {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card)
    (i : Fin (P.p + P.q - rowSlots.card)) :
    (ofFinsets P rowSlots colSlots hcard).colEquiv (Sum.inr i) =
      finSumFinEquiv.symm
        (colSlotsᶜ.orderEmbOfFin (by
          rw [Finset.card_compl, Fintype.card_fin, hcard]) i) := by
  simp [ofFinsets]

/-- Slots occupied by the original left factor, viewed in the common ordered
slot set `Fin (P.p + P.q)`. -/
def leftSlotFinset {m n : ℕ} (P : RawMinorPair m n) :
    Finset (Fin (P.p + P.q)) :=
  Finset.univ.map (Fin.castAddEmb P.q)

@[simp] lemma card_leftSlotFinset {m n : ℕ} (P : RawMinorPair m n) :
    (leftSlotFinset P).card = P.p := by
  simp [leftSlotFinset]

@[simp] lemma mem_leftSlotFinset_castAdd {m n : ℕ} (P : RawMinorPair m n)
    (i : Fin P.p) :
    Fin.castAdd P.q i ∈ leftSlotFinset P := by
  simp [leftSlotFinset]

lemma leftSlotFinset_orderEmbOfFin {m n : ℕ} (P : RawMinorPair m n)
    (i : Fin P.p) :
    (leftSlotFinset P).orderEmbOfFin (card_leftSlotFinset P) i =
      Fin.castAdd P.q i := by
  classical
  have h :
      (fun i : Fin P.p => Fin.castAdd P.q i) =
        (leftSlotFinset P).orderEmbOfFin (card_leftSlotFinset P) := by
    refine Finset.orderEmbOfFin_unique (s := leftSlotFinset P)
      (h := card_leftSlotFinset P) ?_ (Fin.strictMono_castAdd P.q)
    intro i
    exact mem_leftSlotFinset_castAdd P i
  exact congrFun h.symm i

lemma leftSlotFinset_orderEmbOfFin_cast {m n : ℕ} (P : RawMinorPair m n)
    {r : ℕ} (hcard : (leftSlotFinset P).card = r)
    (hr : r = P.p) (i : Fin r) :
    (leftSlotFinset P).orderEmbOfFin hcard i =
      Fin.castAdd P.q (Fin.cast hr i) := by
  subst hr
  simpa using leftSlotFinset_orderEmbOfFin P i

lemma leftSlotFinset_compl_orderEmbOfFin {m n : ℕ} (P : RawMinorPair m n)
    (hcard : (leftSlotFinset P)ᶜ.card = P.q) (j : Fin P.q) :
    ((leftSlotFinset P)ᶜ).orderEmbOfFin hcard j =
      Fin.natAdd P.p j := by
  classical
  have h :
      (fun j : Fin P.q => Fin.natAdd P.p j) =
        ((leftSlotFinset P)ᶜ).orderEmbOfFin hcard := by
    refine Finset.orderEmbOfFin_unique (s := (leftSlotFinset P)ᶜ)
      (h := hcard) ?_ (Fin.strictMono_natAdd P.p)
    intro j
    simp only [leftSlotFinset, Fin.natAdd, Finset.mem_compl, Finset.mem_map, Finset.mem_univ,
      Fin.coe_castAddEmb, Fin.castAdd, Fin.ext_iff, Fin.val_castLE, true_and, not_exists]
    intro x hx
    have hxlt : x.val < P.p := x.isLt
    omega
  exact congrFun h.symm j

lemma card_leftSlotFinset_compl {m n : ℕ} (P : RawMinorPair m n) :
    (leftSlotFinset P)ᶜ.card = P.q := by
  rw [Finset.card_compl, Fintype.card_fin, card_leftSlotFinset]
  omega

lemma leftSlotFinset_ne_univ_of_right_pos {m n : ℕ}
    (P : RawMinorPair m n) (hq : 0 < P.q) :
    leftSlotFinset P ≠ Finset.univ := by
  intro h
  have hcard := congrArg Finset.card h
  simp [card_leftSlotFinset] at hcard
  omega

def permPreimageLeftSlotFinset {m n : ℕ} (P : RawMinorPair m n)
    (π : Equiv.Perm (Fin (P.p + P.q))) :
    Finset (Fin (P.p + P.q)) :=
  (leftSlotFinset P).map π.symm.toEmbedding

@[simp] lemma card_permPreimageLeftSlotFinset {m n : ℕ}
    (P : RawMinorPair m n) (π : Equiv.Perm (Fin (P.p + P.q))) :
    (permPreimageLeftSlotFinset P π).card = P.p := by
  simp [permPreimageLeftSlotFinset]

lemma mem_permPreimageLeftSlotFinset_iff {m n : ℕ}
    (P : RawMinorPair m n) (π : Equiv.Perm (Fin (P.p + P.q)))
    (x : Fin (P.p + P.q)) :
    x ∈ permPreimageLeftSlotFinset P π ↔ π x ∈ leftSlotFinset P := by
  classical
  simp [permPreimageLeftSlotFinset]

lemma leftSlotFinset_union_permPreimageLeftSlotFinset_ne_univ_of_two_mul_lt
    {m n : ℕ} (P : RawMinorPair m n)
    (hcard : 2 * P.p < P.p + P.q)
    (π : Equiv.Perm (Fin (P.p + P.q))) :
    leftSlotFinset P ∪ permPreimageLeftSlotFinset P π ≠ Finset.univ := by
  classical
  intro h
  have hle :
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π).card ≤ 2 * P.p := by
    calc
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π).card
          ≤ (leftSlotFinset P).card + (permPreimageLeftSlotFinset P π).card :=
            Finset.card_union_le _ _
      _ = 2 * P.p := by simp [two_mul]
  have huniv :
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π).card = P.p + P.q := by
    simp [h]
  omega

lemma sum_Icc_leftSlotFinset_union_permPreimage_neg_one_pow_card_compl_eq_zero
    {m n : ℕ} (k : Type*) [CommRing k]
    (P : RawMinorPair m n)
    (hcard : 2 * P.p < P.p + P.q)
    (π : Equiv.Perm (Fin (P.p + P.q))) :
    (∑ s ∈ Finset.Icc
        (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π) Finset.univ,
      (-1 : k) ^ sᶜ.card) = 0 := by
  exact Finset.sum_Icc_neg_one_pow_card_compl_eq_zero
    (s := leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
    (R := k)
    (leftSlotFinset_union_permPreimageLeftSlotFinset_ne_univ_of_two_mul_lt
      P hcard π)

lemma sum_Icc_leftSlotFinset_neg_one_pow_card_compl_eq_zero
    {m n : ℕ} {k : Type*} [CommRing k]
    (P : RawMinorPair m n) (hq : 0 < P.q) :
    (∑ s ∈ Finset.Icc (leftSlotFinset P) Finset.univ,
      (-1 : k) ^ sᶜ.card) = 0 := by
  exact Finset.sum_Icc_neg_one_pow_card_compl_eq_zero
    (s := leftSlotFinset P) (R := k)
    (leftSlotFinset_ne_univ_of_right_pos P hq)

lemma leftSlotFinset_compl_orderEmbOfFin_cast {m n : ℕ} (P : RawMinorPair m n)
    {r : ℕ} (hcard : (leftSlotFinset P)ᶜ.card = r)
    (hr : r = P.q) (j : Fin r) :
    ((leftSlotFinset P)ᶜ).orderEmbOfFin hcard j =
      Fin.natAdd P.p (Fin.cast hr j) := by
  subst hr
  simpa using leftSlotFinset_compl_orderEmbOfFin P hcard j

namespace Hodge

/-- The initial segment of the original right slots up to the Hodge bad
position.  These are Swan's `j₁,...,jν`. -/
def rightPrefix {m n : ℕ} (P : RawMinorPair m n) (ν : Fin P.q) :
    Finset (Fin (P.p + P.q)) :=
  (Finset.univ.filter fun μ : Fin P.q => μ ≤ ν).map (Fin.natAddEmb P.p)

/-- The final segment of the original left slots starting at the Hodge bad
position.  These are Swan's `iν,...,ip`. -/
def leftSuffix {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (_hνp : ν.val < P.p) :
    Finset (Fin (P.p + P.q)) :=
  (Finset.univ.filter fun i : Fin P.p => ν.val ≤ i.val).map (Fin.castAddEmb P.q)

/-- The initial segment of the original left slots up to a fixed left
position. -/
def leftPrefix {m n : ℕ} (P : RawMinorPair m n) (i : Fin P.p) :
    Finset (Fin (P.p + P.q)) :=
  (Finset.univ.filter fun a : Fin P.p => a ≤ i).map (Fin.castAddEmb P.q)

/-- The strict initial segment of the original left slots before the Hodge bad
position. -/
def leftBefore {m n : ℕ} (P : RawMinorPair m n) (ν : Fin P.q) :
    Finset (Fin (P.p + P.q)) :=
  (Finset.univ.filter fun i : Fin P.p => i.val < ν.val).map (Fin.castAddEmb P.q)

/-- The strict tail of the original left slots after a fixed left position. -/
def leftAfter {m n : ℕ} (P : RawMinorPair m n) (i : Fin P.p) :
    Finset (Fin (P.p + P.q)) :=
  (Finset.univ.filter fun a : Fin P.p => i < a).map (Fin.castAddEmb P.q)

/-- Swan's `D = B ∪ {j₁,...,jν}` in ambient slot form. -/
def hodgeD {m n : ℕ} (P : RawMinorPair m n) (ν : Fin P.q) :
    Finset (Fin (P.p + P.q)) :=
  leftSlotFinset P ∪ rightPrefix P ν

/-- Swan's `C = {j₁,...,jν,iν,...,ip}` in ambient slot form. -/
def hodgeC {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    Finset (Fin (P.p + P.q)) :=
  rightPrefix P ν ∪ leftSuffix P ν hνp

lemma rightPrefix_subset_hodgeD {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    rightPrefix P ν ⊆ hodgeD P ν := by
  intro x hx
  exact Finset.mem_union_right (leftSlotFinset P) hx

lemma rightPrefix_subset_hodgeC {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    rightPrefix P ν ⊆ hodgeC P ν hνp := by
  intro x hx
  exact Finset.mem_union_left (leftSuffix P ν hνp) hx

lemma leftSlotFinset_subset_hodgeD {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    leftSlotFinset P ⊆ hodgeD P ν := by
  intro x hx
  exact Finset.mem_union_left (rightPrefix P ν) hx

lemma rightPrefix_disjoint_leftSlotFinset {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    Disjoint (rightPrefix P ν) (leftSlotFinset P) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxright hxleft
  rcases Finset.mem_map.mp hxright with ⟨μ, _hμ, hμx⟩
  rcases Finset.mem_map.mp hxleft with ⟨i, _hi, hix⟩
  have hval :
      (Fin.natAdd P.p μ).val = (Fin.castAdd P.q i).val := by
    have hfin : Fin.natAdd P.p μ = Fin.castAdd P.q i := by
      simpa using hμx.trans hix.symm
    exact congrArg Fin.val hfin
  simp [Fin.natAdd, Fin.castAdd] at hval
  omega

lemma leftSlotFinset_disjoint_rightPrefix {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    Disjoint (leftSlotFinset P) (rightPrefix P ν) :=
  (rightPrefix_disjoint_leftSlotFinset P ν).symm

lemma leftSuffix_subset_leftSlotFinset {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    leftSuffix P ν hνp ⊆ leftSlotFinset P := by
  classical
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨i, _hi, hix⟩
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hix⟩

@[simp] lemma card_leftPrefix {m n : ℕ}
    (P : RawMinorPair m n) (i : Fin P.p) :
    (leftPrefix P i).card = i.val + 1 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin P.p => a ≤ i) =
        Finset.Iic i := by
    ext a
    simp
  rw [leftPrefix, hfilter]
  simp

lemma leftPrefix_subset_leftSlotFinset {m n : ℕ}
    (P : RawMinorPair m n) (i : Fin P.p) :
    leftPrefix P i ⊆ leftSlotFinset P := by
  classical
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨a, _ha, hax⟩
  exact Finset.mem_map.mpr ⟨a, Finset.mem_univ _, hax⟩

@[simp] lemma card_leftBefore {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (leftBefore P ν).card = ν.val := by
  classical
  let a : Fin P.p := ⟨ν.val, hνp⟩
  have hfilter :
      (Finset.univ.filter fun i : Fin P.p => i.val < ν.val) =
        Finset.Iio a := by
    ext i
    simp [a, Fin.lt_def]
  rw [leftBefore, hfilter]
  simp [a]

lemma leftBefore_subset_leftSlotFinset {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    leftBefore P ν ⊆ leftSlotFinset P := by
  classical
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨a, _ha, hax⟩
  exact Finset.mem_map.mpr ⟨a, Finset.mem_univ _, hax⟩

lemma leftPrefix_subset_hodgeD {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (i : Fin P.p) :
    leftPrefix P i ⊆ hodgeD P ν := by
  intro x hx
  exact leftSlotFinset_subset_hodgeD P ν
    (leftPrefix_subset_leftSlotFinset P i hx)

lemma leftBefore_subset_hodgeD {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    leftBefore P ν ⊆ hodgeD P ν := by
  intro x hx
  exact leftSlotFinset_subset_hodgeD P ν
    (leftBefore_subset_leftSlotFinset P ν hx)

lemma leftPrefix_disjoint_rightPrefix {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (i : Fin P.p) :
    Disjoint (leftPrefix P i) (rightPrefix P ν) :=
  (leftSlotFinset_disjoint_rightPrefix P ν).mono_left
    (leftPrefix_subset_leftSlotFinset P i)

lemma leftBefore_disjoint_rightPrefix {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    Disjoint (leftBefore P ν) (rightPrefix P ν) :=
  (leftSlotFinset_disjoint_rightPrefix P ν).mono_left
    (leftBefore_subset_leftSlotFinset P ν)

lemma leftBefore_disjoint_leftSuffix {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    Disjoint (leftBefore P ν) (leftSuffix P ν hνp) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxBefore hxSuffix
  rcases Finset.mem_map.mp hxBefore with ⟨a, ha, hax⟩
  rcases Finset.mem_map.mp hxSuffix with ⟨b, hb, hbx⟩
  have haν : a.val < ν.val := (Finset.mem_filter.mp ha).2
  have hνb : ν.val ≤ b.val := (Finset.mem_filter.mp hb).2
  have hab : a.val = b.val := by
    have hfin :
        Fin.castAdd P.q a = Fin.castAdd P.q b := by
      exact hax.trans hbx.symm
    simpa [Fin.castAdd] using congrArg Fin.val hfin
  omega

lemma leftBefore_disjoint_hodgeC {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    Disjoint (leftBefore P ν) (hodgeC P ν hνp) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxBefore hxC
  rcases Finset.mem_union.mp hxC with hxRight | hxSuffix
  · have hdis := leftBefore_disjoint_rightPrefix P ν
    rw [Finset.disjoint_left] at hdis
    exact hdis hxBefore hxRight
  · have hdis := leftBefore_disjoint_leftSuffix P ν hνp
    rw [Finset.disjoint_left] at hdis
    exact hdis hxBefore hxSuffix

lemma leftBefore_subset_hodgeD_sdiff_W {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p)
    {W : Finset (Fin (P.p + P.q))}
    (hW : W ⊆ hodgeC P ν hνp) :
    leftBefore P ν ⊆ hodgeD P ν \ W := by
  classical
  intro x hx
  refine Finset.mem_sdiff.mpr ⟨leftBefore_subset_hodgeD P ν hx, ?_⟩
  intro hxW
  have hdis := leftBefore_disjoint_hodgeC P ν hνp
  rw [Finset.disjoint_left] at hdis
  exact hdis hx (hW hxW)

lemma slotCol_lt_of_mem_leftBefore {m n : ℕ}
    (P : RawMinorPair m n) (hcol : StrictMono P.left.col)
    {ν : Fin P.q} (hνp : ν.val < P.p)
    {x : Fin (P.p + P.q)} (hx : x ∈ leftBefore P ν) :
    P.slotCol (finSumFinEquiv.symm x) < P.left.col ⟨ν.val, hνp⟩ := by
  classical
  rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
  have haν : a.val < ν.val := (Finset.mem_filter.mp ha).2
  have hslot :
      P.slotCol (finSumFinEquiv.symm x) = P.left.col a := by
    rw [← hax]
    change P.slotCol (finSumFinEquiv.symm (Fin.castAdd P.q a)) = P.left.col a
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  rw [hslot]
  exact hcol (by simpa [Fin.lt_def] using haν)

lemma slotRow_lt_of_mem_leftBefore {m n : ℕ}
    (P : RawMinorPair m n) (hrow : StrictMono P.left.row)
    {ν : Fin P.q} (hνp : ν.val < P.p)
    {x : Fin (P.p + P.q)} (hx : x ∈ leftBefore P ν) :
    P.slotRow (finSumFinEquiv.symm x) < P.left.row ⟨ν.val, hνp⟩ := by
  classical
  rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
  have haν : a.val < ν.val := (Finset.mem_filter.mp ha).2
  have hslot :
      P.slotRow (finSumFinEquiv.symm x) = P.left.row a := by
    rw [← hax]
    change P.slotRow (finSumFinEquiv.symm (Fin.castAdd P.q a)) = P.left.row a
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  rw [hslot]
  exact hrow (by simpa [Fin.lt_def] using haν)

@[simp] lemma card_leftAfter {m n : ℕ}
    (P : RawMinorPair m n) (i : Fin P.p) :
    (leftAfter P i).card = P.p - (i.val + 1) := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin P.p => i < a) =
        Finset.Ioi i := by
    ext a
    simp
  rw [leftAfter, hfilter]
  simp
  omega

lemma leftAfter_subset_leftSlotFinset {m n : ℕ}
    (P : RawMinorPair m n) (i : Fin P.p) :
    leftAfter P i ⊆ leftSlotFinset P := by
  classical
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨a, _ha, hax⟩
  exact Finset.mem_map.mpr ⟨a, Finset.mem_univ _, hax⟩

lemma leftSuffix_subset_hodgeD {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    leftSuffix P ν hνp ⊆ hodgeD P ν := by
  intro x hx
  exact leftSlotFinset_subset_hodgeD P ν
    (leftSuffix_subset_leftSlotFinset P ν hνp hx)

lemma hodgeC_subset_hodgeD {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    hodgeC P ν hνp ⊆ hodgeD P ν := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact rightPrefix_subset_hodgeD P ν hx
  · exact leftSuffix_subset_hodgeD P ν hνp hx

lemma rightPrefix_disjoint_leftSuffix {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    Disjoint (rightPrefix P ν) (leftSuffix P ν hνp) := by
  exact (rightPrefix_disjoint_leftSlotFinset P ν).mono_right
    (leftSuffix_subset_leftSlotFinset P ν hνp)

@[simp] lemma card_rightPrefix {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    (rightPrefix P ν).card = ν.val + 1 := by
  classical
  have hfilter :
      (Finset.univ.filter fun μ : Fin P.q => μ ≤ ν) =
        Finset.Iic ν := by
    ext μ
    simp
  rw [rightPrefix, hfilter]
  simp

@[simp] lemma card_leftSuffix {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (leftSuffix P ν hνp).card = P.p - ν.val := by
  classical
  let a : Fin P.p := ⟨ν.val, hνp⟩
  have hfilter :
      (Finset.univ.filter fun i : Fin P.p => ν.val ≤ i.val) =
        Finset.Ici a := by
    ext i
    simp [a, Fin.le_def]
  rw [leftSuffix, hfilter]
  simp [a]

@[simp] lemma card_hodgeD {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    (hodgeD P ν).card = P.p + (ν.val + 1) := by
  classical
  rw [hodgeD, Finset.card_union_of_disjoint
    (leftSlotFinset_disjoint_rightPrefix P ν)]
  simp

@[simp] lemma card_hodgeC {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (hodgeC P ν hνp).card = P.p + 1 := by
  classical
  rw [hodgeC, Finset.card_union_of_disjoint
    (rightPrefix_disjoint_leftSuffix P ν hνp)]
  simp
  omega

lemma hodgeC_sdiff_permPreimageLeftSlotFinset_nonempty
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    (π : Equiv.Perm (Fin (P.p + P.q))) :
    (hodgeC P ν hνp \ permPreimageLeftSlotFinset P π).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hsubset :
      hodgeC P ν hνp ⊆ permPreimageLeftSlotFinset P π := by
    intro x hx
    by_contra hxpre
    have hxsdiff : x ∈ hodgeC P ν hνp \ permPreimageLeftSlotFinset P π :=
      Finset.mem_sdiff.mpr ⟨hx, hxpre⟩
    simp [hempty] at hxsdiff
  have hcard := Finset.card_le_card hsubset
  rw [card_hodgeC, card_permPreimageLeftSlotFinset] at hcard
  omega

lemma hodgeD_sdiff_rightPrefix {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) :
    hodgeD P ν \ rightPrefix P ν = leftSlotFinset P := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxD, hxnot⟩
    rcases Finset.mem_union.mp hxD with hxleft | hxright
    · exact hxleft
    · exact False.elim (hxnot hxright)
  · intro hxleft
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_union_left (rightPrefix P ν) hxleft
    · intro hxright
      have hdis := rightPrefix_disjoint_leftSlotFinset P ν
      rw [Finset.disjoint_left] at hdis
      exact hdis hxright hxleft

lemma W_eq_rightPrefix_of_rightPrefix_subset_of_subset_hodgeC_of_card_hodgeD_sdiff
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    {W : Finset (Fin (P.p + P.q))}
    (hright : rightPrefix P ν ⊆ W)
    (hW : W ⊆ hodgeC P ν hνp)
    (hcard : (hodgeD P ν \ W).card = P.p) :
    W = rightPrefix P ν := by
  classical
  have hWD : W ⊆ hodgeD P ν := by
    intro x hx
    exact hodgeC_subset_hodgeD P ν hνp (hW hx)
  have hsdiff :
      (hodgeD P ν \ W).card = (hodgeD P ν).card - W.card := by
    simpa using Finset.card_sdiff_of_subset hWD
  have hWle : W.card ≤ (hodgeD P ν).card := Finset.card_le_card hWD
  have hWcard : W.card = (rightPrefix P ν).card := by
    rw [card_rightPrefix]
    rw [card_hodgeD] at hsdiff hWle
    omega
  exact (Finset.eq_of_subset_of_card_le hright (by simp [hWcard])).symm

end Hodge

/-- Column-side Hodge split for Swan's component branch.

`rowSlots` is Swan's `U ⊇ A`, `W` is a subset of the Hodge set `C`, and the
new column slots are `D \ W`. -/
structure HodgeColSplit {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) where
  rowSlots : Finset (Fin (P.p + P.q))
  W : Finset (Fin (P.p + P.q))
  leftRows : leftSlotFinset P ⊆ rowSlots
  W_subset : W ⊆ Hodge.hodgeC P ν hνp
  card_eq : rowSlots.card = (Hodge.hodgeD P ν \ W).card

namespace HodgeColSplit

def colSlots {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    Finset (Fin (P.p + P.q)) :=
  Hodge.hodgeD P ν \ S.W

def code {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    Finset (Fin (P.p + P.q)) × Finset (Fin (P.p + P.q)) :=
  (S.rowSlots, S.W)

lemma code_injective {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Function.Injective (@code m n P ν hνp) := by
  intro S T h
  cases S
  cases T
  simp only [code, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

instance instFinite {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Finite (HodgeColSplit P ν hνp) := by
  classical
  exact Finite.of_injective (@code m n P ν hνp) code_injective

noncomputable instance instFintype {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Fintype (HodgeColSplit P ν hνp) := by
  classical
  exact Fintype.ofFinite _

noncomputable def toBiReshuffle {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    BiReshuffle P :=
  ofFinsets P S.rowSlots S.colSlots S.card_eq

/-- The Hodge pivot has `U = A` and `W = {j₁,...,jν}`, hence `D \ W = A`. -/
noncomputable def pivot {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    HodgeColSplit P ν hνp where
  rowSlots := leftSlotFinset P
  W := Hodge.rightPrefix P ν
  leftRows := Finset.Subset.rfl
  W_subset := Hodge.rightPrefix_subset_hodgeC P ν hνp
  card_eq := by
    rw [Hodge.hodgeD_sdiff_rightPrefix]

@[simp] lemma pivot_rowSlots {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (pivot P ν hνp).rowSlots = leftSlotFinset P := rfl

@[simp] lemma pivot_W {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (pivot P ν hνp).W = Hodge.rightPrefix P ν := rfl

@[simp] lemma pivot_colSlots {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (pivot P ν hνp).colSlots = leftSlotFinset P := by
  simp [pivot, colSlots, Hodge.hodgeD_sdiff_rightPrefix]

@[simp] lemma toBiReshuffle_r {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    S.toBiReshuffle.r = S.rowSlots.card := by
  rfl

@[simp] lemma pivot_toBiReshuffle_r {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (pivot P ν hνp).toBiReshuffle.r = P.p := by
  simp

noncomputable def colSplit {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
      Fin (P.p + P.q) :=
  finSumEquivOfFinset S.card_eq.symm (by
    rw [Finset.card_compl, Fintype.card_fin]
    rw [← S.card_eq])

noncomputable def rowSplit {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
      Fin (P.p + P.q) :=
  finSumEquivOfFinset rfl (by
    rw [Finset.card_compl, Fintype.card_fin])

noncomputable def leibnizPerm {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    Equiv.Perm (Fin (P.p + P.q)) :=
  (S.colSplit.symm.trans (Equiv.sumCongr τ σ)).trans S.rowSplit

noncomputable def stdSplit {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
      Fin (P.p + P.q) :=
  finSumFinEquivToTotal (P.p + P.q) S.rowSlots.card (by
    simpa using Finset.card_le_univ S.rowSlots)

noncomputable def rowSplitRel {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    Equiv.Perm (Fin S.rowSlots.card ⊕
      Fin (P.p + P.q - S.rowSlots.card)) :=
  S.rowSplit.trans S.stdSplit.symm

noncomputable def colSplitRel {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    Equiv.Perm (Fin S.rowSlots.card ⊕
      Fin (P.p + P.q - S.rowSlots.card)) :=
  S.colSplit.trans S.stdSplit.symm

noncomputable def splitSignFactor {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} {R : Type*} [CommRing R]
    (S : HodgeColSplit P ν hνp) : R :=
  equivPermSign (R := R) S.rowSplitRel *
    equivPermSign (R := R) S.colSplitRel

lemma splitSignFactor_mul_self {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} {R : Type*} [CommRing R]
    (S : HodgeColSplit P ν hνp) :
    S.splitSignFactor (R := R) * S.splitSignFactor (R := R) = 1 := by
  unfold splitSignFactor
  have hrow := equivPermSign_mul_self (R := R) S.rowSplitRel
  have hcol := equivPermSign_mul_self (R := R) S.colSplitRel
  calc
    (equivPermSign (R := R) S.rowSplitRel *
          equivPermSign (R := R) S.colSplitRel) *
        (equivPermSign (R := R) S.rowSplitRel *
          equivPermSign (R := R) S.colSplitRel)
        =
      (equivPermSign (R := R) S.rowSplitRel *
          equivPermSign (R := R) S.rowSplitRel) *
        (equivPermSign (R := R) S.colSplitRel *
          equivPermSign (R := R) S.colSplitRel) := by
          ring
    _ = 1 := by
          rw [hrow, hcol]
          ring

lemma eq_pivot_of_rowSlots_card_eq_of_rightPrefix_subset_W
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (hcard : S.rowSlots.card = P.p)
    (hright : Hodge.rightPrefix P ν ⊆ S.W) :
    S = pivot P ν hνp := by
  classical
  have hrow : S.rowSlots = leftSlotFinset P := by
    exact (Finset.eq_of_subset_of_card_le S.leftRows (by
      simp [hcard])).symm
  have hcolcard : (Hodge.hodgeD P ν \ S.W).card = P.p := by
    rw [← S.card_eq, hcard]
  have hW : S.W = Hodge.rightPrefix P ν :=
    Hodge.W_eq_rightPrefix_of_rightPrefix_subset_of_subset_hodgeC_of_card_hodgeD_sdiff
      P ν hνp hright S.W_subset hcolcard
  exact code_injective (by simp [code, hrow, hW])

lemma rightPrefix_sdiff_W_nonempty_of_ne_pivot_of_rowSlots_card_eq
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (hne : S ≠ pivot P ν hνp)
    (hcard : S.rowSlots.card = P.p) :
    (Hodge.rightPrefix P ν \ S.W).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hright : Hodge.rightPrefix P ν ⊆ S.W := by
    intro x hx
    by_contra hxW
    have hxsdiff : x ∈ Hodge.rightPrefix P ν \ S.W :=
      Finset.mem_sdiff.mpr ⟨hx, hxW⟩
    simp [hempty] at hxsdiff
  exact hne
    (eq_pivot_of_rowSlots_card_eq_of_rightPrefix_subset_W S hcard hright)

noncomputable instance instFintypeNePivot {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Fintype { S : HodgeColSplit P ν hνp // S ≠ pivot P ν hνp } := by
  classical
  exact Fintype.ofFinite _

end HodgeColSplit

/-- Row-side Hodge split for Swan's component branch.

This is the row/column mirror of `HodgeColSplit`: row slots are `D \ W`, while
`colSlots` is Swan's containing set on the column side. -/
structure HodgeRowSplit {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) where
  W : Finset (Fin (P.p + P.q))
  colSlots : Finset (Fin (P.p + P.q))
  W_subset : W ⊆ Hodge.hodgeC P ν hνp
  leftCols : leftSlotFinset P ⊆ colSlots
  card_eq : (Hodge.hodgeD P ν \ W).card = colSlots.card

namespace HodgeRowSplit

def rowSlots {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    Finset (Fin (P.p + P.q)) :=
  Hodge.hodgeD P ν \ S.W

def code {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    Finset (Fin (P.p + P.q)) × Finset (Fin (P.p + P.q)) :=
  (S.W, S.colSlots)

lemma code_injective {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Function.Injective (@code m n P ν hνp) := by
  intro S T h
  cases S
  cases T
  simp only [code, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

instance instFinite {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Finite (HodgeRowSplit P ν hνp) := by
  classical
  exact Finite.of_injective (@code m n P ν hνp) code_injective

noncomputable instance instFintype {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Fintype (HodgeRowSplit P ν hνp) := by
  classical
  exact Fintype.ofFinite _

noncomputable def toBiReshuffle {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    BiReshuffle P :=
  ofFinsets P S.rowSlots S.colSlots S.card_eq

/-- The Hodge row pivot has `W = {j₁,...,jν}` and column slots equal to the
original left slots. -/
noncomputable def pivot {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    HodgeRowSplit P ν hνp where
  W := Hodge.rightPrefix P ν
  colSlots := leftSlotFinset P
  W_subset := Hodge.rightPrefix_subset_hodgeC P ν hνp
  leftCols := Finset.Subset.rfl
  card_eq := by
    rw [Hodge.hodgeD_sdiff_rightPrefix]

@[simp] lemma pivot_W {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (pivot P ν hνp).W = Hodge.rightPrefix P ν := rfl

@[simp] lemma pivot_colSlots {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (pivot P ν hνp).colSlots = leftSlotFinset P := rfl

@[simp] lemma pivot_rowSlots {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (pivot P ν hνp).rowSlots = leftSlotFinset P := by
  simp [pivot, rowSlots, Hodge.hodgeD_sdiff_rightPrefix]

@[simp] lemma toBiReshuffle_r {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    S.toBiReshuffle.r = S.rowSlots.card := by
  rfl

@[simp] lemma pivot_toBiReshuffle_r {m n : ℕ}
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p) :
    (pivot P ν hνp).toBiReshuffle.r = P.p := by
  simp

noncomputable def colSplit {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
      Fin (P.p + P.q) :=
  finSumEquivOfFinset S.card_eq.symm (by
    rw [Finset.card_compl, Fintype.card_fin]
    rw [← S.card_eq]
    rfl)

noncomputable def rowSplit {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
      Fin (P.p + P.q) :=
  finSumEquivOfFinset rfl (by
    rw [Finset.card_compl, Fintype.card_fin])

noncomputable def leibnizPerm {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    Equiv.Perm (Fin (P.p + P.q)) :=
  (S.colSplit.symm.trans (Equiv.sumCongr τ σ)).trans S.rowSplit

noncomputable def stdSplit {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
      Fin (P.p + P.q) :=
  finSumFinEquivToTotal (P.p + P.q) S.rowSlots.card (by
    simpa using Finset.card_le_univ S.rowSlots)

noncomputable def rowSplitRel {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    Equiv.Perm (Fin S.rowSlots.card ⊕
      Fin (P.p + P.q - S.rowSlots.card)) :=
  S.rowSplit.trans S.stdSplit.symm

noncomputable def colSplitRel {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    Equiv.Perm (Fin S.rowSlots.card ⊕
      Fin (P.p + P.q - S.rowSlots.card)) :=
  S.colSplit.trans S.stdSplit.symm

noncomputable def splitSignFactor {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} {R : Type*} [CommRing R]
    (S : HodgeRowSplit P ν hνp) : R :=
  equivPermSign (R := R) S.rowSplitRel *
    equivPermSign (R := R) S.colSplitRel

lemma splitSignFactor_mul_self {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} {R : Type*} [CommRing R]
    (S : HodgeRowSplit P ν hνp) :
    S.splitSignFactor (R := R) * S.splitSignFactor (R := R) = 1 := by
  unfold splitSignFactor
  have hrow := equivPermSign_mul_self (R := R) S.rowSplitRel
  have hcol := equivPermSign_mul_self (R := R) S.colSplitRel
  calc
    (equivPermSign (R := R) S.rowSplitRel *
          equivPermSign (R := R) S.colSplitRel) *
        (equivPermSign (R := R) S.rowSplitRel *
          equivPermSign (R := R) S.colSplitRel)
        =
      (equivPermSign (R := R) S.rowSplitRel *
          equivPermSign (R := R) S.rowSplitRel) *
        (equivPermSign (R := R) S.colSplitRel *
          equivPermSign (R := R) S.colSplitRel) := by
          ring
    _ = 1 := by
          rw [hrow, hcol]
          ring

lemma eq_pivot_of_rowSlots_card_eq_of_rightPrefix_subset_W
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (hcard : S.rowSlots.card = P.p)
    (hright : Hodge.rightPrefix P ν ⊆ S.W) :
    S = pivot P ν hνp := by
  classical
  have hrowcard : (Hodge.hodgeD P ν \ S.W).card = P.p := by
    simpa [rowSlots] using hcard
  have hW : S.W = Hodge.rightPrefix P ν :=
    Hodge.W_eq_rightPrefix_of_rightPrefix_subset_of_subset_hodgeC_of_card_hodgeD_sdiff
      P ν hνp hright S.W_subset hrowcard
  have hcolcard : S.colSlots.card = P.p := by
    rw [← S.card_eq]
    exact hrowcard
  have hcol : S.colSlots = leftSlotFinset P := by
    exact (Finset.eq_of_subset_of_card_le S.leftCols (by
      simp [hcolcard])).symm
  exact code_injective (by simp [code, hW, hcol])

lemma rightPrefix_sdiff_W_nonempty_of_ne_pivot_of_rowSlots_card_eq
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (hne : S ≠ pivot P ν hνp)
    (hcard : S.rowSlots.card = P.p) :
    (Hodge.rightPrefix P ν \ S.W).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hright : Hodge.rightPrefix P ν ⊆ S.W := by
    intro x hx
    by_contra hxW
    have hxsdiff : x ∈ Hodge.rightPrefix P ν \ S.W :=
      Finset.mem_sdiff.mpr ⟨hx, hxW⟩
    simp [hempty] at hxsdiff
  exact hne
    (eq_pivot_of_rowSlots_card_eq_of_rightPrefix_subset_W S hcard hright)

noncomputable instance instFintypeNePivot {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Fintype { S : HodgeRowSplit P ν hνp // S ≠ pivot P ν hνp } := by
  classical
  exact Fintype.ofFinite _

end HodgeRowSplit

/-- A canonical pair of row and column slot selections containing the
original left block.  This is the finite-set form of Swan's conditions
`U ⊇ A` and `W ⊇ B`. -/
structure ContainingSplit {m n : ℕ} (P : RawMinorPair m n) where
  rowSlots : Finset (Fin (P.p + P.q))
  colSlots : Finset (Fin (P.p + P.q))
  card_eq : rowSlots.card = colSlots.card
  leftRows : leftSlotFinset P ⊆ rowSlots
  leftCols : leftSlotFinset P ⊆ colSlots

namespace ContainingSplit

def code {m n : ℕ} {P : RawMinorPair m n} (S : ContainingSplit P) :
    Finset (Fin (P.p + P.q)) × Finset (Fin (P.p + P.q)) :=
  (S.rowSlots, S.colSlots)

lemma code_injective {m n : ℕ} {P : RawMinorPair m n} :
    Function.Injective (@code m n P) := by
  intro S T h
  cases S
  cases T
  simp only [code, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

instance instFinite {m n : ℕ} {P : RawMinorPair m n} :
    Finite (ContainingSplit P) := by
  classical
  exact Finite.of_injective (@code m n P) code_injective

noncomputable instance instFintype {m n : ℕ} {P : RawMinorPair m n} :
    Fintype (ContainingSplit P) := by
  classical
  exact Fintype.ofFinite _

/-- The canonical `BiReshuffle` represented by a containing slot split. -/
noncomputable def toBiReshuffle {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    BiReshuffle P :=
  ofFinsets P S.rowSlots S.colSlots S.card_eq

/-- The distinguished split corresponding to the original raw pair. -/
def pivot {m n : ℕ} (P : RawMinorPair m n) :
    ContainingSplit P where
  rowSlots := leftSlotFinset P
  colSlots := leftSlotFinset P
  card_eq := rfl
  leftRows := Finset.Subset.rfl
  leftCols := Finset.Subset.rfl

@[simp] lemma toBiReshuffle_r {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    S.toBiReshuffle.r = S.rowSlots.card := by
  rfl

@[simp] lemma pivot_rowSlots {m n : ℕ} (P : RawMinorPair m n) :
    (pivot P).rowSlots = leftSlotFinset P := rfl

@[simp] lemma pivot_colSlots {m n : ℕ} (P : RawMinorPair m n) :
    (pivot P).colSlots = leftSlotFinset P := rfl

@[simp] lemma pivot_toBiReshuffle_r {m n : ℕ} (P : RawMinorPair m n) :
    (pivot P).toBiReshuffle.r = P.p := by
  simp

noncomputable instance instFintypeNePivot {m n : ℕ} {P : RawMinorPair m n} :
    Fintype { S : ContainingSplit P // S ≠ pivot P } := by
  classical
  exact Fintype.ofFinite _

lemma eq_pivot_of_rowSlots_card_eq {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) (hcard : S.rowSlots.card = P.p) :
    S = pivot P := by
  cases S with
  | mk rowSlots colSlots card_eq leftRows leftCols =>
      have hrow : rowSlots = leftSlotFinset P := by
        exact (Finset.eq_of_subset_of_card_le leftRows (by
          simp [hcard])).symm
      have hcol : colSlots = leftSlotFinset P := by
        exact (Finset.eq_of_subset_of_card_le leftCols (by
          simp [card_eq.symm, hcard])).symm
      subst rowSlots
      subst colSlots
      rfl

lemma leftSlotFinset_card_le_rowSlots_card {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    P.p ≤ S.rowSlots.card := by
  simpa using Finset.card_le_card S.leftRows

lemma leftSlotFinset_card_le_colSlots_card {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    P.p ≤ S.colSlots.card := by
  simpa using Finset.card_le_card S.leftCols

lemma rowSlots_card_lt_of_ne_pivot {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) (hS : S ≠ pivot P) :
    P.p < S.rowSlots.card := by
  have hle : P.p ≤ S.rowSlots.card := S.leftSlotFinset_card_le_rowSlots_card
  exact lt_of_le_of_ne hle (by
    intro h
    exact hS (eq_pivot_of_rowSlots_card_eq S h.symm))

lemma colSlots_card_lt_of_ne_pivot {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) (hS : S ≠ pivot P) :
    P.p < S.colSlots.card := by
  have hrow : P.p < S.rowSlots.card := S.rowSlots_card_lt_of_ne_pivot hS
  simpa [S.card_eq] using hrow

lemma rowSlots_sdiff_leftSlotFinset_nonempty_of_ne_pivot
    {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) (hS : S ≠ pivot P) :
    (S.rowSlots \ leftSlotFinset P).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hcard :
      (S.rowSlots \ leftSlotFinset P).card = S.rowSlots.card - P.p := by
    simpa using Finset.card_sdiff_of_subset S.leftRows
  have hle : S.rowSlots.card ≤ P.p := by
    have hzero : (S.rowSlots \ leftSlotFinset P).card = 0 := by
      simp [hempty]
    omega
  have hlt : P.p < S.rowSlots.card := S.rowSlots_card_lt_of_ne_pivot hS
  omega

lemma colSlots_sdiff_leftSlotFinset_nonempty_of_ne_pivot
    {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) (hS : S ≠ pivot P) :
    (S.colSlots \ leftSlotFinset P).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hcard :
      (S.colSlots \ leftSlotFinset P).card = S.colSlots.card - P.p := by
    simpa using Finset.card_sdiff_of_subset S.leftCols
  have hle : S.colSlots.card ≤ P.p := by
    have hzero : (S.colSlots \ leftSlotFinset P).card = 0 := by
      simp [hempty]
    omega
  have hlt : P.p < S.colSlots.card := S.colSlots_card_lt_of_ne_pivot hS
  omega

lemma rowSlots_mem_Icc {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    S.rowSlots ∈ Finset.Icc (leftSlotFinset P) Finset.univ := by
  exact Finset.mem_Icc.mpr ⟨S.leftRows, Finset.subset_univ _⟩

lemma colSlots_mem_Icc {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    S.colSlots ∈ Finset.Icc (leftSlotFinset P) Finset.univ := by
  exact Finset.mem_Icc.mpr ⟨S.leftCols, Finset.subset_univ _⟩

lemma leftSlotFinset_subset_of_mem_Icc {m n : ℕ} {P : RawMinorPair m n}
    {s : Finset (Fin (P.p + P.q))}
    (hs : s ∈ Finset.Icc (leftSlotFinset P) Finset.univ) :
    leftSlotFinset P ⊆ s :=
  (Finset.mem_Icc.mp hs).1

lemma subset_univ_of_mem_Icc {m n : ℕ} {P : RawMinorPair m n}
    {s : Finset (Fin (P.p + P.q))}
    (hs : s ∈ Finset.Icc (leftSlotFinset P) Finset.univ) :
    s ⊆ Finset.univ :=
  (Finset.mem_Icc.mp hs).2

noncomputable def ofIcc {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : { s : Finset (Fin (P.p + P.q)) //
      s ∈ Finset.Icc (leftSlotFinset P) Finset.univ })
    (hcard : rowSlots.1.card = colSlots.1.card) :
    ContainingSplit P where
  rowSlots := rowSlots.1
  colSlots := colSlots.1
  card_eq := hcard
  leftRows := leftSlotFinset_subset_of_mem_Icc rowSlots.2
  leftCols := leftSlotFinset_subset_of_mem_Icc colSlots.2

@[simp] lemma ofIcc_rowSlots {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : { s : Finset (Fin (P.p + P.q)) //
      s ∈ Finset.Icc (leftSlotFinset P) Finset.univ })
    (hcard : rowSlots.1.card = colSlots.1.card) :
    (ofIcc P rowSlots colSlots hcard).rowSlots = rowSlots.1 := rfl

@[simp] lemma ofIcc_colSlots {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : { s : Finset (Fin (P.p + P.q)) //
      s ∈ Finset.Icc (leftSlotFinset P) Finset.univ })
    (hcard : rowSlots.1.card = colSlots.1.card) :
    (ofIcc P rowSlots colSlots hcard).colSlots = colSlots.1 := rfl

abbrev IccSplit {m n : ℕ} (P : RawMinorPair m n) :=
  { rc :
      ({ s : Finset (Fin (P.p + P.q)) //
          s ∈ Finset.Icc (leftSlotFinset P) Finset.univ } ×
        { s : Finset (Fin (P.p + P.q)) //
          s ∈ Finset.Icc (leftSlotFinset P) Finset.univ }) //
      rc.1.1.card = rc.2.1.card }

noncomputable def toIccSplit {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) : IccSplit P :=
  ⟨(⟨S.rowSlots, S.rowSlots_mem_Icc⟩, ⟨S.colSlots, S.colSlots_mem_Icc⟩), S.card_eq⟩

noncomputable def ofIccSplit {m n : ℕ} {P : RawMinorPair m n}
    (S : IccSplit P) : ContainingSplit P :=
  ofIcc P S.1.1 S.1.2 S.2

lemma ofIccSplit_toIccSplit {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    ofIccSplit (toIccSplit S) = S := by
  cases S
  rfl

lemma toIccSplit_ofIccSplit {m n : ℕ} {P : RawMinorPair m n}
    (S : IccSplit P) :
    toIccSplit (ofIccSplit S) = S := by
  cases S with
  | mk rc hcard =>
      cases rc with
      | mk row col =>
          cases row
          cases col
          rfl

noncomputable def iccSplitEquiv {m n : ℕ} (P : RawMinorPair m n) :
    ContainingSplit P ≃ IccSplit P where
  toFun := toIccSplit
  invFun := ofIccSplit
  left_inv := ofIccSplit_toIccSplit
  right_inv := toIccSplit_ofIccSplit

@[simp] lemma iccSplitEquiv_apply_fst_fst {m n : ℕ} (P : RawMinorPair m n)
    (S : ContainingSplit P) :
    ((iccSplitEquiv P S).1.1.1) = S.rowSlots := rfl

@[simp] lemma iccSplitEquiv_apply_fst_snd {m n : ℕ} (P : RawMinorPair m n)
    (S : ContainingSplit P) :
    ((iccSplitEquiv P S).1.2.1) = S.colSlots := rfl

lemma sum_containingSplit_eq_sum_iccSplit {m n : ℕ} {P : RawMinorPair m n}
    {M : Type*} [AddCommMonoid M] (f : ContainingSplit P → M) :
    (∑ S : ContainingSplit P, f S) =
      ∑ S : IccSplit P, f (ofIccSplit S) := by
  classical
  exact Fintype.sum_equiv (iccSplitEquiv P) f (fun S => f (ofIccSplit S))
    (by intro S; simp [iccSplitEquiv, ofIccSplit_toIccSplit])

lemma exists_rowEquiv_inl_eq_inl {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) (i : Fin P.p) :
    ∃ a : Fin S.toBiReshuffle.r,
      S.toBiReshuffle.rowEquiv (Sum.inl a) = Sum.inl i := by
  classical
  let x : S.rowSlots := ⟨Fin.castAdd P.q i,
    S.leftRows (mem_leftSlotFinset_castAdd P i)⟩
  let a : Fin S.rowSlots.card := (S.rowSlots.orderIsoOfFin rfl).symm x
  refine ⟨a, ?_⟩
  simp only [toBiReshuffle, ofFinsets_rowEquiv_inl]
  have ha :
      S.rowSlots.orderEmbOfFin rfl a = Fin.castAdd P.q i := by
    exact congrArg Subtype.val ((S.rowSlots.orderIsoOfFin rfl).apply_symm_apply x)
  rw [ha, finSumFinEquiv_symm_apply_castAdd]

lemma exists_colEquiv_inl_eq_inl {m n : ℕ} {P : RawMinorPair m n}
    (S : ContainingSplit P) (i : Fin P.p) :
    ∃ a : Fin S.toBiReshuffle.r,
      S.toBiReshuffle.colEquiv (Sum.inl a) = Sum.inl i := by
  classical
  let x : S.colSlots := ⟨Fin.castAdd P.q i,
    S.leftCols (mem_leftSlotFinset_castAdd P i)⟩
  let a : Fin S.colSlots.card := (S.colSlots.orderIsoOfFin rfl).symm x
  refine ⟨Fin.cast S.card_eq.symm a, ?_⟩
  simp only [toBiReshuffle, ofFinsets_colEquiv_inl]
  have ha :
      S.colSlots.orderEmbOfFin S.card_eq.symm (Fin.cast S.card_eq.symm a) =
        Fin.castAdd P.q i := by
    exact congrArg Subtype.val ((S.colSlots.orderIsoOfFin rfl).apply_symm_apply x)
  rw [ha, finSumFinEquiv_symm_apply_castAdd]

end ContainingSplit

def toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) : RawMinorPair m n where
  p := E.r
  q := P.p + P.q - E.r
  left :=
    { row := fun i => P.slotRow (E.rowEquiv (Sum.inl i))
      col := fun i => P.slotCol (E.colEquiv (Sum.inl i)) }
  right :=
    { row := fun j => P.slotRow (E.rowEquiv (Sum.inr j))
      col := fun j => P.slotCol (E.colEquiv (Sum.inr j)) }

lemma ofFinsets_left_row_filter_card_eq {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) (x : Fin m) :
    (Finset.univ.filter fun a : Fin rowSlots.card =>
        (ofFinsets P rowSlots colSlots hcard).toPair.left.row a ≤ x).card =
      (rowSlots.filter fun y =>
        P.slotRow (finSumFinEquiv.symm y) ≤ x).card := by
  classical
  refine Finset.card_bij
      (fun a _ha => rowSlots.orderEmbOfFin rfl a) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.orderEmbOfFin_mem rowSlots rfl a, ?_⟩
    simpa [BiReshuffle.toPair] using ha.2
  · intro a₁ _ha₁ a₂ _ha₂ h
    exact (rowSlots.orderEmbOfFin rfl).injective h
  · intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyrow, hyx⟩
    let a : Fin rowSlots.card := (rowSlots.orderIsoOfFin rfl).symm ⟨y, hyrow⟩
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have ha :
          rowSlots.orderEmbOfFin rfl a = y := by
        exact congrArg Subtype.val
          ((rowSlots.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyrow⟩)
      change
        P.slotRow (finSumFinEquiv.symm (rowSlots.orderEmbOfFin rfl a)) ≤ x
      rw [ha]
      exact hyx
    · exact congrArg Subtype.val
        ((rowSlots.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyrow⟩)

lemma ofFinsets_left_col_filter_card_eq {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) (x : Fin n) :
    (Finset.univ.filter fun a : Fin rowSlots.card =>
        (ofFinsets P rowSlots colSlots hcard).toPair.left.col a ≤ x).card =
      (colSlots.filter fun y =>
        P.slotCol (finSumFinEquiv.symm y) ≤ x).card := by
  classical
  refine Finset.card_bij
      (fun a _ha => colSlots.orderEmbOfFin hcard.symm a) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.orderEmbOfFin_mem colSlots hcard.symm a, ?_⟩
    simpa [BiReshuffle.toPair] using ha.2
  · intro a₁ _ha₁ a₂ _ha₂ h
    exact (colSlots.orderEmbOfFin hcard.symm).injective h
  · intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hycol, hyx⟩
    let a : Fin colSlots.card := (colSlots.orderIsoOfFin rfl).symm ⟨y, hycol⟩
    refine ⟨Fin.cast hcard.symm a, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have ha :
          colSlots.orderEmbOfFin hcard.symm (Fin.cast hcard.symm a) = y := by
        exact congrArg Subtype.val
          ((colSlots.orderIsoOfFin rfl).apply_symm_apply ⟨y, hycol⟩)
      change
        P.slotCol
          (finSumFinEquiv.symm
            (colSlots.orderEmbOfFin hcard.symm (Fin.cast hcard.symm a))) ≤ x
      rw [ha]
      exact hyx
    · exact congrArg Subtype.val
        ((colSlots.orderIsoOfFin rfl).apply_symm_apply ⟨y, hycol⟩)

lemma ofFinsets_left_row_filter_card_lt_eq {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) (x : Fin m) :
    (Finset.univ.filter fun a : Fin rowSlots.card =>
        (ofFinsets P rowSlots colSlots hcard).toPair.left.row a < x).card =
      (rowSlots.filter fun y =>
        P.slotRow (finSumFinEquiv.symm y) < x).card := by
  classical
  refine Finset.card_bij
      (fun a _ha => rowSlots.orderEmbOfFin rfl a) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.orderEmbOfFin_mem rowSlots rfl a, ?_⟩
    simpa [BiReshuffle.toPair] using ha.2
  · intro a₁ _ha₁ a₂ _ha₂ h
    exact (rowSlots.orderEmbOfFin rfl).injective h
  · intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hyrow, hyx⟩
    let a : Fin rowSlots.card := (rowSlots.orderIsoOfFin rfl).symm ⟨y, hyrow⟩
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have ha :
          rowSlots.orderEmbOfFin rfl a = y := by
        exact congrArg Subtype.val
          ((rowSlots.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyrow⟩)
      change
        P.slotRow (finSumFinEquiv.symm (rowSlots.orderEmbOfFin rfl a)) < x
      rw [ha]
      exact hyx
    · exact congrArg Subtype.val
        ((rowSlots.orderIsoOfFin rfl).apply_symm_apply ⟨y, hyrow⟩)

lemma ofFinsets_left_col_filter_card_lt_eq {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) (x : Fin n) :
    (Finset.univ.filter fun a : Fin rowSlots.card =>
        (ofFinsets P rowSlots colSlots hcard).toPair.left.col a < x).card =
      (colSlots.filter fun y =>
        P.slotCol (finSumFinEquiv.symm y) < x).card := by
  classical
  refine Finset.card_bij
      (fun a _ha => colSlots.orderEmbOfFin hcard.symm a) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.orderEmbOfFin_mem colSlots hcard.symm a, ?_⟩
    simpa [BiReshuffle.toPair] using ha.2
  · intro a₁ _ha₁ a₂ _ha₂ h
    exact (colSlots.orderEmbOfFin hcard.symm).injective h
  · intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hycol, hyx⟩
    let a : Fin colSlots.card := (colSlots.orderIsoOfFin rfl).symm ⟨y, hycol⟩
    refine ⟨Fin.cast hcard.symm a, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have ha :
          colSlots.orderEmbOfFin hcard.symm (Fin.cast hcard.symm a) = y := by
        exact congrArg Subtype.val
          ((colSlots.orderIsoOfFin rfl).apply_symm_apply ⟨y, hycol⟩)
      change
        P.slotCol
          (finSumFinEquiv.symm
            (colSlots.orderEmbOfFin hcard.symm (Fin.cast hcard.symm a))) < x
      rw [ha]
      exact hyx
    · exact congrArg Subtype.val
        ((colSlots.orderIsoOfFin rfl).apply_symm_apply ⟨y, hycol⟩)

lemma ofFinsets_sorted_left_row_le_of_slot_count {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card)
    (i : Fin rowSlots.card) (x : Fin m)
    (hcount :
      (i : ℕ) <
        (rowSlots.filter fun y =>
          P.slotRow (finSumFinEquiv.symm y) ≤ x).card) :
    (ofFinsets P rowSlots colSlots hcard).toPair.left.sorted.row i ≤ x := by
  have hdomain :
      (i : ℕ) <
        (Finset.univ.filter fun a : Fin rowSlots.card =>
          (ofFinsets P rowSlots colSlots hcard).toPair.left.row a ≤ x).card := by
    simpa [ofFinsets_left_row_filter_card_eq] using hcount
  exact RawMinorIndex.sorted_row_le_of_card_filter_le
    (ofFinsets P rowSlots colSlots hcard).toPair.left i x hdomain

lemma ofFinsets_sorted_left_col_le_of_slot_count {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card)
    (i : Fin rowSlots.card) (x : Fin n)
    (hcount :
      (i : ℕ) <
        (colSlots.filter fun y =>
          P.slotCol (finSumFinEquiv.symm y) ≤ x).card) :
    (ofFinsets P rowSlots colSlots hcard).toPair.left.sorted.col i ≤ x := by
  have hdomain :
      (i : ℕ) <
        (Finset.univ.filter fun a : Fin rowSlots.card =>
          (ofFinsets P rowSlots colSlots hcard).toPair.left.col a ≤ x).card := by
    simpa [ofFinsets_left_col_filter_card_eq] using hcount
  exact RawMinorIndex.sorted_col_le_of_card_filter_le
    (ofFinsets P rowSlots colSlots hcard).toPair.left i x hdomain

lemma ofFinsets_sorted_left_row_lt_of_slot_count {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card)
    (i : Fin rowSlots.card) (x : Fin m)
    (hcount :
      (i : ℕ) <
        (rowSlots.filter fun y =>
          P.slotRow (finSumFinEquiv.symm y) < x).card) :
    (ofFinsets P rowSlots colSlots hcard).toPair.left.sorted.row i < x := by
  have hdomain :
      (i : ℕ) <
        (Finset.univ.filter fun a : Fin rowSlots.card =>
          (ofFinsets P rowSlots colSlots hcard).toPair.left.row a < x).card := by
    simpa [ofFinsets_left_row_filter_card_lt_eq] using hcount
  exact RawMinorIndex.sorted_row_lt_of_card_filter_lt
    (ofFinsets P rowSlots colSlots hcard).toPair.left i x hdomain

lemma ofFinsets_sorted_left_col_lt_of_slot_count {m n : ℕ} (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card)
    (i : Fin rowSlots.card) (x : Fin n)
    (hcount :
      (i : ℕ) <
        (colSlots.filter fun y =>
          P.slotCol (finSumFinEquiv.symm y) < x).card) :
    (ofFinsets P rowSlots colSlots hcard).toPair.left.sorted.col i < x := by
  have hdomain :
      (i : ℕ) <
        (Finset.univ.filter fun a : Fin rowSlots.card =>
          (ofFinsets P rowSlots colSlots hcard).toPair.left.col a < x).card := by
    simpa [ofFinsets_left_col_filter_card_lt_eq] using hcount
  exact RawMinorIndex.sorted_col_lt_of_card_filter_lt
    (ofFinsets P rowSlots colSlots hcard).toPair.left i x hdomain

/-- The common square matrix of slot variables underlying every bi-reshuffle
of `P`.  Repeated ambient rows or columns are intentionally retained. -/
noncomputable def slotMatrix (k : Type*) [CommRing k] {m n : ℕ}
    (P : RawMinorPair m n) :
    Matrix (Fin (P.p + P.q)) (Fin (P.p + P.q))
      (MvPolynomial (Fin m × Fin n) k) :=
  fun i j =>
    MvPolynomial.X
      (P.slotRow (finSumFinEquiv.symm i),
        P.slotCol (finSumFinEquiv.symm j))

lemma ofFinsets_toPair_left_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) :
    RawMinorIndex.toPolynomial k
        (ofFinsets P rowSlots colSlots hcard).toPair.left =
      Matrix.det
        (Matrix.submatrix (slotMatrix k P)
          (rowSlots.orderEmbOfFin rfl)
          (colSlots.orderEmbOfFin hcard.symm)) := by
  unfold RawMinorIndex.toPolynomial
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.submatrix_apply, slotMatrix, toPair, genericMatrix_apply,
    ofFinsets_rowEquiv_inl, ofFinsets_colEquiv_inl]

lemma ofFinsets_toPair_right_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n)
    (rowSlots colSlots : Finset (Fin (P.p + P.q)))
    (hcard : rowSlots.card = colSlots.card) :
    RawMinorIndex.toPolynomial k
        (ofFinsets P rowSlots colSlots hcard).toPair.right =
      Matrix.det
        (Matrix.submatrix (slotMatrix k P)
          (rowSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]))
          (colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin, hcard]))) := by
  unfold RawMinorIndex.toPolynomial
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.submatrix_apply, slotMatrix, toPair, genericMatrix_apply,
    ofFinsets_rowEquiv_inr, ofFinsets_colEquiv_inr]

lemma ContainingSplit.toBiReshuffle_toPair_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    RawMinorPair.toPolynomial k S.toBiReshuffle.toPair =
      Matrix.det
          (Matrix.submatrix (slotMatrix k P)
            (S.rowSlots.orderEmbOfFin rfl)
            (S.colSlots.orderEmbOfFin S.card_eq.symm)) *
      Matrix.det
          (Matrix.submatrix (slotMatrix k P)
            (S.rowSlotsᶜ.orderEmbOfFin (by
              rw [Finset.card_compl, Fintype.card_fin]))
            (S.colSlotsᶜ.orderEmbOfFin (by
              rw [Finset.card_compl, Fintype.card_fin, S.card_eq]))) := by
  rw [RawMinorPair.toPolynomial]
  change
    RawMinorIndex.toPolynomial k
        (ofFinsets P S.rowSlots S.colSlots S.card_eq).toPair.left *
      RawMinorIndex.toPolynomial k
        (ofFinsets P S.rowSlots S.colSlots S.card_eq).toPair.right =
      _
  rw [ofFinsets_toPair_left_toPolynomial k P S.rowSlots S.colSlots S.card_eq]
  rw [ofFinsets_toPair_right_toPolynomial k P S.rowSlots S.colSlots S.card_eq]

lemma ContainingSplit.toBiReshuffle_toPair_laplacePolynomial {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair =
      MvPolynomial.C
          (RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair) *
        (Matrix.det
            (Matrix.submatrix (slotMatrix k P)
              (S.rowSlots.orderEmbOfFin rfl)
              (S.colSlots.orderEmbOfFin S.card_eq.symm)) *
          Matrix.det
            (Matrix.submatrix (slotMatrix k P)
            (S.rowSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin]))
              (S.colSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin, S.card_eq])))) := by
  rw [RawMinorPair.laplacePolynomial,
    ContainingSplit.toBiReshuffle_toPair_toPolynomial k S]

/-- The full Leibniz permutation obtained by gluing the two permutations from
the selected and complementary determinant blocks of a `ContainingSplit`.

It maps ambient column slots to ambient row slots. -/
noncomputable def ContainingSplit.colSplit {m n : ℕ}
    {P : RawMinorPair m n} (S : ContainingSplit P) :
    Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
      Fin (P.p + P.q) :=
  finSumEquivOfFinset S.card_eq.symm (by
    rw [Finset.card_compl, Fintype.card_fin]
    simp [S.card_eq])

noncomputable def ContainingSplit.rowSplit {m n : ℕ}
    {P : RawMinorPair m n} (S : ContainingSplit P) :
    Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
      Fin (P.p + P.q) :=
  finSumEquivOfFinset rfl (by
    rw [Finset.card_compl, Fintype.card_fin])

noncomputable def ContainingSplit.leibnizPerm {m n : ℕ}
    {P : RawMinorPair m n} (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    Equiv.Perm (Fin (P.p + P.q)) :=
  (S.colSplit.symm.trans (Equiv.sumCongr τ σ)).trans S.rowSplit

noncomputable def ContainingSplit.stdSplit {m n : ℕ}
    {P : RawMinorPair m n} (S : ContainingSplit P) :
    Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
      Fin (P.p + P.q) :=
  finSumFinEquivToTotal (P.p + P.q) S.rowSlots.card (by
    simpa using Finset.card_le_univ S.rowSlots)

noncomputable def ContainingSplit.rowSplitRel {m n : ℕ}
    {P : RawMinorPair m n} (S : ContainingSplit P) :
    Equiv.Perm (Fin S.rowSlots.card ⊕
      Fin (P.p + P.q - S.rowSlots.card)) :=
  S.rowSplit.trans S.stdSplit.symm

noncomputable def ContainingSplit.colSplitRel {m n : ℕ}
    {P : RawMinorPair m n} (S : ContainingSplit P) :
    Equiv.Perm (Fin S.rowSlots.card ⊕
      Fin (P.p + P.q - S.rowSlots.card)) :=
  S.colSplit.trans S.stdSplit.symm

noncomputable def ContainingSplit.splitSignFactor {m n : ℕ}
    {P : RawMinorPair m n} {R : Type*} [CommRing R]
    (S : ContainingSplit P) : R :=
  equivPermSign (R := R) S.rowSplitRel *
    equivPermSign (R := R) S.colSplitRel

lemma ContainingSplit.splitSignFactor_mul_self {m n : ℕ}
    {P : RawMinorPair m n} {R : Type*} [CommRing R]
    (S : ContainingSplit P) :
    S.splitSignFactor (R := R) * S.splitSignFactor (R := R) = 1 := by
  unfold ContainingSplit.splitSignFactor
  have hrow := equivPermSign_mul_self (R := R) S.rowSplitRel
  have hcol := equivPermSign_mul_self (R := R) S.colSplitRel
  calc
    (equivPermSign (R := R) S.rowSplitRel *
          equivPermSign (R := R) S.colSplitRel) *
        (equivPermSign (R := R) S.rowSplitRel *
          equivPermSign (R := R) S.colSplitRel)
        =
      (equivPermSign (R := R) S.rowSplitRel *
          equivPermSign (R := R) S.rowSplitRel) *
        (equivPermSign (R := R) S.colSplitRel *
          equivPermSign (R := R) S.colSplitRel) := by
          ring
    _ = 1 := by
          rw [hrow, hcol]
          ring

lemma ContainingSplit.sign_leibnizPerm {m n : ℕ}
    {P : RawMinorPair m n}
    (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    Equiv.Perm.sign (S.leibnizPerm τ σ) =
      Equiv.Perm.sign S.rowSplitRel *
        (Equiv.Perm.sign τ * Equiv.Perm.sign σ) *
          Equiv.Perm.sign S.colSplitRel := by
  classical
  let A := S.stdSplit
  let rrel : Equiv.Perm
      (Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card)) :=
    S.rowSplitRel
  let crel : Equiv.Perm
      (Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card)) :=
    S.colSplitRel
  have hconj :
      (A.trans (S.leibnizPerm τ σ)).trans A.symm =
        crel.symm.trans ((Equiv.Perm.sumCongr τ σ).trans rrel) := by
    ext x
    simp [A, rrel, crel, ContainingSplit.leibnizPerm,
      ContainingSplit.rowSplitRel, ContainingSplit.colSplitRel]
  have hsign :
      Equiv.Perm.sign (S.leibnizPerm τ σ) =
        Equiv.Perm.sign
          (crel.symm.trans ((Equiv.Perm.sumCongr τ σ).trans rrel)) := by
    rw [← hconj]
    exact (Equiv.Perm.sign_trans_trans_symm (S.leibnizPerm τ σ) A).symm
  rw [hsign]
  simp [rrel, crel, Equiv.Perm.sign_trans, Equiv.Perm.sign_sumCongr,
    mul_assoc, mul_comm, mul_left_comm]

lemma ContainingSplit.splitSignFactor_mul_blockSigns {m n : ℕ}
    {P : RawMinorPair m n} {R : Type*} [CommRing R]
    (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    S.splitSignFactor (R := R) *
        (equivPermSign (R := R) τ * equivPermSign (R := R) σ) =
      equivPermSign (R := R) (S.leibnizPerm τ σ) := by
  unfold ContainingSplit.splitSignFactor equivPermSign
  rw [S.sign_leibnizPerm τ σ]
  simp only [Units.val_mul, Int.cast_mul]
  ring

@[simp] lemma ContainingSplit.leibnizPerm_colSlots {m n : ℕ}
    {P : RawMinorPair m n} (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (j : Fin S.rowSlots.card) :
    S.leibnizPerm τ σ (S.colSlots.orderEmbOfFin S.card_eq.symm j) =
      S.rowSlots.orderEmbOfFin rfl (τ j) := by
  classical
  have hleft :
      S.colSplit.symm
          (S.colSlots.orderEmbOfFin S.card_eq.symm j) =
        Sum.inl j := by
    simpa [ContainingSplit.colSplit] using S.colSplit.left_inv (Sum.inl j)
  simp [ContainingSplit.leibnizPerm, hleft, ContainingSplit.rowSplit]

@[simp] lemma ContainingSplit.leibnizPerm_colSlots_compl {m n : ℕ}
    {P : RawMinorPair m n} (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (j : Fin (P.p + P.q - S.rowSlots.card)) :
    S.leibnizPerm τ σ
        (S.colSlotsᶜ.orderEmbOfFin (by
          rw [Finset.card_compl, Fintype.card_fin]
          simp [S.card_eq]) j) =
      S.rowSlotsᶜ.orderEmbOfFin (by
        rw [Finset.card_compl, Fintype.card_fin]) (σ j) := by
  classical
  have hright :
      S.colSplit.symm
          (S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp [S.card_eq]) j) =
        Sum.inr j := by
    simpa [ContainingSplit.colSplit] using S.colSplit.left_inv (Sum.inr j)
  simp [ContainingSplit.leibnizPerm, hright, ContainingSplit.rowSplit]

lemma ContainingSplit.leibnizPerm_pair_injective {m n : ℕ}
    {P : RawMinorPair m n} (S : ContainingSplit P) :
    Function.Injective
      (fun p : Equiv.Perm (Fin S.rowSlots.card) ×
          Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)) =>
        S.leibnizPerm p.1 p.2) := by
  classical
  intro a b hab
  cases a with
  | mk τa σa =>
      cases b with
      | mk τb σb =>
          change S.leibnizPerm τa σa = S.leibnizPerm τb σb at hab
          congr
          · ext j
            have h :=
              congrArg
                (fun e : Equiv.Perm (Fin (P.p + P.q)) =>
                  e (S.colSlots.orderEmbOfFin S.card_eq.symm j)) hab
            exact congrArg Fin.val
              ((S.rowSlots.orderEmbOfFin rfl).injective (by
                simpa using h))
          · ext j
            have h :=
              congrArg
                (fun e : Equiv.Perm (Fin (P.p + P.q)) =>
                  e
                    (S.colSlotsᶜ.orderEmbOfFin (by
                      rw [Finset.card_compl, Fintype.card_fin]
                      simp [S.card_eq]) j)) hab
            exact congrArg Fin.val
              ((S.rowSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin])).injective (by
                  simpa using h))

lemma ContainingSplit.rowSlots_eq_colSlots_image_of_leibnizPerm_eq
    {m n : ℕ} {P : RawMinorPair m n} (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (hπ : S.leibnizPerm τ σ = π) :
    S.rowSlots = S.colSlots.map π.toEmbedding := by
  classical
  subst π
  ext x
  constructor
  · intro hx
    let xr : {x // x ∈ S.rowSlots} := ⟨x, hx⟩
    let j : Fin S.rowSlots.card := (S.rowSlots.orderIsoOfFin rfl).symm xr
    have hxj : S.rowSlots.orderEmbOfFin rfl j = x := by
      exact congrArg Subtype.val
        ((S.rowSlots.orderIsoOfFin rfl).apply_symm_apply xr)
    refine Finset.mem_map.mpr ?_
    refine ⟨S.colSlots.orderEmbOfFin S.card_eq.symm (τ.symm j), ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem S.colSlots S.card_eq.symm (τ.symm j)
    · change S.leibnizPerm τ σ
          (S.colSlots.orderEmbOfFin S.card_eq.symm (τ.symm j)) = x
      rw [ContainingSplit.leibnizPerm_colSlots]
      simp [hxj]
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, hyx⟩
    let yc : {y // y ∈ S.colSlots} := ⟨y, hy⟩
    let j : Fin S.rowSlots.card := (S.colSlots.orderIsoOfFin S.card_eq.symm).symm yc
    have hyj : S.colSlots.orderEmbOfFin S.card_eq.symm j = y := by
      exact congrArg Subtype.val
        ((S.colSlots.orderIsoOfFin S.card_eq.symm).apply_symm_apply yc)
    have hrow :
        S.leibnizPerm τ σ y ∈ S.rowSlots := by
      rw [← hyj, ContainingSplit.leibnizPerm_colSlots]
      exact Finset.orderEmbOfFin_mem S.rowSlots rfl (τ j)
    have hyx' : S.leibnizPerm τ σ y = x := by
      simpa using hyx
    simpa [hyx'] using hrow

lemma ContainingSplit.eq_of_colSlots_eq_of_leibnizPerm_eq
    {m n : ℕ} {P : RawMinorPair m n}
    {S S' : ContainingSplit P}
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (τ' : Equiv.Perm (Fin S'.rowSlots.card))
    (σ' : Equiv.Perm (Fin (P.p + P.q - S'.rowSlots.card)))
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (hπ : S.leibnizPerm τ σ = π)
    (hπ' : S'.leibnizPerm τ' σ' = π)
    (hcol : S.colSlots = S'.colSlots) :
    S = S' := by
  have hrow : S.rowSlots = S'.rowSlots := by
    rw [S.rowSlots_eq_colSlots_image_of_leibnizPerm_eq τ σ π hπ,
      S'.rowSlots_eq_colSlots_image_of_leibnizPerm_eq τ' σ' π hπ',
      hcol]
  cases S with
  | mk rowSlots colSlots card_eq leftRows leftCols =>
      cases S' with
      | mk rowSlots' colSlots' card_eq' leftRows' leftCols' =>
          simp only at hrow hcol
          subst rowSlots'
          subst colSlots'
          rfl

lemma ContainingSplit.leibnizPerm_mem_rowSlots_compl_of_mem_colSlots_compl
    {m n : ℕ} {P : RawMinorPair m n} (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    {x : Fin (P.p + P.q)} (hx : x ∈ S.colSlotsᶜ) :
    S.leibnizPerm τ σ x ∈ S.rowSlotsᶜ := by
  classical
  let hcol :
      S.colSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    simp [S.card_eq]
  let x' : { x // x ∈ S.colSlotsᶜ } := ⟨x, hx⟩
  let j : Fin (P.p + P.q - S.rowSlots.card) :=
    ((S.colSlotsᶜ).orderIsoOfFin hcol).symm x'
  have hxj :
      (S.colSlotsᶜ.orderEmbOfFin hcol j) = x := by
    exact congrArg Subtype.val
      (((S.colSlotsᶜ).orderIsoOfFin hcol).apply_symm_apply x')
  rw [← hxj]
  rw [ContainingSplit.leibnizPerm_colSlots_compl]
  exact Finset.orderEmbOfFin_mem S.rowSlotsᶜ
    (by rw [Finset.card_compl, Fintype.card_fin]) (σ j)

lemma ContainingSplit.leftSlotFinset_union_permPreimage_subset_colSlots
    {m n : ℕ} {P : RawMinorPair m n} (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    leftSlotFinset P ∪
        permPreimageLeftSlotFinset P (S.leibnizPerm τ σ) ⊆
      S.colSlots := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hleft | hpre
  · exact S.leftCols hleft
  · by_contra hxcol
    have hxcomp : x ∈ S.colSlotsᶜ := by
      simpa [Finset.mem_compl] using hxcol
    have hrowcomp :
        S.leibnizPerm τ σ x ∈ S.rowSlotsᶜ :=
      S.leibnizPerm_mem_rowSlots_compl_of_mem_colSlots_compl τ σ hxcomp
    have hnotrow : S.leibnizPerm τ σ x ∉ S.rowSlots := by
      simpa [Finset.mem_compl] using hrowcomp
    have hleftrow :
        S.leibnizPerm τ σ x ∈ leftSlotFinset P :=
      (mem_permPreimageLeftSlotFinset_iff P (S.leibnizPerm τ σ) x).mp hpre
    exact hnotrow (S.leftRows hleftrow)

lemma ContainingSplit.colSlots_mem_Icc_leftSlotFinset_union_permPreimage
    {m n : ℕ} {P : RawMinorPair m n} (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    S.colSlots ∈
      Finset.Icc
        (leftSlotFinset P ∪
          permPreimageLeftSlotFinset P (S.leibnizPerm τ σ))
        Finset.univ := by
  exact Finset.mem_Icc.mpr
    ⟨S.leftSlotFinset_union_permPreimage_subset_colSlots τ σ,
      Finset.subset_univ _⟩

lemma ContainingSplit.colSlots_mem_Icc_of_leibnizPerm_eq
    {m n : ℕ} {P : RawMinorPair m n} (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (hπ : S.leibnizPerm τ σ = π) :
    S.colSlots ∈
      Finset.Icc
        (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
        Finset.univ := by
  subst π
  exact S.colSlots_mem_Icc_leftSlotFinset_union_permPreimage τ σ

noncomputable def ContainingSplit.ofColSlotsPerm
    {m n : ℕ} (P : RawMinorPair m n)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (s : Finset (Fin (P.p + P.q)))
    (hs : s ∈ Finset.Icc
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π) Finset.univ) :
    ContainingSplit P where
  rowSlots := s.map π.toEmbedding
  colSlots := s
  card_eq := by
    simp
  leftRows := by
    intro x hxleft
    have hsub :
        leftSlotFinset P ∪ permPreimageLeftSlotFinset P π ⊆ s :=
      (Finset.mem_Icc.mp hs).1
    have hpre :
        π.symm x ∈ permPreimageLeftSlotFinset P π := by
      rw [mem_permPreimageLeftSlotFinset_iff]
      simp [hxleft]
    have hxs : π.symm x ∈ s :=
      hsub (Finset.mem_union_right (leftSlotFinset P) hpre)
    exact Finset.mem_map.mpr
      ⟨π.symm x, hxs, by simp⟩
  leftCols := by
    intro x hxleft
    exact (Finset.mem_Icc.mp hs).1
      (Finset.mem_union_left (permPreimageLeftSlotFinset P π) hxleft)

@[simp] lemma ContainingSplit.ofColSlotsPerm_rowSlots
    {m n : ℕ} (P : RawMinorPair m n)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (s : Finset (Fin (P.p + P.q)))
    (hs : s ∈ Finset.Icc
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π) Finset.univ) :
    (ContainingSplit.ofColSlotsPerm P π s hs).rowSlots =
      s.map π.toEmbedding := rfl

@[simp] lemma ContainingSplit.ofColSlotsPerm_colSlots
    {m n : ℕ} (P : RawMinorPair m n)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (s : Finset (Fin (P.p + P.q)))
    (hs : s ∈ Finset.Icc
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π) Finset.univ) :
    (ContainingSplit.ofColSlotsPerm P π s hs).colSlots = s := rfl

lemma ContainingSplit.exists_leibnizPerm_eq_of_colSlots_mem_Icc
    {m n : ℕ} (P : RawMinorPair m n)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (s : Finset (Fin (P.p + P.q)))
    (hs : s ∈ Finset.Icc
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π) Finset.univ) :
    ∃ S : ContainingSplit P,
      ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
      ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        S.colSlots = s ∧ S.leibnizPerm τ σ = π := by
  classical
  let S : ContainingSplit P := ContainingSplit.ofColSlotsPerm P π s hs
  let τFun : Fin S.rowSlots.card → Fin S.rowSlots.card := fun j =>
    (S.rowSlots.orderIsoOfFin rfl).symm
      ⟨π (S.colSlots.orderEmbOfFin S.card_eq.symm j), by
        have hj : S.colSlots.orderEmbOfFin S.card_eq.symm j ∈ S.colSlots :=
          Finset.orderEmbOfFin_mem S.colSlots S.card_eq.symm j
        change π (S.colSlots.orderEmbOfFin S.card_eq.symm j) ∈ s.map π.toEmbedding
        exact Finset.mem_map.mpr
          ⟨S.colSlots.orderEmbOfFin S.card_eq.symm j, by simp [S], rfl⟩⟩
  have hτFun :
      ∀ j : Fin S.rowSlots.card,
        S.rowSlots.orderEmbOfFin rfl (τFun j) =
          π (S.colSlots.orderEmbOfFin S.card_eq.symm j) := by
    intro j
    exact congrArg Subtype.val
      ((S.rowSlots.orderIsoOfFin rfl).apply_symm_apply
        ⟨π (S.colSlots.orderEmbOfFin S.card_eq.symm j), by
          have hj : S.colSlots.orderEmbOfFin S.card_eq.symm j ∈ S.colSlots :=
            Finset.orderEmbOfFin_mem S.colSlots S.card_eq.symm j
          change π (S.colSlots.orderEmbOfFin S.card_eq.symm j) ∈
            s.map π.toEmbedding
          exact Finset.mem_map.mpr
            ⟨S.colSlots.orderEmbOfFin S.card_eq.symm j, by simp [S], rfl⟩⟩)
  have hτInj : Function.Injective τFun := by
    intro a b hab
    have h := congrArg (fun j => S.rowSlots.orderEmbOfFin rfl j) hab
    simp only at h
    rw [hτFun a, hτFun b] at h
    exact (S.colSlots.orderEmbOfFin S.card_eq.symm).injective (π.injective h)
  have hτBij : Function.Bijective τFun :=
    (Fintype.bijective_iff_injective_and_card τFun).mpr ⟨hτInj, rfl⟩
  let τ : Equiv.Perm (Fin S.rowSlots.card) := Equiv.ofBijective τFun hτBij
  have hτ :
      ∀ j : Fin S.rowSlots.card,
        S.rowSlots.orderEmbOfFin rfl (τ j) =
          π (S.colSlots.orderEmbOfFin S.card_eq.symm j) := by
    intro j
    exact hτFun j
  let hrowCompl :
      S.rowSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  let hcolCompl :
      S.colSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    simp [S.card_eq]
  let σFun :
      Fin (P.p + P.q - S.rowSlots.card) →
        Fin (P.p + P.q - S.rowSlots.card) := fun j =>
    (S.rowSlotsᶜ.orderIsoOfFin hrowCompl).symm
      ⟨π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j), by
        have hjc :
            S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ S.colSlotsᶜ :=
          Finset.orderEmbOfFin_mem S.colSlotsᶜ hcolCompl j
        rw [Finset.mem_compl] at hjc
        rw [Finset.mem_compl]
        intro hrow
        change π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) ∈ s.map π.toEmbedding at hrow
        rcases Finset.mem_map.mp hrow with
          ⟨y, hy, hyπ⟩
        have hxy :
            S.colSlotsᶜ.orderEmbOfFin hcolCompl j = y :=
          π.injective hyπ.symm
        have hxmem : S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ S.colSlots := by
          change S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ s
          rw [hxy]
          exact hy
        exact hjc hxmem⟩
  have hσFun :
      ∀ j : Fin (P.p + P.q - S.rowSlots.card),
        S.rowSlotsᶜ.orderEmbOfFin hrowCompl (σFun j) =
          π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) := by
    intro j
    exact congrArg Subtype.val
      ((S.rowSlotsᶜ.orderIsoOfFin hrowCompl).apply_symm_apply
        ⟨π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j), by
          have hjc :
              S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ S.colSlotsᶜ :=
            Finset.orderEmbOfFin_mem S.colSlotsᶜ hcolCompl j
          rw [Finset.mem_compl] at hjc
          rw [Finset.mem_compl]
          intro hrow
          change π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) ∈ s.map π.toEmbedding at hrow
          rcases Finset.mem_map.mp hrow with
            ⟨y, hy, hyπ⟩
          have hxy :
              S.colSlotsᶜ.orderEmbOfFin hcolCompl j = y :=
            π.injective hyπ.symm
          have hxmem : S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ S.colSlots := by
            change S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ s
            rw [hxy]
            exact hy
          exact hjc hxmem⟩)
  have hσInj : Function.Injective σFun := by
    intro a b hab
    have h := congrArg (fun j => S.rowSlotsᶜ.orderEmbOfFin hrowCompl j) hab
    simp only at h
    rw [hσFun a, hσFun b] at h
    exact (S.colSlotsᶜ.orderEmbOfFin hcolCompl).injective (π.injective h)
  have hσBij : Function.Bijective σFun :=
    (Fintype.bijective_iff_injective_and_card σFun).mpr ⟨hσInj, rfl⟩
  let σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)) :=
    Equiv.ofBijective σFun hσBij
  have hσ :
      ∀ j : Fin (P.p + P.q - S.rowSlots.card),
        S.rowSlotsᶜ.orderEmbOfFin hrowCompl (σ j) =
          π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) := by
    intro j
    exact hσFun j
  refine ⟨S, τ, σ, rfl, ?_⟩
  ext x
  by_cases hx : x ∈ S.colSlots
  · let x' : { x // x ∈ S.colSlots } := ⟨x, hx⟩
    let j : Fin S.rowSlots.card := (S.colSlots.orderIsoOfFin S.card_eq.symm).symm x'
    have hxj : S.colSlots.orderEmbOfFin S.card_eq.symm j = x := by
      exact congrArg Subtype.val
        ((S.colSlots.orderIsoOfFin S.card_eq.symm).apply_symm_apply x')
    rw [← hxj]
    rw [ContainingSplit.leibnizPerm_colSlots]
    simpa using congrArg Fin.val (hτ j)
  · have hxc : x ∈ S.colSlotsᶜ := by
      simpa [Finset.mem_compl] using hx
    let x' : { x // x ∈ S.colSlotsᶜ } := ⟨x, hxc⟩
    let j : Fin (P.p + P.q - S.rowSlots.card) :=
      (S.colSlotsᶜ.orderIsoOfFin hcolCompl).symm x'
    have hxj : S.colSlotsᶜ.orderEmbOfFin hcolCompl j = x := by
      exact congrArg Subtype.val
        ((S.colSlotsᶜ.orderIsoOfFin hcolCompl).apply_symm_apply x')
    rw [← hxj]
    rw [ContainingSplit.leibnizPerm_colSlots_compl]
    simpa using congrArg Fin.val (hσ j)

theorem ContainingSplit.exists_leibnizPerm_eq_and_colSlots_iff_mem_Icc
    {m n : ℕ} (P : RawMinorPair m n)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (s : Finset (Fin (P.p + P.q))) :
    (∃ S : ContainingSplit P,
      ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
      ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        S.colSlots = s ∧ S.leibnizPerm τ σ = π) ↔
      s ∈ Finset.Icc
        (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
        Finset.univ := by
  constructor
  · rintro ⟨S, τ, σ, rfl, hπ⟩
    exact S.colSlots_mem_Icc_of_leibnizPerm_eq τ σ π hπ
  · intro hs
    exact ContainingSplit.exists_leibnizPerm_eq_of_colSlots_mem_Icc P π s hs

/-- For a fixed ambient Leibniz permutation `π`, the possible column-slot sets
of all `ContainingSplit` terms whose two local permutations glue to `π` are
exactly the interval from `left ∪ π⁻¹(left)` to `univ`. -/
theorem ContainingSplit.fixedLeibnizPerm_colSlots_iff_mem_Icc
    {m n : ℕ} (P : RawMinorPair m n)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (s : Finset (Fin (P.p + P.q))) :
    (∃ S : ContainingSplit P,
      ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
      ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        S.leibnizPerm τ σ = π ∧ S.colSlots = s) ↔
      s ∈ Finset.Icc
        (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
        Finset.univ := by
  rw [← ContainingSplit.exists_leibnizPerm_eq_and_colSlots_iff_mem_Icc P π s]
  constructor
  · rintro ⟨S, τ, σ, hπ, hcols⟩
    exact ⟨S, τ, σ, hcols, hπ⟩
  · rintro ⟨S, τ, σ, hcols, hπ⟩
    exact ⟨S, τ, σ, hπ, hcols⟩

noncomputable def ContainingSplit.colSlotsLeibnizFiberEquivIcc
    {m n : ℕ} (P : RawMinorPair m n)
    (π : Equiv.Perm (Fin (P.p + P.q))) :
    { s : Finset (Fin (P.p + P.q)) //
      ∃ S : ContainingSplit P,
      ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
      ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        S.colSlots = s ∧ S.leibnizPerm τ σ = π } ≃
    { s : Finset (Fin (P.p + P.q)) //
      s ∈ Finset.Icc
        (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
        Finset.univ } where
  toFun s :=
    ⟨s.1,
      (ContainingSplit.exists_leibnizPerm_eq_and_colSlots_iff_mem_Icc P π s.1).mp
        s.2⟩
  invFun s :=
    ⟨s.1,
      (ContainingSplit.exists_leibnizPerm_eq_and_colSlots_iff_mem_Icc P π s.1).mpr
        s.2⟩
  left_inv := by
    intro s
    ext
    rfl
  right_inv := by
    intro s
    ext
    rfl

lemma ContainingSplit.sum_colSlots_leibnizFiber_eq_sum_Icc
    {m n : ℕ} {P : RawMinorPair m n}
    {M : Type*} [AddCommMonoid M]
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (f : Finset (Fin (P.p + P.q)) → M) :
    (∑ s : { s : Finset (Fin (P.p + P.q)) //
        ∃ S : ContainingSplit P,
        ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
        ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
          S.colSlots = s ∧ S.leibnizPerm τ σ = π },
      f s.1) =
    ∑ s : { s : Finset (Fin (P.p + P.q)) //
        s ∈ Finset.Icc
          (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
          Finset.univ },
      f s.1 := by
  classical
  refine Fintype.sum_equiv
    (ContainingSplit.colSlotsLeibnizFiberEquivIcc P π)
    (fun s => f s.1) (fun s => f s.1) ?_
  intro s
  rfl

lemma ContainingSplit.sum_colSlots_leibnizFiber_eq_finset_sum_Icc
    {m n : ℕ} {P : RawMinorPair m n}
    {M : Type*} [AddCommMonoid M]
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (f : Finset (Fin (P.p + P.q)) → M) :
    (∑ s : { s : Finset (Fin (P.p + P.q)) //
        ∃ S : ContainingSplit P,
        ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
        ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
          S.colSlots = s ∧ S.leibnizPerm τ σ = π },
      f s.1) =
    ∑ s ∈ Finset.Icc
        (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
        Finset.univ,
      f s := by
  classical
  rw [ContainingSplit.sum_colSlots_leibnizFiber_eq_sum_Icc (P := P) π f]
  let interval : Finset (Finset (Fin (P.p + P.q))) :=
    Finset.Icc
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
      Finset.univ
  letI : Fintype { s : Finset (Fin (P.p + P.q)) // s ∈ interval } :=
    Finset.Subtype.fintype interval
  change (∑ s : { s : Finset (Fin (P.p + P.q)) // s ∈ interval }, f s.1) =
    ∑ s ∈ interval, f s
  have huniv :
      (Finset.univ : Finset
        { s : Finset (Fin (P.p + P.q)) // s ∈ interval }) =
        interval.attach := by
    ext s
    constructor
    · intro _
      exact Finset.mem_attach interval s
    · intro _
      exact Finset.mem_univ s
  rw [← interval.sum_attach f]
  change
      (∑ s ∈ (Finset.univ : Finset
        { s : Finset (Fin (P.p + P.q)) // s ∈ interval }), f s.1) =
      ∑ s ∈ interval.attach, f s.1
  rw [huniv]

lemma ContainingSplit.leibnizPerm_product_split {m n : ℕ}
    {Rng : Type*} [CommMonoid Rng] {P : RawMinorPair m n}
    (S : ContainingSplit P)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (M : Matrix (Fin (P.p + P.q)) (Fin (P.p + P.q)) Rng) :
    (∏ j : Fin (P.p + P.q), M (S.leibnizPerm τ σ j) j) =
      (∏ j : Fin S.rowSlots.card,
        M (S.rowSlots.orderEmbOfFin rfl (τ j))
          (S.colSlots.orderEmbOfFin S.card_eq.symm j)) *
      (∏ j : Fin (P.p + P.q - S.rowSlots.card),
        M (S.rowSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]) (σ j))
          (S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp [S.card_eq]) j)) := by
  classical
  let colSplit :
      Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card) ≃
        Fin (P.p + P.q) :=
    finSumEquivOfFinset S.card_eq.symm (by
      rw [Finset.card_compl, Fintype.card_fin]
      simp [S.card_eq])
  rw [← Equiv.prod_comp
    colSplit
    (fun j : Fin (P.p + P.q) => M (S.leibnizPerm τ σ j) j)]
  rw [Fintype.prod_sum_type]
  simp [colSplit]

lemma ContainingSplit.det_mul_det_eq_sum_leibnizPerm_terms {m n : ℕ}
    {Rng : Type*} [CommRing Rng] {P : RawMinorPair m n}
    (S : ContainingSplit P)
    (M : Matrix (Fin (P.p + P.q)) (Fin (P.p + P.q)) Rng) :
    Matrix.det
        (Matrix.submatrix M
          (S.rowSlots.orderEmbOfFin rfl)
          (S.colSlots.orderEmbOfFin S.card_eq.symm)) *
      Matrix.det
        (Matrix.submatrix M
          (S.rowSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]))
          (S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp [S.card_eq]))) =
      ∑ p : Equiv.Perm (Fin S.rowSlots.card) ×
          Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        ((Equiv.Perm.sign p.1 : Rng) *
            (Equiv.Perm.sign p.2 : Rng)) *
          ∏ j : Fin (P.p + P.q), M (S.leibnizPerm p.1 p.2 j) j := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply']
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [Matrix.submatrix_apply]
  rw [← Fintype.sum_prod_type' (γ := Rng)
    (f := fun τ σ =>
      ((Equiv.Perm.sign τ : Rng) *
          ∏ j : Fin S.rowSlots.card,
            M (S.rowSlots.orderEmbOfFin rfl (τ j))
              (S.colSlots.orderEmbOfFin S.card_eq.symm j)) *
        ((Equiv.Perm.sign σ : Rng) *
          ∏ j : Fin (P.p + P.q - S.rowSlots.card),
            M (S.rowSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin]) (σ j))
              (S.colSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin]
                simp [S.card_eq]) j)))]
  refine Finset.sum_congr rfl ?_
  rintro ⟨τ, σ⟩ _hp
  have hprod := S.leibnizPerm_product_split τ σ M
  rw [hprod]
  ring

lemma ContainingSplit.toBiReshuffle_toPair_laplacePolynomial_eq_sum_leibnizPerm_terms
    {m n : ℕ} (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (S : ContainingSplit P) :
    RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair =
      ∑ p : Equiv.Perm (Fin S.rowSlots.card) ×
          Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        MvPolynomial.C
            (RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign p.1 :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign p.2 :
              MvPolynomial (Fin m × Fin n) k)) *
            ∏ j : Fin (P.p + P.q),
              slotMatrix k P (S.leibnizPerm p.1 p.2 j) j) := by
  classical
  rw [ContainingSplit.toBiReshuffle_toPair_laplacePolynomial k S]
  rw [ContainingSplit.det_mul_det_eq_sum_leibnizPerm_terms
    (S := S) (M := slotMatrix k P)]
  rw [Finset.mul_sum]

/-- One Leibniz term occurring after expanding both determinant blocks attached
to a containing split. -/
abbrev ContainingSplit.LeibnizTerm {m n : ℕ} (P : RawMinorPair m n) :=
  Σ S : ContainingSplit P,
    Equiv.Perm (Fin S.rowSlots.card) ×
      Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))

namespace ContainingSplit.LeibnizTerm

noncomputable def ambientPerm {m n : ℕ} {P : RawMinorPair m n}
    (X : ContainingSplit.LeibnizTerm P) :
    Equiv.Perm (Fin (P.p + P.q)) :=
  X.1.leibnizPerm X.2.1 X.2.2

@[simp] lemma ambientPerm_apply {m n : ℕ} {P : RawMinorPair m n}
    (X : ContainingSplit.LeibnizTerm P) (j : Fin (P.p + P.q)) :
    X.ambientPerm j = X.1.leibnizPerm X.2.1 X.2.2 j := rfl

lemma colSlots_mem_Icc {m n : ℕ} {P : RawMinorPair m n}
    (X : ContainingSplit.LeibnizTerm P) :
    X.1.colSlots ∈ Finset.Icc
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P X.ambientPerm)
      Finset.univ := by
  exact X.1.colSlots_mem_Icc_leftSlotFinset_union_permPreimage
    X.2.1 X.2.2

noncomputable def toAmbientColSlots {m n : ℕ} {P : RawMinorPair m n}
    (X : ContainingSplit.LeibnizTerm P) :
    Σ π : Equiv.Perm (Fin (P.p + P.q)),
      { C : Finset (Fin (P.p + P.q)) //
        C ∈ Finset.Icc
          (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
          Finset.univ } :=
  ⟨X.ambientPerm, ⟨X.1.colSlots, X.colSlots_mem_Icc⟩⟩

@[simp] lemma toAmbientColSlots_fst {m n : ℕ} {P : RawMinorPair m n}
    (X : ContainingSplit.LeibnizTerm P) :
    (X.toAmbientColSlots).1 = X.ambientPerm := rfl

@[simp] lemma toAmbientColSlots_snd_val {m n : ℕ} {P : RawMinorPair m n}
    (X : ContainingSplit.LeibnizTerm P) :
    (X.toAmbientColSlots).2.1 = X.1.colSlots := rfl

abbrev AmbientColSlots {m n : ℕ} (P : RawMinorPair m n) :=
  { pc : Equiv.Perm (Fin (P.p + P.q)) × Finset (Fin (P.p + P.q)) //
    pc.2 ∈ Finset.Icc
      (leftSlotFinset P ∪ permPreimageLeftSlotFinset P pc.1)
      Finset.univ }

noncomputable def toAmbientColSlotsFlat {m n : ℕ} {P : RawMinorPair m n}
    (X : ContainingSplit.LeibnizTerm P) :
    AmbientColSlots P :=
  ⟨(X.ambientPerm, X.1.colSlots), X.colSlots_mem_Icc⟩

lemma toAmbientColSlotsFlat_injective {m n : ℕ} {P : RawMinorPair m n} :
    Function.Injective
      (@ContainingSplit.LeibnizTerm.toAmbientColSlotsFlat m n P) := by
  classical
  intro X Y h
  cases X with
  | mk S p =>
      cases p with
      | mk τ σ =>
          cases Y with
          | mk S' p' =>
              cases p' with
              | mk τ' σ' =>
                  have hπ :
                      S.leibnizPerm τ σ = S'.leibnizPerm τ' σ' :=
                    congrArg (fun z : AmbientColSlots P => z.1.1) h
                  have hcol : S.colSlots = S'.colSlots := by
                    exact congrArg (fun z : AmbientColSlots P => z.1.2) h
                  have hS : S = S' :=
                    ContainingSplit.eq_of_colSlots_eq_of_leibnizPerm_eq
                      (S := S) (S' := S') τ σ τ' σ'
                      (S.leibnizPerm τ σ) rfl hπ.symm hcol
                  cases hS
                  have hp : (τ, σ) = (τ', σ') :=
                    S.leibnizPerm_pair_injective hπ
                  cases hp
                  rfl

lemma toAmbientColSlotsFlat_surjective {m n : ℕ} (P : RawMinorPair m n) :
    Function.Surjective
      (@ContainingSplit.LeibnizTerm.toAmbientColSlotsFlat m n P) := by
  classical
  intro Y
  rcases Y with ⟨⟨π, C⟩, hC⟩
  rcases ContainingSplit.exists_leibnizPerm_eq_of_colSlots_mem_Icc
      P π C hC with ⟨S, τ, σ, hcols, hπ⟩
  refine ⟨⟨S, (τ, σ)⟩, ?_⟩
  subst π
  subst C
  rfl

noncomputable def equivAmbientColSlotsFlat {m n : ℕ} (P : RawMinorPair m n) :
    ContainingSplit.LeibnizTerm P ≃ AmbientColSlots P :=
  Equiv.ofBijective
    (@ContainingSplit.LeibnizTerm.toAmbientColSlotsFlat m n P)
    ⟨toAmbientColSlotsFlat_injective, toAmbientColSlotsFlat_surjective P⟩

noncomputable def ambientColSlotsEquivSigma {m n : ℕ} (P : RawMinorPair m n) :
    AmbientColSlots P ≃
      Σ π : Equiv.Perm (Fin (P.p + P.q)),
        { C : Finset (Fin (P.p + P.q)) //
          C ∈ Finset.Icc
            (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
            Finset.univ } where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv := by
    intro z
    rfl
  right_inv := by
    intro z
    rfl

noncomputable def equivAmbientColSlots {m n : ℕ} (P : RawMinorPair m n) :
    ContainingSplit.LeibnizTerm P ≃
      Σ π : Equiv.Perm (Fin (P.p + P.q)),
        { C : Finset (Fin (P.p + P.q)) //
          C ∈ Finset.Icc
            (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
            Finset.univ } :=
  (equivAmbientColSlotsFlat P).trans (ambientColSlotsEquivSigma P)

lemma sum_eq_sum_ambient_Icc {m n : ℕ} {P : RawMinorPair m n}
    {M : Type*} [AddCommMonoid M]
    (f : ContainingSplit.LeibnizTerm P → M)
    (g :
      (π : Equiv.Perm (Fin (P.p + P.q))) →
        { C : Finset (Fin (P.p + P.q)) //
          C ∈ Finset.Icc
            (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
            Finset.univ } → M)
    (h :
      ∀ X : ContainingSplit.LeibnizTerm P,
        f X =
          g X.ambientPerm
            ⟨X.1.colSlots, X.colSlots_mem_Icc⟩) :
    (∑ X : ContainingSplit.LeibnizTerm P, f X) =
      ∑ π : Equiv.Perm (Fin (P.p + P.q)),
        ∑ C : { C : Finset (Fin (P.p + P.q)) //
          C ∈ Finset.Icc
            (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
            Finset.univ },
          g π C := by
  classical
  calc
    (∑ X : ContainingSplit.LeibnizTerm P, f X)
        =
      ∑ Y :
          (Σ π : Equiv.Perm (Fin (P.p + P.q)),
            { C : Finset (Fin (P.p + P.q)) //
              C ∈ Finset.Icc
                (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
                Finset.univ }),
        g Y.1 Y.2 := by
          refine Fintype.sum_equiv
            (ContainingSplit.LeibnizTerm.equivAmbientColSlots P)
            f (fun Y => g Y.1 Y.2) ?_
          intro X
          simpa [ContainingSplit.LeibnizTerm.equivAmbientColSlots,
            ContainingSplit.LeibnizTerm.equivAmbientColSlotsFlat,
            ContainingSplit.LeibnizTerm.ambientColSlotsEquivSigma,
            ContainingSplit.LeibnizTerm.toAmbientColSlotsFlat] using h X
    _ =
      ∑ π : Equiv.Perm (Fin (P.p + P.q)),
        ∑ C : { C : Finset (Fin (P.p + P.q)) //
          C ∈ Finset.Icc
            (leftSlotFinset P ∪ permPreimageLeftSlotFinset P π)
            Finset.univ },
          g π C := by
          rw [Fintype.sum_sigma]

end ContainingSplit.LeibnizTerm

lemma ContainingSplit.sum_laplacePolynomial_eq_sum_leibnizTerm
    {m n : ℕ} (k : Type*) [Field k] {P : RawMinorPair m n}
    (coeff : ContainingSplit P → k) :
    (∑ S : ContainingSplit P,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) =
      ∑ X : ContainingSplit.LeibnizTerm P,
        MvPolynomial.C (coeff X.1) *
          (MvPolynomial.C
              (RawMinorPair.laplaceCoeff k X.1.toBiReshuffle.toPair) *
            (((Equiv.Perm.sign X.2.1 :
                MvPolynomial (Fin m × Fin n) k) *
              (Equiv.Perm.sign X.2.2 :
                MvPolynomial (Fin m × Fin n) k)) *
              ∏ j : Fin (P.p + P.q),
                slotMatrix k P (X.ambientPerm j) j)) := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [ContainingSplit.toBiReshuffle_toPair_laplacePolynomial_eq_sum_leibnizPerm_terms
    k S]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨τ, σ⟩ _hτσ
  simp [ContainingSplit.LeibnizTerm.ambientPerm]

@[simp] lemma HodgeColSplit.colSlots_card {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    S.colSlots.card = S.rowSlots.card := by
  simpa [HodgeColSplit.colSlots] using S.card_eq.symm

@[simp] lemma HodgeColSplit.colSlots_compl_card {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    S.colSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
  rw [Finset.card_compl, Fintype.card_fin]
  exact congrArg (fun r => P.p + P.q - r) S.colSlots_card

@[simp] lemma HodgeRowSplit.colSlots_card {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    S.colSlots.card = S.rowSlots.card := by
  simpa [HodgeRowSplit.rowSlots] using S.card_eq.symm

@[simp] lemma HodgeRowSplit.colSlots_compl_card {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    S.colSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
  rw [Finset.card_compl, Fintype.card_fin]
  exact congrArg (fun r => P.p + P.q - r) S.colSlots_card

lemma HodgeColSplit.toBiReshuffle_toPair_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    RawMinorPair.toPolynomial k S.toBiReshuffle.toPair =
      Matrix.det
          (Matrix.submatrix (slotMatrix k P)
            (S.rowSlots.orderEmbOfFin rfl)
            (S.colSlots.orderEmbOfFin S.card_eq.symm)) *
        Matrix.det
          (Matrix.submatrix (slotMatrix k P)
            (S.rowSlotsᶜ.orderEmbOfFin (by
              rw [Finset.card_compl, Fintype.card_fin]))
            (S.colSlotsᶜ.orderEmbOfFin (by
              simp))) := by
  rw [RawMinorPair.toPolynomial]
  change
    RawMinorIndex.toPolynomial k
        (ofFinsets P S.rowSlots S.colSlots S.card_eq).toPair.left *
      RawMinorIndex.toPolynomial k
        (ofFinsets P S.rowSlots S.colSlots S.card_eq).toPair.right =
      _
  rw [ofFinsets_toPair_left_toPolynomial k P S.rowSlots S.colSlots S.card_eq]
  rw [ofFinsets_toPair_right_toPolynomial k P S.rowSlots S.colSlots S.card_eq]

lemma HodgeColSplit.toBiReshuffle_toPair_laplacePolynomial {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair =
      MvPolynomial.C
          (RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair) *
        (Matrix.det
            (Matrix.submatrix (slotMatrix k P)
              (S.rowSlots.orderEmbOfFin rfl)
              (S.colSlots.orderEmbOfFin S.card_eq.symm)) *
          Matrix.det
            (Matrix.submatrix (slotMatrix k P)
            (S.rowSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin]))
              (S.colSlotsᶜ.orderEmbOfFin (by
                simp)))) := by
  rw [RawMinorPair.laplacePolynomial,
    HodgeColSplit.toBiReshuffle_toPair_toPolynomial k S]

lemma HodgeColSplit.sign_leibnizPerm {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    Equiv.Perm.sign (S.leibnizPerm τ σ) =
      Equiv.Perm.sign S.rowSplitRel *
        (Equiv.Perm.sign τ * Equiv.Perm.sign σ) *
          Equiv.Perm.sign S.colSplitRel := by
  classical
  let A := S.stdSplit
  let rrel : Equiv.Perm
      (Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card)) :=
    S.rowSplitRel
  let crel : Equiv.Perm
      (Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card)) :=
    S.colSplitRel
  have hconj :
      (A.trans (S.leibnizPerm τ σ)).trans A.symm =
        crel.symm.trans ((Equiv.Perm.sumCongr τ σ).trans rrel) := by
    ext x
    simp [A, rrel, crel, HodgeColSplit.leibnizPerm,
      HodgeColSplit.rowSplitRel, HodgeColSplit.colSplitRel]
  have hsign :
      Equiv.Perm.sign (S.leibnizPerm τ σ) =
        Equiv.Perm.sign
          (crel.symm.trans ((Equiv.Perm.sumCongr τ σ).trans rrel)) := by
    rw [← hconj]
    exact (Equiv.Perm.sign_trans_trans_symm (S.leibnizPerm τ σ) A).symm
  rw [hsign]
  simp [rrel, crel, Equiv.Perm.sign_trans, Equiv.Perm.sign_sumCongr,
    mul_assoc, mul_comm, mul_left_comm]

lemma HodgeColSplit.splitSignFactor_mul_blockSigns {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    {R : Type*} [CommRing R]
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    S.splitSignFactor (R := R) *
        (equivPermSign (R := R) τ * equivPermSign (R := R) σ) =
      equivPermSign (R := R) (S.leibnizPerm τ σ) := by
  unfold HodgeColSplit.splitSignFactor equivPermSign
  rw [S.sign_leibnizPerm τ σ]
  simp only [Units.val_mul, Int.cast_mul]
  ring

@[simp] lemma HodgeColSplit.leibnizPerm_colSlots {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (j : Fin S.rowSlots.card) :
    S.leibnizPerm τ σ (S.colSlots.orderEmbOfFin S.card_eq.symm j) =
      S.rowSlots.orderEmbOfFin rfl (τ j) := by
  classical
  have hleft :
      S.colSplit.symm
          (S.colSlots.orderEmbOfFin S.card_eq.symm j) =
        Sum.inl j := by
    simpa [HodgeColSplit.colSplit] using S.colSplit.left_inv (Sum.inl j)
  simp [HodgeColSplit.leibnizPerm, hleft, HodgeColSplit.rowSplit]

@[simp] lemma HodgeColSplit.leibnizPerm_colSlots_compl {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (j : Fin (P.p + P.q - S.rowSlots.card)) :
    S.leibnizPerm τ σ
        (S.colSlotsᶜ.orderEmbOfFin (by
          rw [Finset.card_compl, Fintype.card_fin]
          simp [S.card_eq]) j) =
      S.rowSlotsᶜ.orderEmbOfFin (by
        rw [Finset.card_compl, Fintype.card_fin]) (σ j) := by
  classical
  have hright :
      S.colSplit.symm
          (S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp [S.card_eq]) j) =
        Sum.inr j := by
    simpa [HodgeColSplit.colSplit] using S.colSplit.left_inv (Sum.inr j)
  simp [HodgeColSplit.leibnizPerm, hright, HodgeColSplit.rowSplit]

lemma HodgeColSplit.leibnizPerm_product_split {m n : ℕ}
    {Rng : Type*} [CommMonoid Rng] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (M : Matrix (Fin (P.p + P.q)) (Fin (P.p + P.q)) Rng) :
    (∏ j : Fin (P.p + P.q), M (S.leibnizPerm τ σ j) j) =
      (∏ j : Fin S.rowSlots.card,
        M (S.rowSlots.orderEmbOfFin rfl (τ j))
          (S.colSlots.orderEmbOfFin S.card_eq.symm j)) *
      (∏ j : Fin (P.p + P.q - S.rowSlots.card),
        M (S.rowSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]) (σ j))
          (S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp [S.card_eq]) j)) := by
  classical
  rw [← Equiv.prod_comp
    S.colSplit
    (fun j : Fin (P.p + P.q) => M (S.leibnizPerm τ σ j) j)]
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j _hj
    have hcol :
        S.colSplit (Sum.inl j) =
          S.colSlots.orderEmbOfFin S.card_eq.symm j := by
      simp [HodgeColSplit.colSplit, HodgeColSplit.colSlots]
    rw [hcol, HodgeColSplit.leibnizPerm_colSlots]
  · apply Finset.prod_congr rfl
    intro j _hj
    have hcol :
        S.colSplit (Sum.inr j) =
          S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp [S.card_eq]) j := by
      simp [HodgeColSplit.colSplit, HodgeColSplit.colSlots]
    rw [hcol, HodgeColSplit.leibnizPerm_colSlots_compl]

lemma HodgeColSplit.det_mul_det_eq_sum_leibnizPerm_terms {m n : ℕ}
    {Rng : Type*} [CommRing Rng] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (M : Matrix (Fin (P.p + P.q)) (Fin (P.p + P.q)) Rng) :
    Matrix.det
        (Matrix.submatrix M
          (S.rowSlots.orderEmbOfFin rfl)
          (S.colSlots.orderEmbOfFin S.card_eq.symm)) *
      Matrix.det
        (Matrix.submatrix M
          (S.rowSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]))
          (S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp [S.card_eq]))) =
      ∑ p : Equiv.Perm (Fin S.rowSlots.card) ×
          Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        ((Equiv.Perm.sign p.1 : Rng) *
            (Equiv.Perm.sign p.2 : Rng)) *
          ∏ j : Fin (P.p + P.q), M (S.leibnizPerm p.1 p.2 j) j := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply']
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [Matrix.submatrix_apply]
  rw [← Fintype.sum_prod_type' (γ := Rng)
    (f := fun τ σ =>
      ((Equiv.Perm.sign τ : Rng) *
          ∏ j : Fin S.rowSlots.card,
            M (S.rowSlots.orderEmbOfFin rfl (τ j))
              (S.colSlots.orderEmbOfFin S.card_eq.symm j)) *
        ((Equiv.Perm.sign σ : Rng) *
          ∏ j : Fin (P.p + P.q - S.rowSlots.card),
            M (S.rowSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin]) (σ j))
              (S.colSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin]
                simp [S.card_eq]) j)))]
  refine Finset.sum_congr rfl ?_
  rintro ⟨τ, σ⟩ _hp
  have hprod := S.leibnizPerm_product_split τ σ M
  rw [hprod]
  ring

lemma HodgeColSplit.toBiReshuffle_toPair_laplacePolynomial_eq_sum_leibnizPerm_terms
    {m n : ℕ} (k : Type*) [CommRing k] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair =
      ∑ p : Equiv.Perm (Fin S.rowSlots.card) ×
          Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        MvPolynomial.C
            (RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign p.1 :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign p.2 :
              MvPolynomial (Fin m × Fin n) k)) *
            ∏ j : Fin (P.p + P.q),
              slotMatrix k P (S.leibnizPerm p.1 p.2 j) j) := by
  classical
  rw [HodgeColSplit.toBiReshuffle_toPair_laplacePolynomial k S]
  rw [HodgeColSplit.det_mul_det_eq_sum_leibnizPerm_terms
    (S := S) (M := slotMatrix k P)]
  rw [Finset.mul_sum]

/-- One Leibniz term occurring after expanding both determinant blocks attached
to a column-side Hodge split. -/
abbrev HodgeColSplit.LeibnizTerm {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :=
  Σ S : HodgeColSplit P ν hνp,
    Equiv.Perm (Fin S.rowSlots.card) ×
      Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))

namespace HodgeColSplit.LeibnizTerm

noncomputable def ambientPerm {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (X : HodgeColSplit.LeibnizTerm P ν hνp) :
    Equiv.Perm (Fin (P.p + P.q)) :=
  X.1.leibnizPerm X.2.1 X.2.2

@[simp] lemma ambientPerm_apply {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (X : HodgeColSplit.LeibnizTerm P ν hνp) (j : Fin (P.p + P.q)) :
    X.ambientPerm j = X.1.leibnizPerm X.2.1 X.2.2 j := rfl

end HodgeColSplit.LeibnizTerm

lemma HodgeColSplit.sum_laplacePolynomial_eq_sum_leibnizTerm
    {m n : ℕ} (k : Type*) [Field k] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (coeff : HodgeColSplit P ν hνp → k) :
    (∑ S : HodgeColSplit P ν hνp,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) =
      ∑ X : HodgeColSplit.LeibnizTerm P ν hνp,
        MvPolynomial.C (coeff X.1) *
          (MvPolynomial.C
              (RawMinorPair.laplaceCoeff k X.1.toBiReshuffle.toPair) *
            (((Equiv.Perm.sign X.2.1 :
                MvPolynomial (Fin m × Fin n) k) *
              (Equiv.Perm.sign X.2.2 :
                MvPolynomial (Fin m × Fin n) k)) *
              ∏ j : Fin (P.p + P.q),
                slotMatrix k P (X.ambientPerm j) j)) := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [HodgeColSplit.toBiReshuffle_toPair_laplacePolynomial_eq_sum_leibnizPerm_terms
    k S]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨τ, σ⟩ _hτσ
  simp [HodgeColSplit.LeibnizTerm.ambientPerm]

lemma HodgeColSplit.leibnizPerm_pair_injective {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    Function.Injective
      (fun p : Equiv.Perm (Fin S.rowSlots.card) ×
          Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)) =>
        S.leibnizPerm p.1 p.2) := by
  classical
  intro a b hab
  cases a with
  | mk τa σa =>
      cases b with
      | mk τb σb =>
          change S.leibnizPerm τa σa = S.leibnizPerm τb σb at hab
          congr
          · ext j
            have h :=
              congrArg
                (fun e : Equiv.Perm (Fin (P.p + P.q)) =>
                  e (S.colSlots.orderEmbOfFin S.card_eq.symm j)) hab
            exact congrArg Fin.val
              ((S.rowSlots.orderEmbOfFin rfl).injective (by
                simpa using h))
          · ext j
            have h :=
              congrArg
                (fun e : Equiv.Perm (Fin (P.p + P.q)) =>
                  e
                    (S.colSlotsᶜ.orderEmbOfFin (by
                      rw [Finset.card_compl, Fintype.card_fin]
                      simp [S.card_eq]) j)) hab
            exact congrArg Fin.val
              ((S.rowSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin])).injective (by
                  simpa using h))

lemma HodgeColSplit.rowSlots_eq_colSlots_image_of_leibnizPerm_eq
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (hπ : S.leibnizPerm τ σ = π) :
    S.rowSlots = S.colSlots.map π.toEmbedding := by
  classical
  subst π
  ext x
  constructor
  · intro hx
    let xr : {x // x ∈ S.rowSlots} := ⟨x, hx⟩
    let j : Fin S.rowSlots.card := (S.rowSlots.orderIsoOfFin rfl).symm xr
    have hxj : S.rowSlots.orderEmbOfFin rfl j = x := by
      exact congrArg Subtype.val
        ((S.rowSlots.orderIsoOfFin rfl).apply_symm_apply xr)
    refine Finset.mem_map.mpr ?_
    refine ⟨S.colSlots.orderEmbOfFin S.card_eq.symm (τ.symm j), ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem S.colSlots S.card_eq.symm (τ.symm j)
    · change S.leibnizPerm τ σ
          (S.colSlots.orderEmbOfFin S.card_eq.symm (τ.symm j)) = x
      rw [HodgeColSplit.leibnizPerm_colSlots]
      simp [hxj]
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, hyx⟩
    let yc : {y // y ∈ S.colSlots} := ⟨y, hy⟩
    let j : Fin S.rowSlots.card := (S.colSlots.orderIsoOfFin S.card_eq.symm).symm yc
    have hyj : S.colSlots.orderEmbOfFin S.card_eq.symm j = y := by
      exact congrArg Subtype.val
        ((S.colSlots.orderIsoOfFin S.card_eq.symm).apply_symm_apply yc)
    have hrow :
        S.leibnizPerm τ σ y ∈ S.rowSlots := by
      rw [← hyj, HodgeColSplit.leibnizPerm_colSlots]
      exact Finset.orderEmbOfFin_mem S.rowSlots rfl (τ j)
    have hyx' : S.leibnizPerm τ σ y = x := by
      simpa using hyx
    simpa [hyx'] using hrow

lemma HodgeColSplit.eq_of_W_eq_of_leibnizPerm_eq
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    {S S' : HodgeColSplit P ν hνp}
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (τ' : Equiv.Perm (Fin S'.rowSlots.card))
    (σ' : Equiv.Perm (Fin (P.p + P.q - S'.rowSlots.card)))
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (hπ : S.leibnizPerm τ σ = π)
    (hπ' : S'.leibnizPerm τ' σ' = π)
    (hW : S.W = S'.W) :
    S = S' := by
  have hcol : S.colSlots = S'.colSlots := by
    simp [HodgeColSplit.colSlots, hW]
  have hrow : S.rowSlots = S'.rowSlots := by
    rw [S.rowSlots_eq_colSlots_image_of_leibnizPerm_eq τ σ π hπ,
      S'.rowSlots_eq_colSlots_image_of_leibnizPerm_eq τ' σ' π hπ',
      hcol]
  cases S with
  | mk rowSlots W leftRows W_subset card_eq =>
      cases S' with
      | mk rowSlots' W' leftRows' W_subset' card_eq' =>
          simp only at hrow hW
          subst rowSlots'
          subst W'
          rfl

lemma HodgeColSplit.leibnizPerm_mem_rowSlots_compl_of_mem_colSlots_compl
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    {x : Fin (P.p + P.q)} (hx : x ∈ S.colSlotsᶜ) :
    S.leibnizPerm τ σ x ∈ S.rowSlotsᶜ := by
  classical
  let hcol :
      S.colSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    simp [S.card_eq]
  let x' : { x // x ∈ S.colSlotsᶜ } := ⟨x, hx⟩
  let j : Fin (P.p + P.q - S.rowSlots.card) :=
    ((S.colSlotsᶜ).orderIsoOfFin hcol).symm x'
  have hxj :
      (S.colSlotsᶜ.orderEmbOfFin hcol j) = x := by
    exact congrArg Subtype.val
      (((S.colSlotsᶜ).orderIsoOfFin hcol).apply_symm_apply x')
  rw [← hxj]
  rw [HodgeColSplit.leibnizPerm_colSlots_compl]
  exact Finset.orderEmbOfFin_mem S.rowSlotsᶜ
    (by rw [Finset.card_compl, Fintype.card_fin]) (σ j)

lemma HodgeColSplit.W_subset_colSlots_compl
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp) :
    S.W ⊆ S.colSlotsᶜ := by
  intro x hxW
  rw [Finset.mem_compl]
  intro hxcol
  exact (Finset.mem_sdiff.mp hxcol).2 hxW

lemma HodgeColSplit.permPreimageLeftSlotFinset_subset_hodgeD
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    permPreimageLeftSlotFinset P (S.leibnizPerm τ σ) ⊆
      Hodge.hodgeD P ν := by
  intro x hxpre
  have hleft :
      S.leibnizPerm τ σ x ∈ leftSlotFinset P :=
    (mem_permPreimageLeftSlotFinset_iff P (S.leibnizPerm τ σ) x).mp hxpre
  by_cases hxcol : x ∈ S.colSlots
  · exact (Finset.mem_sdiff.mp hxcol).1
  · have hxcomp : x ∈ S.colSlotsᶜ := by
      simpa [Finset.mem_compl] using hxcol
    have hrowcomp :
        S.leibnizPerm τ σ x ∈ S.rowSlotsᶜ :=
      S.leibnizPerm_mem_rowSlots_compl_of_mem_colSlots_compl τ σ hxcomp
    exact False.elim ((Finset.mem_compl.mp hrowcomp) (S.leftRows hleft))

lemma HodgeColSplit.W_mem_powerset_hodgeC_sdiff_permPreimage
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    S.W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P (S.leibnizPerm τ σ)).powerset := by
  classical
  refine Finset.mem_powerset.mpr ?_
  intro x hxW
  refine Finset.mem_sdiff.mpr ⟨S.W_subset hxW, ?_⟩
  intro hxpre
  have hxcomp : x ∈ S.colSlotsᶜ := S.W_subset_colSlots_compl hxW
  have hrowcomp :
      S.leibnizPerm τ σ x ∈ S.rowSlotsᶜ :=
    S.leibnizPerm_mem_rowSlots_compl_of_mem_colSlots_compl τ σ hxcomp
  have hleft :
      S.leibnizPerm τ σ x ∈ leftSlotFinset P :=
    (mem_permPreimageLeftSlotFinset_iff P (S.leibnizPerm τ σ) x).mp hxpre
  exact (Finset.mem_compl.mp hrowcomp) (S.leftRows hleft)

noncomputable def HodgeColSplit.ofWPerm
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (W : Finset (Fin (P.p + P.q)))
    (hpreD : permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν)
    (hW : W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P π).powerset) :
    HodgeColSplit P ν hνp where
  rowSlots := (Hodge.hodgeD P ν \ W).map π.toEmbedding
  W := W
  leftRows := by
    intro x hxleft
    have hxpre :
        π.symm x ∈ permPreimageLeftSlotFinset P π := by
      rw [mem_permPreimageLeftSlotFinset_iff]
      simpa using hxleft
    have hxD : π.symm x ∈ Hodge.hodgeD P ν := hpreD hxpre
    have hxnotW : π.symm x ∉ W := by
      intro hxW
      have hxsdiff :
          π.symm x ∈ Hodge.hodgeC P ν hνp \
            permPreimageLeftSlotFinset P π :=
        (Finset.mem_powerset.mp hW) hxW
      exact (Finset.mem_sdiff.mp hxsdiff).2 hxpre
    refine Finset.mem_map.mpr ?_
    exact ⟨π.symm x, Finset.mem_sdiff.mpr ⟨hxD, hxnotW⟩, by simp⟩
  W_subset := by
    intro x hxW
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hW) hxW)).1
  card_eq := by
    simp

@[simp] lemma HodgeColSplit.ofWPerm_W
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (W : Finset (Fin (P.p + P.q)))
    (hpreD : permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν)
    (hW : W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P π).powerset) :
    (HodgeColSplit.ofWPerm P ν hνp π W hpreD hW).W = W := rfl

@[simp] lemma HodgeColSplit.ofWPerm_colSlots
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (W : Finset (Fin (P.p + P.q)))
    (hpreD : permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν)
    (hW : W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P π).powerset) :
    (HodgeColSplit.ofWPerm P ν hνp π W hpreD hW).colSlots =
      Hodge.hodgeD P ν \ W := rfl

lemma HodgeColSplit.exists_leibnizPerm_eq_of_rowSlots_eq_colSlots_image
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeColSplit P ν hνp)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (hrow : S.rowSlots = S.colSlots.map π.toEmbedding) :
    ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
    ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
      S.leibnizPerm τ σ = π := by
  classical
  let τFun : Fin S.rowSlots.card → Fin S.rowSlots.card := fun j =>
    (S.rowSlots.orderIsoOfFin rfl).symm
      ⟨π (S.colSlots.orderEmbOfFin S.card_eq.symm j), by
        have hj : S.colSlots.orderEmbOfFin S.card_eq.symm j ∈ S.colSlots :=
          Finset.orderEmbOfFin_mem S.colSlots S.card_eq.symm j
        have hmem :
            π (S.colSlots.orderEmbOfFin S.card_eq.symm j) ∈
              S.colSlots.map π.toEmbedding :=
          Finset.mem_map.mpr
            ⟨S.colSlots.orderEmbOfFin S.card_eq.symm j, hj, rfl⟩
        simpa only [hrow] using hmem⟩
  have hτFun :
      ∀ j : Fin S.rowSlots.card,
        S.rowSlots.orderEmbOfFin rfl (τFun j) =
          π (S.colSlots.orderEmbOfFin S.card_eq.symm j) := by
    intro j
    exact congrArg Subtype.val
      ((S.rowSlots.orderIsoOfFin rfl).apply_symm_apply
        ⟨π (S.colSlots.orderEmbOfFin S.card_eq.symm j), by
          have hj : S.colSlots.orderEmbOfFin S.card_eq.symm j ∈ S.colSlots :=
            Finset.orderEmbOfFin_mem S.colSlots S.card_eq.symm j
          have hmem :
              π (S.colSlots.orderEmbOfFin S.card_eq.symm j) ∈
                S.colSlots.map π.toEmbedding :=
            Finset.mem_map.mpr
              ⟨S.colSlots.orderEmbOfFin S.card_eq.symm j, hj, rfl⟩
          simpa only [hrow] using hmem⟩)
  have hτInj : Function.Injective τFun := by
    intro a b hab
    have h := congrArg (fun j => S.rowSlots.orderEmbOfFin rfl j) hab
    simp only at h
    rw [hτFun a, hτFun b] at h
    exact (S.colSlots.orderEmbOfFin S.card_eq.symm).injective (π.injective h)
  have hτBij : Function.Bijective τFun :=
    (Fintype.bijective_iff_injective_and_card τFun).mpr ⟨hτInj, rfl⟩
  let τ : Equiv.Perm (Fin S.rowSlots.card) := Equiv.ofBijective τFun hτBij
  have hτ :
      ∀ j : Fin S.rowSlots.card,
        S.rowSlots.orderEmbOfFin rfl (τ j) =
          π (S.colSlots.orderEmbOfFin S.card_eq.symm j) := by
    intro j
    exact hτFun j
  let hrowCompl :
      S.rowSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  let hcolCompl :
      S.colSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    simp [S.card_eq]
  let σFun :
      Fin (P.p + P.q - S.rowSlots.card) →
        Fin (P.p + P.q - S.rowSlots.card) := fun j =>
    (S.rowSlotsᶜ.orderIsoOfFin hrowCompl).symm
      ⟨π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j), by
        have hjc :
            S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ S.colSlotsᶜ :=
          Finset.orderEmbOfFin_mem S.colSlotsᶜ hcolCompl j
        rw [Finset.mem_compl] at hjc
        rw [Finset.mem_compl]
        intro hrowmem
        have hrowmem' :
            π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) ∈
              S.colSlots.map π.toEmbedding := hrow ▸ hrowmem
        rcases Finset.mem_map.mp hrowmem' with ⟨y, hy, hyπ⟩
        have hxy :
            S.colSlotsᶜ.orderEmbOfFin hcolCompl j = y :=
          π.injective hyπ.symm
        exact hjc (by rw [hxy]; exact hy)⟩
  have hσFun :
      ∀ j : Fin (P.p + P.q - S.rowSlots.card),
        S.rowSlotsᶜ.orderEmbOfFin hrowCompl (σFun j) =
          π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) := by
    intro j
    exact congrArg Subtype.val
      ((S.rowSlotsᶜ.orderIsoOfFin hrowCompl).apply_symm_apply
        ⟨π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j), by
          have hjc :
              S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ S.colSlotsᶜ :=
            Finset.orderEmbOfFin_mem S.colSlotsᶜ hcolCompl j
          rw [Finset.mem_compl] at hjc
          rw [Finset.mem_compl]
          intro hrowmem
          have hrowmem' :
              π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) ∈
                S.colSlots.map π.toEmbedding := hrow ▸ hrowmem
          rcases Finset.mem_map.mp hrowmem' with ⟨y, hy, hyπ⟩
          have hxy :
              S.colSlotsᶜ.orderEmbOfFin hcolCompl j = y :=
            π.injective hyπ.symm
          exact hjc (by rw [hxy]; exact hy)⟩)
  have hσInj : Function.Injective σFun := by
    intro a b hab
    have h := congrArg (fun j => S.rowSlotsᶜ.orderEmbOfFin hrowCompl j) hab
    simp only at h
    rw [hσFun a, hσFun b] at h
    exact (S.colSlotsᶜ.orderEmbOfFin hcolCompl).injective (π.injective h)
  have hσBij : Function.Bijective σFun :=
    (Fintype.bijective_iff_injective_and_card σFun).mpr ⟨hσInj, rfl⟩
  let σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)) :=
    Equiv.ofBijective σFun hσBij
  have hσ :
      ∀ j : Fin (P.p + P.q - S.rowSlots.card),
        S.rowSlotsᶜ.orderEmbOfFin hrowCompl (σ j) =
          π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) := by
    intro j
    exact hσFun j
  refine ⟨τ, σ, ?_⟩
  ext x
  by_cases hx : x ∈ S.colSlots
  · let x' : { x // x ∈ S.colSlots } := ⟨x, hx⟩
    let j : Fin S.rowSlots.card := (S.colSlots.orderIsoOfFin S.card_eq.symm).symm x'
    have hxj : S.colSlots.orderEmbOfFin S.card_eq.symm j = x := by
      exact congrArg Subtype.val
        ((S.colSlots.orderIsoOfFin S.card_eq.symm).apply_symm_apply x')
    rw [← hxj]
    rw [HodgeColSplit.leibnizPerm_colSlots]
    simpa using congrArg Fin.val (hτ j)
  · have hxc : x ∈ S.colSlotsᶜ := by
      simpa [Finset.mem_compl] using hx
    let x' : { x // x ∈ S.colSlotsᶜ } := ⟨x, hxc⟩
    let j : Fin (P.p + P.q - S.rowSlots.card) :=
      (S.colSlotsᶜ.orderIsoOfFin hcolCompl).symm x'
    have hxj : S.colSlotsᶜ.orderEmbOfFin hcolCompl j = x := by
      exact congrArg Subtype.val
        ((S.colSlotsᶜ.orderIsoOfFin hcolCompl).apply_symm_apply x')
    rw [← hxj]
    rw [HodgeColSplit.leibnizPerm_colSlots_compl]
    simpa using congrArg Fin.val (hσ j)

lemma HodgeColSplit.exists_leibnizPerm_eq_of_W_mem_powerset
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (W : Finset (Fin (P.p + P.q)))
    (hpreD : permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν)
    (hW : W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P π).powerset) :
    ∃ S : HodgeColSplit P ν hνp,
    ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
    ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
      S.W = W ∧ S.leibnizPerm τ σ = π := by
  classical
  let S : HodgeColSplit P ν hνp :=
    HodgeColSplit.ofWPerm P ν hνp π W hpreD hW
  have hrow : S.rowSlots = S.colSlots.map π.toEmbedding := by
    rfl
  rcases S.exists_leibnizPerm_eq_of_rowSlots_eq_colSlots_image π hrow with
    ⟨τ, σ, hπ⟩
  exact ⟨S, τ, σ, rfl, hπ⟩

namespace HodgeColSplit.LeibnizTerm

abbrev AmbientW {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :=
  { pw : Equiv.Perm (Fin (P.p + P.q)) × Finset (Fin (P.p + P.q)) //
    permPreimageLeftSlotFinset P pw.1 ⊆ Hodge.hodgeD P ν ∧
      pw.2 ∈ (Hodge.hodgeC P ν hνp \
        permPreimageLeftSlotFinset P pw.1).powerset }

noncomputable def toAmbientWFlat {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (X : HodgeColSplit.LeibnizTerm P ν hνp) :
    AmbientW P ν hνp :=
  ⟨(X.ambientPerm, X.1.W),
    X.1.permPreimageLeftSlotFinset_subset_hodgeD X.2.1 X.2.2,
    X.1.W_mem_powerset_hodgeC_sdiff_permPreimage X.2.1 X.2.2⟩

lemma toAmbientWFlat_injective {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Function.Injective
      (@HodgeColSplit.LeibnizTerm.toAmbientWFlat m n P ν hνp) := by
  classical
  intro X Y h
  cases X with
  | mk S p =>
      cases p with
      | mk τ σ =>
          cases Y with
          | mk S' p' =>
              cases p' with
              | mk τ' σ' =>
                  have hπ :
                      S.leibnizPerm τ σ = S'.leibnizPerm τ' σ' :=
                    congrArg (fun z : AmbientW P ν hνp => z.1.1) h
                  have hW : S.W = S'.W :=
                    congrArg (fun z : AmbientW P ν hνp => z.1.2) h
                  have hS : S = S' :=
                    HodgeColSplit.eq_of_W_eq_of_leibnizPerm_eq
                      (S := S) (S' := S') τ σ τ' σ'
                      (S.leibnizPerm τ σ) rfl hπ.symm hW
                  cases hS
                  have hp : (τ, σ) = (τ', σ') :=
                    S.leibnizPerm_pair_injective hπ
                  cases hp
                  rfl

lemma toAmbientWFlat_surjective {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    Function.Surjective
      (@HodgeColSplit.LeibnizTerm.toAmbientWFlat m n P ν hνp) := by
  classical
  intro Y
  rcases Y with ⟨⟨π, W⟩, hpreD, hW⟩
  rcases HodgeColSplit.exists_leibnizPerm_eq_of_W_mem_powerset
      P ν hνp π W hpreD hW with ⟨S, τ, σ, hSW, hπ⟩
  refine ⟨⟨S, (τ, σ)⟩, ?_⟩
  apply Subtype.ext
  simp [HodgeColSplit.LeibnizTerm.toAmbientWFlat,
    HodgeColSplit.LeibnizTerm.ambientPerm, hπ, hSW]

noncomputable def equivAmbientWFlat {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    HodgeColSplit.LeibnizTerm P ν hνp ≃ AmbientW P ν hνp :=
  Equiv.ofBijective
    (@HodgeColSplit.LeibnizTerm.toAmbientWFlat m n P ν hνp)
    ⟨toAmbientWFlat_injective, toAmbientWFlat_surjective P ν hνp⟩

noncomputable def ambientWEquivSigma {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    AmbientW P ν hνp ≃
      Σ π : Equiv.Perm (Fin (P.p + P.q)),
        { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π).powerset } where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv := by
    intro z
    rfl
  right_inv := by
    intro z
    rfl

noncomputable def equivAmbientW {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    HodgeColSplit.LeibnizTerm P ν hνp ≃
      Σ π : Equiv.Perm (Fin (P.p + P.q)),
        { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π).powerset } :=
  (equivAmbientWFlat P ν hνp).trans (ambientWEquivSigma P ν hνp)

lemma sum_eq_sum_ambientW {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    {M : Type*} [AddCommMonoid M]
    (f : HodgeColSplit.LeibnizTerm P ν hνp → M)
    (g :
      (π : Equiv.Perm (Fin (P.p + P.q))) →
        { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π).powerset } → M)
    (h :
      ∀ X : HodgeColSplit.LeibnizTerm P ν hνp,
        f X =
          g X.ambientPerm
            ⟨X.1.W,
              X.1.permPreimageLeftSlotFinset_subset_hodgeD X.2.1 X.2.2,
              X.1.W_mem_powerset_hodgeC_sdiff_permPreimage X.2.1 X.2.2⟩) :
    (∑ X : HodgeColSplit.LeibnizTerm P ν hνp, f X) =
      ∑ π : Equiv.Perm (Fin (P.p + P.q)),
        ∑ W : { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π).powerset },
          g π W := by
  classical
  calc
    (∑ X : HodgeColSplit.LeibnizTerm P ν hνp, f X)
        =
      ∑ Y :
          (Σ π : Equiv.Perm (Fin (P.p + P.q)),
            { W : Finset (Fin (P.p + P.q)) //
              permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν ∧
                W ∈ (Hodge.hodgeC P ν hνp \
                  permPreimageLeftSlotFinset P π).powerset }),
        g Y.1 Y.2 := by
          refine Fintype.sum_equiv
            (HodgeColSplit.LeibnizTerm.equivAmbientW P ν hνp)
            f (fun Y => g Y.1 Y.2) ?_
          intro X
          simpa [HodgeColSplit.LeibnizTerm.equivAmbientW,
            HodgeColSplit.LeibnizTerm.equivAmbientWFlat,
            HodgeColSplit.LeibnizTerm.ambientWEquivSigma,
            HodgeColSplit.LeibnizTerm.toAmbientWFlat] using h X
    _ =
      ∑ π : Equiv.Perm (Fin (P.p + P.q)),
        ∑ W : { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π).powerset },
          g π W := by
          rw [Fintype.sum_sigma]

end HodgeColSplit.LeibnizTerm

lemma HodgeRowSplit.toBiReshuffle_toPair_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    RawMinorPair.toPolynomial k S.toBiReshuffle.toPair =
      Matrix.det
          (Matrix.submatrix (slotMatrix k P)
            (S.rowSlots.orderEmbOfFin rfl)
            (S.colSlots.orderEmbOfFin S.card_eq.symm)) *
        Matrix.det
          (Matrix.submatrix (slotMatrix k P)
            (S.rowSlotsᶜ.orderEmbOfFin (by
              rw [Finset.card_compl, Fintype.card_fin]))
            (S.colSlotsᶜ.orderEmbOfFin (by
              simp))) := by
  rw [RawMinorPair.toPolynomial]
  change
    RawMinorIndex.toPolynomial k
        (ofFinsets P S.rowSlots S.colSlots S.card_eq).toPair.left *
      RawMinorIndex.toPolynomial k
        (ofFinsets P S.rowSlots S.colSlots S.card_eq).toPair.right =
      _
  rw [ofFinsets_toPair_left_toPolynomial k P S.rowSlots S.colSlots S.card_eq]
  exact congrArg
    (fun x =>
      Matrix.det
          (Matrix.submatrix (slotMatrix k P)
            (S.rowSlots.orderEmbOfFin rfl)
            (S.colSlots.orderEmbOfFin S.card_eq.symm)) * x)
    (ofFinsets_toPair_right_toPolynomial
      k P S.rowSlots S.colSlots S.card_eq)

lemma HodgeRowSplit.toBiReshuffle_toPair_laplacePolynomial {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair =
      MvPolynomial.C
          (RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair) *
        (Matrix.det
            (Matrix.submatrix (slotMatrix k P)
              (S.rowSlots.orderEmbOfFin rfl)
              (S.colSlots.orderEmbOfFin S.card_eq.symm)) *
          Matrix.det
            (Matrix.submatrix (slotMatrix k P)
            (S.rowSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin]))
              (S.colSlotsᶜ.orderEmbOfFin (by
                simp)))) := by
  rw [RawMinorPair.laplacePolynomial,
    HodgeRowSplit.toBiReshuffle_toPair_toPolynomial k S]

lemma HodgeRowSplit.sign_leibnizPerm {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    Equiv.Perm.sign (S.leibnizPerm τ σ) =
      Equiv.Perm.sign S.rowSplitRel *
        (Equiv.Perm.sign τ * Equiv.Perm.sign σ) *
          Equiv.Perm.sign S.colSplitRel := by
  classical
  let A := S.stdSplit
  let rrel : Equiv.Perm
      (Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card)) :=
    S.rowSplitRel
  let crel : Equiv.Perm
      (Fin S.rowSlots.card ⊕ Fin (P.p + P.q - S.rowSlots.card)) :=
    S.colSplitRel
  have hconj :
      (A.trans (S.leibnizPerm τ σ)).trans A.symm =
        crel.symm.trans ((Equiv.Perm.sumCongr τ σ).trans rrel) := by
    ext x
    simp [A, rrel, crel, HodgeRowSplit.leibnizPerm,
      HodgeRowSplit.rowSplitRel, HodgeRowSplit.colSplitRel]
  have hsign :
      Equiv.Perm.sign (S.leibnizPerm τ σ) =
        Equiv.Perm.sign
          (crel.symm.trans ((Equiv.Perm.sumCongr τ σ).trans rrel)) := by
    rw [← hconj]
    exact (Equiv.Perm.sign_trans_trans_symm (S.leibnizPerm τ σ) A).symm
  rw [hsign]
  simp [rrel, crel, Equiv.Perm.sign_trans, Equiv.Perm.sign_sumCongr,
    mul_assoc, mul_comm, mul_left_comm]

lemma HodgeRowSplit.splitSignFactor_mul_blockSigns {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    {R : Type*} [CommRing R]
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    S.splitSignFactor (R := R) *
        (equivPermSign (R := R) τ * equivPermSign (R := R) σ) =
      equivPermSign (R := R) (S.leibnizPerm τ σ) := by
  unfold HodgeRowSplit.splitSignFactor equivPermSign
  rw [S.sign_leibnizPerm τ σ]
  simp only [Units.val_mul, Int.cast_mul]
  ring

@[simp] lemma HodgeRowSplit.leibnizPerm_colSlots {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (j : Fin S.rowSlots.card) :
    S.leibnizPerm τ σ (S.colSlots.orderEmbOfFin S.card_eq.symm j) =
      S.rowSlots.orderEmbOfFin rfl (τ j) := by
  classical
  have hleft :
      S.colSplit.symm
          (S.colSlots.orderEmbOfFin S.card_eq.symm j) =
        Sum.inl j := by
    simpa [HodgeRowSplit.colSplit] using S.colSplit.left_inv (Sum.inl j)
  simp [HodgeRowSplit.leibnizPerm, hleft, HodgeRowSplit.rowSplit]

@[simp] lemma HodgeRowSplit.leibnizPerm_colSlots_compl {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (j : Fin (P.p + P.q - S.rowSlots.card)) :
    S.leibnizPerm τ σ
        (S.colSlotsᶜ.orderEmbOfFin (by
          rw [Finset.card_compl, Fintype.card_fin]
          simp) j) =
      S.rowSlotsᶜ.orderEmbOfFin (by
        rw [Finset.card_compl, Fintype.card_fin]) (σ j) := by
  classical
  have hright :
      S.colSplit.symm
          (S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp) j) =
        Sum.inr j := by
    simpa [HodgeRowSplit.colSplit] using S.colSplit.left_inv (Sum.inr j)
  simp [HodgeRowSplit.leibnizPerm, hright, HodgeRowSplit.rowSplit]

lemma HodgeRowSplit.leibnizPerm_product_split {m n : ℕ}
    {Rng : Type*} [CommMonoid Rng] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (M : Matrix (Fin (P.p + P.q)) (Fin (P.p + P.q)) Rng) :
    (∏ j : Fin (P.p + P.q), M (S.leibnizPerm τ σ j) j) =
      (∏ j : Fin S.rowSlots.card,
        M (S.rowSlots.orderEmbOfFin rfl (τ j))
          (S.colSlots.orderEmbOfFin S.card_eq.symm j)) *
      (∏ j : Fin (P.p + P.q - S.rowSlots.card),
        M (S.rowSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]) (σ j))
          (S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp) j)) := by
  classical
  rw [← Equiv.prod_comp
    S.colSplit
    (fun j : Fin (P.p + P.q) => M (S.leibnizPerm τ σ j) j)]
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j _hj
    have hcol :
        S.colSplit (Sum.inl j) =
          S.colSlots.orderEmbOfFin S.card_eq.symm j := by
      simp [HodgeRowSplit.colSplit]
    rw [hcol, HodgeRowSplit.leibnizPerm_colSlots]
  · apply Finset.prod_congr rfl
    intro j _hj
    have hcol :
        S.colSplit (Sum.inr j) =
          S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp) j := by
      simp [HodgeRowSplit.colSplit]
    rw [hcol, HodgeRowSplit.leibnizPerm_colSlots_compl]

lemma HodgeRowSplit.det_mul_det_eq_sum_leibnizPerm_terms {m n : ℕ}
    {Rng : Type*} [CommRing Rng] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (M : Matrix (Fin (P.p + P.q)) (Fin (P.p + P.q)) Rng) :
    Matrix.det
        (Matrix.submatrix M
          (S.rowSlots.orderEmbOfFin rfl)
          (S.colSlots.orderEmbOfFin S.card_eq.symm)) *
      Matrix.det
        (Matrix.submatrix M
          (S.rowSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]))
          (S.colSlotsᶜ.orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]
            simp))) =
      ∑ p : Equiv.Perm (Fin S.rowSlots.card) ×
          Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        ((Equiv.Perm.sign p.1 : Rng) *
            (Equiv.Perm.sign p.2 : Rng)) *
          ∏ j : Fin (P.p + P.q), M (S.leibnizPerm p.1 p.2 j) j := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply']
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [Matrix.submatrix_apply]
  rw [← Fintype.sum_prod_type' (γ := Rng)
    (f := fun τ σ =>
      ((Equiv.Perm.sign τ : Rng) *
          ∏ j : Fin S.rowSlots.card,
            M (S.rowSlots.orderEmbOfFin rfl (τ j))
              (S.colSlots.orderEmbOfFin S.card_eq.symm j)) *
        ((Equiv.Perm.sign σ : Rng) *
          ∏ j : Fin (P.p + P.q - S.rowSlots.card),
            M (S.rowSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin]) (σ j))
              (S.colSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin]
                simp) j)))]
  refine Finset.sum_congr rfl ?_
  rintro ⟨τ, σ⟩ _hp
  have hprod := S.leibnizPerm_product_split τ σ M
  rw [hprod]
  ring

lemma HodgeRowSplit.toBiReshuffle_toPair_laplacePolynomial_eq_sum_leibnizPerm_terms
    {m n : ℕ} (k : Type*) [CommRing k] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair =
      ∑ p : Equiv.Perm (Fin S.rowSlots.card) ×
          Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
        MvPolynomial.C
            (RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign p.1 :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign p.2 :
              MvPolynomial (Fin m × Fin n) k)) *
            ∏ j : Fin (P.p + P.q),
              slotMatrix k P (S.leibnizPerm p.1 p.2 j) j) := by
  classical
  rw [HodgeRowSplit.toBiReshuffle_toPair_laplacePolynomial k S]
  rw [HodgeRowSplit.det_mul_det_eq_sum_leibnizPerm_terms
    (S := S) (M := slotMatrix k P)]
  rw [Finset.mul_sum]

/-- One Leibniz term occurring after expanding both determinant blocks attached
to a row-side Hodge split. -/
abbrev HodgeRowSplit.LeibnizTerm {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :=
  Σ S : HodgeRowSplit P ν hνp,
    Equiv.Perm (Fin S.rowSlots.card) ×
      Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))

namespace HodgeRowSplit.LeibnizTerm

noncomputable def ambientPerm {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (X : HodgeRowSplit.LeibnizTerm P ν hνp) :
    Equiv.Perm (Fin (P.p + P.q)) :=
  X.1.leibnizPerm X.2.1 X.2.2

@[simp] lemma ambientPerm_apply {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (X : HodgeRowSplit.LeibnizTerm P ν hνp) (j : Fin (P.p + P.q)) :
    X.ambientPerm j = X.1.leibnizPerm X.2.1 X.2.2 j := rfl

end HodgeRowSplit.LeibnizTerm

lemma HodgeRowSplit.sum_laplacePolynomial_eq_sum_leibnizTerm
    {m n : ℕ} (k : Type*) [Field k] {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (coeff : HodgeRowSplit P ν hνp → k) :
    (∑ S : HodgeRowSplit P ν hνp,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) =
      ∑ X : HodgeRowSplit.LeibnizTerm P ν hνp,
        MvPolynomial.C (coeff X.1) *
          (MvPolynomial.C
              (RawMinorPair.laplaceCoeff k X.1.toBiReshuffle.toPair) *
            (((Equiv.Perm.sign X.2.1 :
                MvPolynomial (Fin m × Fin n) k) *
              (Equiv.Perm.sign X.2.2 :
                MvPolynomial (Fin m × Fin n) k)) *
              ∏ j : Fin (P.p + P.q),
                slotMatrix k P (X.ambientPerm j) j)) := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [HodgeRowSplit.toBiReshuffle_toPair_laplacePolynomial_eq_sum_leibnizPerm_terms
    k S]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨τ, σ⟩ _hτσ
  simp [HodgeRowSplit.LeibnizTerm.ambientPerm]

lemma HodgeRowSplit.leibnizPerm_pair_injective {m n : ℕ}
    {P : RawMinorPair m n} {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    Function.Injective
      (fun p : Equiv.Perm (Fin S.rowSlots.card) ×
          Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)) =>
        S.leibnizPerm p.1 p.2) := by
  classical
  intro a b hab
  cases a with
  | mk τa σa =>
      cases b with
      | mk τb σb =>
          change S.leibnizPerm τa σa = S.leibnizPerm τb σb at hab
          congr
          · ext j
            have h :=
              congrArg
                (fun e : Equiv.Perm (Fin (P.p + P.q)) =>
                  e (S.colSlots.orderEmbOfFin S.card_eq.symm j)) hab
            exact congrArg Fin.val
              ((S.rowSlots.orderEmbOfFin rfl).injective (by
                simpa using h))
          · ext j
            have h :=
              congrArg
                (fun e : Equiv.Perm (Fin (P.p + P.q)) =>
                  e
                    (S.colSlotsᶜ.orderEmbOfFin (by
                      rw [Finset.card_compl, Fintype.card_fin]
                      simp) j)) hab
            exact congrArg Fin.val
              ((S.rowSlotsᶜ.orderEmbOfFin (by
                rw [Finset.card_compl, Fintype.card_fin])).injective (by
                  simpa using h))

lemma HodgeRowSplit.rowSlots_eq_colSlots_image_of_leibnizPerm_eq
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (hπ : S.leibnizPerm τ σ = π) :
    S.rowSlots = S.colSlots.map π.toEmbedding := by
  classical
  subst π
  ext x
  constructor
  · intro hx
    let xr : {x // x ∈ S.rowSlots} := ⟨x, hx⟩
    let j : Fin S.rowSlots.card := (S.rowSlots.orderIsoOfFin rfl).symm xr
    have hxj : S.rowSlots.orderEmbOfFin rfl j = x := by
      exact congrArg Subtype.val
        ((S.rowSlots.orderIsoOfFin rfl).apply_symm_apply xr)
    refine Finset.mem_map.mpr ?_
    refine ⟨S.colSlots.orderEmbOfFin S.card_eq.symm (τ.symm j), ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem S.colSlots S.card_eq.symm (τ.symm j)
    · change S.leibnizPerm τ σ
          (S.colSlots.orderEmbOfFin S.card_eq.symm (τ.symm j)) = x
      rw [HodgeRowSplit.leibnizPerm_colSlots]
      simp [hxj]
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, hyx⟩
    let yc : {y // y ∈ S.colSlots} := ⟨y, hy⟩
    let j : Fin S.rowSlots.card := (S.colSlots.orderIsoOfFin S.card_eq.symm).symm yc
    have hyj : S.colSlots.orderEmbOfFin S.card_eq.symm j = y := by
      exact congrArg Subtype.val
        ((S.colSlots.orderIsoOfFin S.card_eq.symm).apply_symm_apply yc)
    have hrow :
        S.leibnizPerm τ σ y ∈ S.rowSlots := by
      rw [← hyj, HodgeRowSplit.leibnizPerm_colSlots]
      exact Finset.orderEmbOfFin_mem S.rowSlots rfl (τ j)
    have hyx' : S.leibnizPerm τ σ y = x := by
      simpa using hyx
    simpa [hyx'] using hrow

lemma HodgeRowSplit.eq_of_W_eq_of_leibnizPerm_eq
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    {S S' : HodgeRowSplit P ν hνp}
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    (τ' : Equiv.Perm (Fin S'.rowSlots.card))
    (σ' : Equiv.Perm (Fin (P.p + P.q - S'.rowSlots.card)))
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (hπ : S.leibnizPerm τ σ = π)
    (hπ' : S'.leibnizPerm τ' σ' = π)
    (hW : S.W = S'.W) :
    S = S' := by
  have hrow : S.rowSlots = S'.rowSlots := by
    simp [HodgeRowSplit.rowSlots, hW]
  have hmap :
      S.colSlots.map π.toEmbedding = S'.colSlots.map π.toEmbedding := by
    rw [← S.rowSlots_eq_colSlots_image_of_leibnizPerm_eq τ σ π hπ,
      ← S'.rowSlots_eq_colSlots_image_of_leibnizPerm_eq τ' σ' π hπ',
      hrow]
  have hcol : S.colSlots = S'.colSlots :=
    Finset.map_injective π.toEmbedding hmap
  cases S with
  | mk W colSlots W_subset leftCols card_eq =>
      cases S' with
      | mk W' colSlots' W_subset' leftCols' card_eq' =>
          simp only at hW hcol
          subst W'
          subst colSlots'
          rfl

lemma HodgeRowSplit.leibnizPerm_mem_rowSlots_of_mem_colSlots
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)))
    {x : Fin (P.p + P.q)} (hx : x ∈ S.colSlots) :
    S.leibnizPerm τ σ x ∈ S.rowSlots := by
  classical
  let x' : { x // x ∈ S.colSlots } := ⟨x, hx⟩
  let j : Fin S.rowSlots.card :=
    (S.colSlots.orderIsoOfFin S.card_eq.symm).symm x'
  have hxj : S.colSlots.orderEmbOfFin S.card_eq.symm j = x := by
    exact congrArg Subtype.val
      ((S.colSlots.orderIsoOfFin S.card_eq.symm).apply_symm_apply x')
  rw [← hxj, HodgeRowSplit.leibnizPerm_colSlots]
  exact Finset.orderEmbOfFin_mem S.rowSlots rfl (τ j)

lemma HodgeRowSplit.W_subset_rowSlots_compl
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp) :
    S.W ⊆ S.rowSlotsᶜ := by
  intro x hxW
  rw [Finset.mem_compl]
  intro hxrow
  exact (Finset.mem_sdiff.mp hxrow).2 hxW

lemma HodgeRowSplit.permPreimageLeftSlotFinset_symm_subset_hodgeD
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    permPreimageLeftSlotFinset P (S.leibnizPerm τ σ).symm ⊆
      Hodge.hodgeD P ν := by
  intro x hxpre
  have hleft :
      (S.leibnizPerm τ σ).symm x ∈ leftSlotFinset P :=
    (mem_permPreimageLeftSlotFinset_iff P
      (S.leibnizPerm τ σ).symm x).mp hxpre
  have hcol : (S.leibnizPerm τ σ).symm x ∈ S.colSlots :=
    S.leftCols hleft
  have hrow :
      S.leibnizPerm τ σ ((S.leibnizPerm τ σ).symm x) ∈ S.rowSlots :=
    S.leibnizPerm_mem_rowSlots_of_mem_colSlots τ σ hcol
  have hxrow : x ∈ S.rowSlots := by
    simpa using hrow
  exact (Finset.mem_sdiff.mp hxrow).1

lemma HodgeRowSplit.W_mem_powerset_hodgeC_sdiff_permPreimage_symm
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (τ : Equiv.Perm (Fin S.rowSlots.card))
    (σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card))) :
    S.W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P (S.leibnizPerm τ σ).symm).powerset := by
  classical
  refine Finset.mem_powerset.mpr ?_
  intro x hxW
  refine Finset.mem_sdiff.mpr ⟨S.W_subset hxW, ?_⟩
  intro hxpre
  have hxrowcomp : x ∈ S.rowSlotsᶜ := S.W_subset_rowSlots_compl hxW
  have hleft :
      (S.leibnizPerm τ σ).symm x ∈ leftSlotFinset P :=
    (mem_permPreimageLeftSlotFinset_iff P
      (S.leibnizPerm τ σ).symm x).mp hxpre
  have hcol : (S.leibnizPerm τ σ).symm x ∈ S.colSlots :=
    S.leftCols hleft
  have hrow :
      S.leibnizPerm τ σ ((S.leibnizPerm τ σ).symm x) ∈ S.rowSlots :=
    S.leibnizPerm_mem_rowSlots_of_mem_colSlots τ σ hcol
  exact (Finset.mem_compl.mp hxrowcomp) (by simpa using hrow)

noncomputable def HodgeRowSplit.ofWPerm
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (W : Finset (Fin (P.p + P.q)))
    (hpreD : permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν)
    (hW : W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P π.symm).powerset) :
    HodgeRowSplit P ν hνp where
  W := W
  colSlots := (Hodge.hodgeD P ν \ W).map π.symm.toEmbedding
  W_subset := by
    intro x hxW
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hW) hxW)).1
  leftCols := by
    intro x hxleft
    have hxpre :
        π x ∈ permPreimageLeftSlotFinset P π.symm := by
      rw [mem_permPreimageLeftSlotFinset_iff]
      simpa using hxleft
    have hxD : π x ∈ Hodge.hodgeD P ν := hpreD hxpre
    have hxnotW : π x ∉ W := by
      intro hxW
      have hxsdiff :
          π x ∈ Hodge.hodgeC P ν hνp \
            permPreimageLeftSlotFinset P π.symm :=
        (Finset.mem_powerset.mp hW) hxW
      exact (Finset.mem_sdiff.mp hxsdiff).2 hxpre
    refine Finset.mem_map.mpr ?_
    exact ⟨π x, Finset.mem_sdiff.mpr ⟨hxD, hxnotW⟩, by simp⟩
  card_eq := by
    simp

@[simp] lemma HodgeRowSplit.ofWPerm_W
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (W : Finset (Fin (P.p + P.q)))
    (hpreD : permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν)
    (hW : W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P π.symm).powerset) :
    (HodgeRowSplit.ofWPerm P ν hνp π W hpreD hW).W = W := rfl

@[simp] lemma HodgeRowSplit.ofWPerm_rowSlots
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (W : Finset (Fin (P.p + P.q)))
    (hpreD : permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν)
    (hW : W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P π.symm).powerset) :
    (HodgeRowSplit.ofWPerm P ν hνp π W hpreD hW).rowSlots =
      Hodge.hodgeD P ν \ W := rfl

lemma HodgeRowSplit.exists_leibnizPerm_eq_of_rowSlots_eq_colSlots_image
    {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : HodgeRowSplit P ν hνp)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (hrow : S.rowSlots = S.colSlots.map π.toEmbedding) :
    ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
    ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
      S.leibnizPerm τ σ = π := by
  classical
  let τFun : Fin S.rowSlots.card → Fin S.rowSlots.card := fun j =>
    (S.rowSlots.orderIsoOfFin rfl).symm
      ⟨π (S.colSlots.orderEmbOfFin S.card_eq.symm j), by
        have hj : S.colSlots.orderEmbOfFin S.card_eq.symm j ∈ S.colSlots :=
          Finset.orderEmbOfFin_mem S.colSlots S.card_eq.symm j
        have hmem :
            π (S.colSlots.orderEmbOfFin S.card_eq.symm j) ∈
              S.colSlots.map π.toEmbedding :=
          Finset.mem_map.mpr
            ⟨S.colSlots.orderEmbOfFin S.card_eq.symm j, hj, rfl⟩
        simpa only [hrow] using hmem⟩
  have hτFun :
      ∀ j : Fin S.rowSlots.card,
        S.rowSlots.orderEmbOfFin rfl (τFun j) =
          π (S.colSlots.orderEmbOfFin S.card_eq.symm j) := by
    intro j
    exact congrArg Subtype.val
      ((S.rowSlots.orderIsoOfFin rfl).apply_symm_apply
        ⟨π (S.colSlots.orderEmbOfFin S.card_eq.symm j), by
          have hj : S.colSlots.orderEmbOfFin S.card_eq.symm j ∈ S.colSlots :=
            Finset.orderEmbOfFin_mem S.colSlots S.card_eq.symm j
          have hmem :
              π (S.colSlots.orderEmbOfFin S.card_eq.symm j) ∈
                S.colSlots.map π.toEmbedding :=
            Finset.mem_map.mpr
              ⟨S.colSlots.orderEmbOfFin S.card_eq.symm j, hj, rfl⟩
          simpa only [hrow] using hmem⟩)
  have hτInj : Function.Injective τFun := by
    intro a b hab
    have h := congrArg (fun j => S.rowSlots.orderEmbOfFin rfl j) hab
    simp only at h
    rw [hτFun a, hτFun b] at h
    exact (S.colSlots.orderEmbOfFin S.card_eq.symm).injective (π.injective h)
  have hτBij : Function.Bijective τFun :=
    (Fintype.bijective_iff_injective_and_card τFun).mpr ⟨hτInj, rfl⟩
  let τ : Equiv.Perm (Fin S.rowSlots.card) := Equiv.ofBijective τFun hτBij
  have hτ :
      ∀ j : Fin S.rowSlots.card,
        S.rowSlots.orderEmbOfFin rfl (τ j) =
          π (S.colSlots.orderEmbOfFin S.card_eq.symm j) := by
    intro j
    exact hτFun j
  let hrowCompl :
      S.rowSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  let hcolCompl :
      S.colSlotsᶜ.card = P.p + P.q - S.rowSlots.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    simp
  let σFun :
      Fin (P.p + P.q - S.rowSlots.card) →
        Fin (P.p + P.q - S.rowSlots.card) := fun j =>
    (S.rowSlotsᶜ.orderIsoOfFin hrowCompl).symm
      ⟨π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j), by
        have hjc :
            S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ S.colSlotsᶜ :=
          Finset.orderEmbOfFin_mem S.colSlotsᶜ hcolCompl j
        rw [Finset.mem_compl] at hjc
        rw [Finset.mem_compl]
        intro hrowmem
        have hrowmem' :
            π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) ∈
              S.colSlots.map π.toEmbedding := hrow ▸ hrowmem
        rcases Finset.mem_map.mp hrowmem' with ⟨y, hy, hyπ⟩
        have hxy :
            S.colSlotsᶜ.orderEmbOfFin hcolCompl j = y :=
          π.injective hyπ.symm
        exact hjc (by rw [hxy]; exact hy)⟩
  have hσFun :
      ∀ j : Fin (P.p + P.q - S.rowSlots.card),
        S.rowSlotsᶜ.orderEmbOfFin hrowCompl (σFun j) =
          π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) := by
    intro j
    exact congrArg Subtype.val
      ((S.rowSlotsᶜ.orderIsoOfFin hrowCompl).apply_symm_apply
        ⟨π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j), by
          have hjc :
              S.colSlotsᶜ.orderEmbOfFin hcolCompl j ∈ S.colSlotsᶜ :=
            Finset.orderEmbOfFin_mem S.colSlotsᶜ hcolCompl j
          rw [Finset.mem_compl] at hjc
          rw [Finset.mem_compl]
          intro hrowmem
          have hrowmem' :
              π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) ∈
                S.colSlots.map π.toEmbedding := hrow ▸ hrowmem
          rcases Finset.mem_map.mp hrowmem' with ⟨y, hy, hyπ⟩
          have hxy :
              S.colSlotsᶜ.orderEmbOfFin hcolCompl j = y :=
            π.injective hyπ.symm
          exact hjc (by rw [hxy]; exact hy)⟩)
  have hσInj : Function.Injective σFun := by
    intro a b hab
    have h := congrArg (fun j => S.rowSlotsᶜ.orderEmbOfFin hrowCompl j) hab
    simp only at h
    rw [hσFun a, hσFun b] at h
    exact (S.colSlotsᶜ.orderEmbOfFin hcolCompl).injective (π.injective h)
  have hσBij : Function.Bijective σFun :=
    (Fintype.bijective_iff_injective_and_card σFun).mpr ⟨hσInj, rfl⟩
  let σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)) :=
    Equiv.ofBijective σFun hσBij
  have hσ :
      ∀ j : Fin (P.p + P.q - S.rowSlots.card),
        S.rowSlotsᶜ.orderEmbOfFin hrowCompl (σ j) =
          π (S.colSlotsᶜ.orderEmbOfFin hcolCompl j) := by
    intro j
    exact hσFun j
  refine ⟨τ, σ, ?_⟩
  ext x
  by_cases hx : x ∈ S.colSlots
  · let x' : { x // x ∈ S.colSlots } := ⟨x, hx⟩
    let j : Fin S.rowSlots.card := (S.colSlots.orderIsoOfFin S.card_eq.symm).symm x'
    have hxj : S.colSlots.orderEmbOfFin S.card_eq.symm j = x := by
      exact congrArg Subtype.val
        ((S.colSlots.orderIsoOfFin S.card_eq.symm).apply_symm_apply x')
    rw [← hxj]
    rw [HodgeRowSplit.leibnizPerm_colSlots]
    simpa using congrArg Fin.val (hτ j)
  · have hxc : x ∈ S.colSlotsᶜ := by
      simpa [Finset.mem_compl] using hx
    let x' : { x // x ∈ S.colSlotsᶜ } := ⟨x, hxc⟩
    let j : Fin (P.p + P.q - S.rowSlots.card) :=
      (S.colSlotsᶜ.orderIsoOfFin hcolCompl).symm x'
    have hxj : S.colSlotsᶜ.orderEmbOfFin hcolCompl j = x := by
      exact congrArg Subtype.val
        ((S.colSlotsᶜ.orderIsoOfFin hcolCompl).apply_symm_apply x')
    rw [← hxj]
    rw [HodgeRowSplit.leibnizPerm_colSlots_compl]
    simpa using congrArg Fin.val (hσ j)

lemma HodgeRowSplit.exists_leibnizPerm_eq_of_W_mem_powerset
    {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p)
    (π : Equiv.Perm (Fin (P.p + P.q)))
    (W : Finset (Fin (P.p + P.q)))
    (hpreD : permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν)
    (hW : W ∈ (Hodge.hodgeC P ν hνp \
      permPreimageLeftSlotFinset P π.symm).powerset) :
    ∃ S : HodgeRowSplit P ν hνp,
    ∃ τ : Equiv.Perm (Fin S.rowSlots.card),
    ∃ σ : Equiv.Perm (Fin (P.p + P.q - S.rowSlots.card)),
      S.W = W ∧ S.leibnizPerm τ σ = π := by
  classical
  let S : HodgeRowSplit P ν hνp :=
    HodgeRowSplit.ofWPerm P ν hνp π W hpreD hW
  have hrow : S.rowSlots = S.colSlots.map π.toEmbedding := by
    ext x
    simp [S, HodgeRowSplit.ofWPerm, HodgeRowSplit.rowSlots]
  rcases S.exists_leibnizPerm_eq_of_rowSlots_eq_colSlots_image π hrow with
    ⟨τ, σ, hπ⟩
  exact ⟨S, τ, σ, rfl, hπ⟩

namespace HodgeRowSplit.LeibnizTerm

abbrev AmbientW {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :=
  { pw : Equiv.Perm (Fin (P.p + P.q)) × Finset (Fin (P.p + P.q)) //
    permPreimageLeftSlotFinset P pw.1.symm ⊆ Hodge.hodgeD P ν ∧
      pw.2 ∈ (Hodge.hodgeC P ν hνp \
        permPreimageLeftSlotFinset P pw.1.symm).powerset }

noncomputable def toAmbientWFlat {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (X : HodgeRowSplit.LeibnizTerm P ν hνp) :
    AmbientW P ν hνp :=
  ⟨(X.ambientPerm, X.1.W),
    X.1.permPreimageLeftSlotFinset_symm_subset_hodgeD X.2.1 X.2.2,
    X.1.W_mem_powerset_hodgeC_sdiff_permPreimage_symm X.2.1 X.2.2⟩

lemma toAmbientWFlat_injective {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p} :
    Function.Injective
      (@HodgeRowSplit.LeibnizTerm.toAmbientWFlat m n P ν hνp) := by
  classical
  intro X Y h
  cases X with
  | mk S p =>
      cases p with
      | mk τ σ =>
          cases Y with
          | mk S' p' =>
              cases p' with
              | mk τ' σ' =>
                  have hπ :
                      S.leibnizPerm τ σ = S'.leibnizPerm τ' σ' :=
                    congrArg (fun z : AmbientW P ν hνp => z.1.1) h
                  have hW : S.W = S'.W :=
                    congrArg (fun z : AmbientW P ν hνp => z.1.2) h
                  have hS : S = S' :=
                    HodgeRowSplit.eq_of_W_eq_of_leibnizPerm_eq
                      (S := S) (S' := S') τ σ τ' σ'
                      (S.leibnizPerm τ σ) rfl hπ.symm hW
                  cases hS
                  have hp : (τ, σ) = (τ', σ') :=
                    S.leibnizPerm_pair_injective hπ
                  cases hp
                  rfl

lemma toAmbientWFlat_surjective {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    Function.Surjective
      (@HodgeRowSplit.LeibnizTerm.toAmbientWFlat m n P ν hνp) := by
  classical
  intro Y
  rcases Y with ⟨⟨π, W⟩, hpreD, hW⟩
  rcases HodgeRowSplit.exists_leibnizPerm_eq_of_W_mem_powerset
      P ν hνp π W hpreD hW with ⟨S, τ, σ, hSW, hπ⟩
  refine ⟨⟨S, (τ, σ)⟩, ?_⟩
  apply Subtype.ext
  simp [HodgeRowSplit.LeibnizTerm.toAmbientWFlat,
    HodgeRowSplit.LeibnizTerm.ambientPerm, hπ, hSW]

noncomputable def equivAmbientWFlat {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    HodgeRowSplit.LeibnizTerm P ν hνp ≃ AmbientW P ν hνp :=
  Equiv.ofBijective
    (@HodgeRowSplit.LeibnizTerm.toAmbientWFlat m n P ν hνp)
    ⟨toAmbientWFlat_injective, toAmbientWFlat_surjective P ν hνp⟩

noncomputable def ambientWEquivSigma {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    AmbientW P ν hνp ≃
      Σ π : Equiv.Perm (Fin (P.p + P.q)),
        { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π.symm).powerset } where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv := by
    intro z
    rfl
  right_inv := by
    intro z
    rfl

noncomputable def equivAmbientW {m n : ℕ} (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    HodgeRowSplit.LeibnizTerm P ν hνp ≃
      Σ π : Equiv.Perm (Fin (P.p + P.q)),
        { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π.symm).powerset } :=
  (equivAmbientWFlat P ν hνp).trans (ambientWEquivSigma P ν hνp)

lemma sum_eq_sum_ambientW {m n : ℕ} {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    {M : Type*} [AddCommMonoid M]
    (f : HodgeRowSplit.LeibnizTerm P ν hνp → M)
    (g :
      (π : Equiv.Perm (Fin (P.p + P.q))) →
        { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π.symm).powerset } → M)
    (h :
      ∀ X : HodgeRowSplit.LeibnizTerm P ν hνp,
        f X =
          g X.ambientPerm
            ⟨X.1.W,
              X.1.permPreimageLeftSlotFinset_symm_subset_hodgeD X.2.1 X.2.2,
              X.1.W_mem_powerset_hodgeC_sdiff_permPreimage_symm X.2.1 X.2.2⟩) :
    (∑ X : HodgeRowSplit.LeibnizTerm P ν hνp, f X) =
      ∑ π : Equiv.Perm (Fin (P.p + P.q)),
        ∑ W : { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π.symm).powerset },
          g π W := by
  classical
  calc
    (∑ X : HodgeRowSplit.LeibnizTerm P ν hνp, f X)
        =
      ∑ Y :
          (Σ π : Equiv.Perm (Fin (P.p + P.q)),
            { W : Finset (Fin (P.p + P.q)) //
              permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν ∧
                W ∈ (Hodge.hodgeC P ν hνp \
                  permPreimageLeftSlotFinset P π.symm).powerset }),
        g Y.1 Y.2 := by
          refine Fintype.sum_equiv
            (HodgeRowSplit.LeibnizTerm.equivAmbientW P ν hνp)
            f (fun Y => g Y.1 Y.2) ?_
          intro X
          simpa [HodgeRowSplit.LeibnizTerm.equivAmbientW,
            HodgeRowSplit.LeibnizTerm.equivAmbientWFlat,
            HodgeRowSplit.LeibnizTerm.ambientWEquivSigma,
            HodgeRowSplit.LeibnizTerm.toAmbientWFlat] using h X
    _ =
      ∑ π : Equiv.Perm (Fin (P.p + P.q)),
        ∑ W : { W : Finset (Fin (P.p + P.q)) //
          permPreimageLeftSlotFinset P π.symm ⊆ Hodge.hodgeD P ν ∧
            W ∈ (Hodge.hodgeC P ν hνp \
              permPreimageLeftSlotFinset P π.symm).powerset },
          g π W := by
          rw [Fintype.sum_sigma]

end HodgeRowSplit.LeibnizTerm

lemma ContainingSplit.pivot_toBiReshuffle_toPair_left_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n) :
    RawMinorIndex.toPolynomial k
        (ContainingSplit.pivot P).toBiReshuffle.toPair.left =
      RawMinorIndex.toPolynomial k P.left := by
  classical
  unfold RawMinorIndex.toPolynomial
  let r : ℕ := (leftSlotFinset P).card
  let hp : r = P.p := card_leftSlotFinset P
  let e : Fin r ≃ Fin P.p := finCongr hp
  let A : Matrix (Fin P.p) (Fin P.p) (MvPolynomial (Fin m × Fin n) k) :=
    Matrix.submatrix (genericMatrix m n k) P.left.row P.left.col
  have hmatrix :
      Matrix.submatrix (genericMatrix m n k)
          (ContainingSplit.pivot P).toBiReshuffle.toPair.left.row
          (ContainingSplit.pivot P).toBiReshuffle.toPair.left.col =
        Matrix.submatrix A e e := by
    change
      Matrix.submatrix (genericMatrix m n k)
          (fun i : Fin r =>
            P.slotRow
              ((ofFinsets P (leftSlotFinset P) (leftSlotFinset P) rfl).rowEquiv
                (Sum.inl i)))
          (fun j : Fin r =>
            P.slotCol
              ((ofFinsets P (leftSlotFinset P) (leftSlotFinset P) rfl).colEquiv
                (Sum.inl j))) =
        Matrix.submatrix A e e
    ext i j
    simp only [A, e, Matrix.submatrix_apply, ofFinsets_rowEquiv_inl,
      ofFinsets_colEquiv_inl, RawMinorPair.slotRow, RawMinorPair.slotCol]
    have hrow :
        (leftSlotFinset P).orderEmbOfFin rfl i =
          Fin.castAdd P.q (e i) := by
      exact leftSlotFinset_orderEmbOfFin_cast P rfl hp i
    have hcolj :
        (leftSlotFinset P).orderEmbOfFin rfl j =
          Fin.castAdd P.q (e j) := by
      exact leftSlotFinset_orderEmbOfFin_cast P rfl hp j
    rw [hrow, hcolj]
    simp [finSumFinEquiv_symm_apply_castAdd, e]
  rw [hmatrix]
  exact Matrix.det_submatrix_equiv_self e A

lemma ContainingSplit.pivot_toBiReshuffle_toPair_right_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n) :
    RawMinorIndex.toPolynomial k
        (ContainingSplit.pivot P).toBiReshuffle.toPair.right =
      RawMinorIndex.toPolynomial k P.right := by
  classical
  unfold RawMinorIndex.toPolynomial
  let r : ℕ := P.p + P.q - (leftSlotFinset P).card
  let hq : r = P.q := by
    simp [r]
  let e : Fin r ≃ Fin P.q := finCongr hq
  let A : Matrix (Fin P.q) (Fin P.q) (MvPolynomial (Fin m × Fin n) k) :=
    Matrix.submatrix (genericMatrix m n k) P.right.row P.right.col
  have hmatrix :
      Matrix.submatrix (genericMatrix m n k)
          (ContainingSplit.pivot P).toBiReshuffle.toPair.right.row
          (ContainingSplit.pivot P).toBiReshuffle.toPair.right.col =
        Matrix.submatrix A e e := by
    change
      Matrix.submatrix (genericMatrix m n k)
          (fun i : Fin r =>
            P.slotRow
              ((ofFinsets P (leftSlotFinset P) (leftSlotFinset P) rfl).rowEquiv
                (Sum.inr i)))
          (fun j : Fin r =>
            P.slotCol
              ((ofFinsets P (leftSlotFinset P) (leftSlotFinset P) rfl).colEquiv
                (Sum.inr j))) =
        Matrix.submatrix A e e
    ext i j
    simp only [A, e, Matrix.submatrix_apply, ofFinsets_rowEquiv_inr,
      ofFinsets_colEquiv_inr, RawMinorPair.slotRow, RawMinorPair.slotCol]
    have hrow :
        ((leftSlotFinset P)ᶜ).orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]) i =
          Fin.natAdd P.p (e i) := by
      exact leftSlotFinset_compl_orderEmbOfFin_cast P
        (by rw [Finset.card_compl, Fintype.card_fin])
        hq i
    have hcolj :
        ((leftSlotFinset P)ᶜ).orderEmbOfFin (by
            rw [Finset.card_compl, Fintype.card_fin]) j =
          Fin.natAdd P.p (e j) := by
      exact leftSlotFinset_compl_orderEmbOfFin_cast P
        (by rw [Finset.card_compl, Fintype.card_fin])
        hq j
    rw [hrow, hcolj]
    simp [finSumFinEquiv_symm_apply_natAdd, e]
  rw [hmatrix]
  exact Matrix.det_submatrix_equiv_self e A

lemma ContainingSplit.pivot_toBiReshuffle_toPair_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n) :
    RawMinorPair.toPolynomial k
        (ContainingSplit.pivot P).toBiReshuffle.toPair =
      RawMinorPair.toPolynomial k P := by
  rw [RawMinorPair.toPolynomial, RawMinorPair.toPolynomial,
    ContainingSplit.pivot_toBiReshuffle_toPair_left_toPolynomial k P,
    ContainingSplit.pivot_toBiReshuffle_toPair_right_toPolynomial k P]

def permuteBlocks {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P)
    (ρL : Equiv.Perm (Fin E.r))
    (ρR : Equiv.Perm (Fin (P.p + P.q - E.r)))
    (κL : Equiv.Perm (Fin E.r))
    (κR : Equiv.Perm (Fin (P.p + P.q - E.r))) :
    BiReshuffle P where
  r := E.r
  hle := E.hle
  rowEquiv := (Equiv.sumCongr ρL ρR).trans E.rowEquiv
  colEquiv := (Equiv.sumCongr κL κR).trans E.colEquiv

lemma toPair_permuteBlocks {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P)
    (ρL : Equiv.Perm (Fin E.r))
    (ρR : Equiv.Perm (Fin (P.p + P.q - E.r)))
    (κL : Equiv.Perm (Fin E.r))
    (κR : Equiv.Perm (Fin (P.p + P.q - E.r))) :
    (E.permuteBlocks ρL ρR κL κR).toPair =
      E.toPair.permute ρL κL ρR κR := by
  rfl

noncomputable def sorted {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) : BiReshuffle P :=
  E.permuteBlocks
    (Tuple.sort E.toPair.left.row)
    (Tuple.sort E.toPair.right.row)
    (Tuple.sort E.toPair.left.col)
    (Tuple.sort E.toPair.right.col)

lemma toPair_sorted {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) :
    E.sorted.toPair = E.toPair.sorted := by
  rfl

lemma rowContent_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) :
    RawMinorPair.rowContent E.toPair = RawMinorPair.rowContent P := by
  classical
  rw [RawMinorPair.rowContent_eq_sum_slots,
    RawMinorPair.rowContent_eq_sum_slots]
  have hleft :
      (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          Finsupp.single (E.toPair.slotRow s) 1) =
        ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          Finsupp.single (P.slotRow (E.rowEquiv s)) 1 := by
    apply Finset.sum_congr rfl
    intro s _hs
    cases s <;> rfl
  calc
    (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        Finsupp.single (E.toPair.slotRow s) 1)
        =
      ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        Finsupp.single (P.slotRow (E.rowEquiv s)) 1 := hleft
    _ =
      ∑ s : Sum (Fin P.p) (Fin P.q),
        Finsupp.single (P.slotRow s) 1 := by
        simpa using
          (Fintype.sum_equiv E.rowEquiv
            (fun s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)) =>
              Finsupp.single (P.slotRow (E.rowEquiv s)) 1)
            (fun s : Sum (Fin P.p) (Fin P.q) =>
              Finsupp.single (P.slotRow s) 1)
            (by intro s; rfl))

lemma colContent_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) :
    RawMinorPair.colContent E.toPair = RawMinorPair.colContent P := by
  classical
  rw [RawMinorPair.colContent_eq_sum_slots,
    RawMinorPair.colContent_eq_sum_slots]
  have hleft :
      (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          Finsupp.single (E.toPair.slotCol s) 1) =
        ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          Finsupp.single (P.slotCol (E.colEquiv s)) 1 := by
    apply Finset.sum_congr rfl
    intro s _hs
    cases s <;> rfl
  calc
    (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        Finsupp.single (E.toPair.slotCol s) 1)
        =
      ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        Finsupp.single (P.slotCol (E.colEquiv s)) 1 := hleft
    _ =
      ∑ s : Sum (Fin P.p) (Fin P.q),
        Finsupp.single (P.slotCol s) 1 := by
        simpa using
          (Fintype.sum_equiv E.colEquiv
            (fun s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)) =>
              Finsupp.single (P.slotCol (E.colEquiv s)) 1)
            (fun s : Sum (Fin P.p) (Fin P.q) =>
              Finsupp.single (P.slotCol s) 1)
            (by intro s; rfl))

lemma rowIndexSum_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) :
    RawMinorPair.rowIndexSum E.toPair = RawMinorPair.rowIndexSum P := by
  classical
  rw [RawMinorPair.rowIndexSum_eq_sum_slots,
    RawMinorPair.rowIndexSum_eq_sum_slots]
  have hleft :
      (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          (E.toPair.slotRow s).val) =
        ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          (P.slotRow (E.rowEquiv s)).val := by
    apply Finset.sum_congr rfl
    intro s _hs
    cases s <;> rfl
  calc
    (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        (E.toPair.slotRow s).val)
        =
      ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        (P.slotRow (E.rowEquiv s)).val := hleft
    _ =
      ∑ s : Sum (Fin P.p) (Fin P.q),
        (P.slotRow s).val := by
        simpa using
          (Fintype.sum_equiv E.rowEquiv
            (fun s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)) =>
              (P.slotRow (E.rowEquiv s)).val)
            (fun s : Sum (Fin P.p) (Fin P.q) =>
              (P.slotRow s).val)
            (by intro s; rfl))

lemma colIndexSum_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) :
    RawMinorPair.colIndexSum E.toPair = RawMinorPair.colIndexSum P := by
  classical
  rw [RawMinorPair.colIndexSum_eq_sum_slots,
    RawMinorPair.colIndexSum_eq_sum_slots]
  have hleft :
      (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          (E.toPair.slotCol s).val) =
        ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
          (P.slotCol (E.colEquiv s)).val := by
    apply Finset.sum_congr rfl
    intro s _hs
    cases s <;> rfl
  calc
    (∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        (E.toPair.slotCol s).val)
        =
      ∑ s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)),
        (P.slotCol (E.colEquiv s)).val := hleft
    _ =
      ∑ s : Sum (Fin P.p) (Fin P.q),
        (P.slotCol s).val := by
        simpa using
          (Fintype.sum_equiv E.colEquiv
            (fun s : Sum (Fin E.r) (Fin (P.p + P.q - E.r)) =>
              (P.slotCol (E.colEquiv s)).val)
            (fun s : Sum (Fin P.p) (Fin P.q) =>
              (P.slotCol s).val)
            (by intro s; rfl))

lemma laplaceSignExponent_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) :
    RawMinorPair.laplaceSignExponent E.toPair =
      RawMinorPair.laplaceSignExponent P := by
  simp [RawMinorPair.laplaceSignExponent, E.rowIndexSum_toPair,
    E.colIndexSum_toPair]

lemma laplaceCoeff_toPair {m n : ℕ} {P : RawMinorPair m n}
    (k : Type*) [CommRing k] (E : BiReshuffle P) :
    RawMinorPair.laplaceCoeff k E.toPair =
      RawMinorPair.laplaceCoeff k P := by
  simp [RawMinorPair.laplaceCoeff, E.laplaceSignExponent_toPair]

lemma laplacePolynomial_toPair {m n : ℕ} {P : RawMinorPair m n}
    (k : Type*) [CommRing k] (E : BiReshuffle P) :
    RawMinorPair.laplacePolynomial k E.toPair =
      MvPolynomial.C (RawMinorPair.laplaceCoeff k P) *
        RawMinorPair.toPolynomial k E.toPair := by
  simp [RawMinorPair.laplacePolynomial, RawMinorPair.BiReshuffle.laplaceCoeff_toPair k E]

lemma ContainingSplit.pivot_toBiReshuffle_toPair_laplacePolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n) :
    RawMinorPair.laplacePolynomial k
        (ContainingSplit.pivot P).toBiReshuffle.toPair =
      RawMinorPair.laplacePolynomial k P := by
  rw [RawMinorPair.BiReshuffle.laplacePolynomial_toPair k]
  rw [ContainingSplit.pivot_toBiReshuffle_toPair_toPolynomial k P]
  rfl

lemma HodgeColSplit.pivot_toBiReshuffle_toPair_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    RawMinorPair.toPolynomial k
        (HodgeColSplit.pivot P ν hνp).toBiReshuffle.toPair =
      RawMinorPair.toPolynomial k P := by
  simpa [HodgeColSplit.toBiReshuffle, HodgeColSplit.pivot,
    HodgeColSplit.colSlots, Hodge.hodgeD_sdiff_rightPrefix] using
      ContainingSplit.pivot_toBiReshuffle_toPair_toPolynomial k P

lemma HodgeRowSplit.pivot_toBiReshuffle_toPair_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    RawMinorPair.toPolynomial k
        (HodgeRowSplit.pivot P ν hνp).toBiReshuffle.toPair =
      RawMinorPair.toPolynomial k P := by
  simpa [HodgeRowSplit.toBiReshuffle, HodgeRowSplit.pivot,
    HodgeRowSplit.rowSlots, Hodge.hodgeD_sdiff_rightPrefix] using
      ContainingSplit.pivot_toBiReshuffle_toPair_toPolynomial k P

lemma HodgeColSplit.pivot_toBiReshuffle_toPair_laplacePolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    RawMinorPair.laplacePolynomial k
        (HodgeColSplit.pivot P ν hνp).toBiReshuffle.toPair =
      RawMinorPair.laplacePolynomial k P := by
  rw [RawMinorPair.BiReshuffle.laplacePolynomial_toPair k]
  rw [HodgeColSplit.pivot_toBiReshuffle_toPair_toPolynomial k P ν hνp]
  rfl

lemma HodgeRowSplit.pivot_toBiReshuffle_toPair_laplacePolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n)
    (ν : Fin P.q) (hνp : ν.val < P.p) :
    RawMinorPair.laplacePolynomial k
        (HodgeRowSplit.pivot P ν hνp).toBiReshuffle.toPair =
      RawMinorPair.laplacePolynomial k P := by
  rw [RawMinorPair.BiReshuffle.laplacePolynomial_toPair k]
  rw [HodgeRowSplit.pivot_toBiReshuffle_toPair_toPolynomial k P ν hνp]
  rfl

lemma sorted_toPair_left_row_strictMono_of_injective {m n : ℕ}
    {P : RawMinorPair m n} (E : BiReshuffle P)
    (h : Function.Injective E.toPair.left.row) :
    StrictMono E.sorted.toPair.left.row := by
  rw [E.toPair_sorted]
  exact RawMinorPair.sorted_left_row_strictMono E.toPair h

lemma sorted_toPair_left_col_strictMono_of_injective {m n : ℕ}
    {P : RawMinorPair m n} (E : BiReshuffle P)
    (h : Function.Injective E.toPair.left.col) :
    StrictMono E.sorted.toPair.left.col := by
  rw [E.toPair_sorted]
  exact RawMinorPair.sorted_left_col_strictMono E.toPair h

lemma sorted_toPair_right_row_strictMono_of_injective {m n : ℕ}
    {P : RawMinorPair m n} (E : BiReshuffle P)
    (h : Function.Injective E.toPair.right.row) :
    StrictMono E.sorted.toPair.right.row := by
  rw [E.toPair_sorted]
  exact RawMinorPair.sorted_right_row_strictMono E.toPair h

lemma sorted_toPair_right_col_strictMono_of_injective {m n : ℕ}
    {P : RawMinorPair m n} (E : BiReshuffle P)
    (h : Function.Injective E.toPair.right.col) :
    StrictMono E.sorted.toPair.right.col := by
  rw [E.toPair_sorted]
  exact RawMinorPair.sorted_right_col_strictMono E.toPair h

lemma rowContent_sorted_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) :
    RawMinorPair.rowContent E.sorted.toPair = RawMinorPair.rowContent P := by
  rw [E.toPair_sorted, RawMinorPair.rowContent_sorted, E.rowContent_toPair]

lemma colContent_sorted_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) :
    RawMinorPair.colContent E.sorted.toPair = RawMinorPair.colContent P := by
  rw [E.toPair_sorted, RawMinorPair.colContent_sorted, E.colContent_toPair]

lemma laplacePolynomial_sorted_toPair {m n : ℕ} {P : RawMinorPair m n}
    (k : Type*) [CommRing k] (E : BiReshuffle P) :
    RawMinorPair.laplacePolynomial k E.sorted.toPair =
      RawMinorPair.sortSign k E.toPair *
        RawMinorPair.laplacePolynomial k E.toPair := by
  rw [E.toPair_sorted, RawMinorPair.laplacePolynomial_sorted]

noncomputable def code {m n : ℕ} {P : RawMinorPair m n}
    (E : BiReshuffle P) :
    Sigma (fun r : Fin (P.p + P.q + 1) =>
      (Sum (Fin r.1) (Fin (P.p + P.q - r.1)) ≃
        Sum (Fin P.p) (Fin P.q)) ×
      (Sum (Fin r.1) (Fin (P.p + P.q - r.1)) ≃
        Sum (Fin P.p) (Fin P.q))) :=
  ⟨⟨E.r, Nat.lt_succ_of_le E.hle⟩, (E.rowEquiv, E.colEquiv)⟩

lemma code_injective {m n : ℕ} {P : RawMinorPair m n} :
    Function.Injective (BiReshuffle.code (P := P)) := by
  intro E E' h
  cases E
  cases h
  rfl

instance instFinite {m n : ℕ} {P : RawMinorPair m n} :
    Finite (BiReshuffle P) := by
  classical
  exact Finite.of_injective (BiReshuffle.code (P := P)) BiReshuffle.code_injective

noncomputable instance instFintype {m n : ℕ} {P : RawMinorPair m n} :
    Fintype (BiReshuffle P) := by
  classical
  exact Fintype.ofFinite (BiReshuffle P)

end BiReshuffle

def ofMinorPair {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    RawMinorPair m n where
  p := p
  q := q
  left := RawMinorIndex.ofMinorIndex I
  right := RawMinorIndex.ofMinorIndex J

@[simp] lemma toPolynomial_ofMinorPair {m n p q : ℕ}
    {k : Type*} [CommRing k]
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    RawMinorPair.toPolynomial k (RawMinorPair.ofMinorPair I J) =
      genericMinor k I * genericMinor k J := by
  rfl

@[simp] lemma rowContent_ofMinorPair {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    RawMinorPair.rowContent (RawMinorPair.ofMinorPair I J) =
      MinorIndex.rowContent I + MinorIndex.rowContent J := by
  rfl

@[simp] lemma colContent_ofMinorPair {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    RawMinorPair.colContent (RawMinorPair.ofMinorPair I J) =
      MinorIndex.colContent I + MinorIndex.colContent J := by
  rfl

lemma toPolynomial_eq_zero_of_left_row_not_injective {m n : ℕ}
    (k : Type*) [CommRing k]
    (P : RawMinorPair m n)
    (h : ¬ Function.Injective P.left.row) :
    RawMinorPair.toPolynomial k P = 0 := by
  simp [RawMinorPair.toPolynomial,
    RawMinorIndex.toPolynomial_eq_zero_of_not_injective_row k P.left h]

lemma toPolynomial_eq_zero_of_left_col_not_injective {m n : ℕ}
    (k : Type*) [CommRing k]
    (P : RawMinorPair m n)
    (h : ¬ Function.Injective P.left.col) :
    RawMinorPair.toPolynomial k P = 0 := by
  simp [RawMinorPair.toPolynomial,
    RawMinorIndex.toPolynomial_eq_zero_of_not_injective_col k P.left h]

lemma toPolynomial_eq_zero_of_right_row_not_injective {m n : ℕ}
    (k : Type*) [CommRing k]
    (P : RawMinorPair m n)
    (h : ¬ Function.Injective P.right.row) :
    RawMinorPair.toPolynomial k P = 0 := by
  simp [RawMinorPair.toPolynomial,
    RawMinorIndex.toPolynomial_eq_zero_of_not_injective_row k P.right h]

lemma toPolynomial_eq_zero_of_right_col_not_injective {m n : ℕ}
    (k : Type*) [CommRing k]
    (P : RawMinorPair m n)
    (h : ¬ Function.Injective P.right.col) :
    RawMinorPair.toPolynomial k P = 0 := by
  simp [RawMinorPair.toPolynomial,
    RawMinorIndex.toPolynomial_eq_zero_of_not_injective_col k P.right h]

end RawMinorPair

/-! ## Minor words for local straightening -/

/-- One minor factor in a local straightening word.

Unlike `YoungBitableau`, this deliberately allows `t = 0`, so Swan's unit
factor `(∅|∅) = 1` can be represented without forcing it into the dependent
Young-bitableau shape. -/
structure MinorFactor (m n : ℕ) where
  t : ℕ
  idx : MinorIndex m n t

namespace MinorFactor

noncomputable def toPolynomial (k : Type*) [CommRing k] {m n : ℕ}
    (F : MinorFactor m n) : MvPolynomial (Fin m × Fin n) k :=
  genericMinor k F.idx

lemma toPolynomial_eq_one_of_size_zero {m n : ℕ} (k : Type*) [CommRing k]
    (F : MinorFactor m n) (hF : F.t = 0) :
    MinorFactor.toPolynomial k F = 1 := by
  cases F with
  | mk t idx =>
      subst hF
      simp [MinorFactor.toPolynomial]

def degree {m n : ℕ} (F : MinorFactor m n) : ℕ := F.t

def length {m n : ℕ} (F : MinorFactor m n) : ℕ := F.t

noncomputable def rowContent {m n : ℕ} (F : MinorFactor m n) : Fin m →₀ ℕ :=
  MinorIndex.rowContent F.idx

/-- Total row-content multiplicity of a minor factor is its size. -/
lemma rowContent_total {m n : ℕ} (F : MinorFactor m n) :
    (∑ i : Fin m, MinorFactor.rowContent F i) = F.t := by
  cases F with
  | mk t idx =>
      simpa [MinorFactor.rowContent] using MinorIndex.rowContent_total idx

noncomputable def colContent {m n : ℕ} (F : MinorFactor m n) : Fin n →₀ ℕ :=
  MinorIndex.colContent F.idx

/-- Total column-content multiplicity of a minor factor is its size. -/
lemma colContent_total {m n : ℕ} (F : MinorFactor m n) :
    (∑ j : Fin n, MinorFactor.colContent F j) = F.t := by
  cases F with
  | mk t idx =>
      simpa [MinorFactor.colContent] using MinorIndex.colContent_total idx

/-- Two minor factors are equal if they are mutually comparable in Swan's
minor-index order. -/
lemma eq_of_pairLE_pairLE {m n : ℕ} {F G : MinorFactor m n}
    (hFG : MinorIndex.PairLE F.idx G.idx)
    (hGF : MinorIndex.PairLE G.idx F.idx) :
    F = G := by
  cases F with
  | mk Ft Fidx =>
      cases G with
      | mk Gt Gidx =>
          have hsize : Gt = Ft := le_antisymm hFG.size_le hGF.size_le
          subst Gt
          have hrow : Fidx.row = Gidx.row := by
            ext i
            apply le_antisymm
            · simpa using hFG.row_le i
            · simpa using hGF.row_le i
          have hcol : Fidx.col = Gidx.col := by
            ext i
            apply le_antisymm
            · simpa using hFG.col_le i
            · simpa using hGF.col_le i
          have hidx : Fidx = Gidx := by
            cases Fidx
            cases Gidx
            simp_all
          subst hidx
          rfl

lemma eq_of_rowContent_eq_colContent {m n : ℕ} {F G : MinorFactor m n}
    (hrow : MinorFactor.rowContent F = MinorFactor.rowContent G)
    (hcol : MinorFactor.colContent F = MinorFactor.colContent G) :
    F = G := by
  cases F with
  | mk Ft Fidx =>
      cases G with
      | mk Gt Gidx =>
          have hsize : Ft = Gt := by
            have hsum :=
              congrArg (fun c : Fin m →₀ ℕ => ∑ i : Fin m, c i) hrow
            simpa [MinorFactor.rowContent,
              MinorIndex.rowContent_total] using hsum
          subst Gt
          have hidx :
              Fidx = Gidx :=
            MinorIndex.eq_of_rowContent_eq_colContent
              (by simpa [MinorFactor.rowContent] using hrow)
              (by simpa [MinorFactor.colContent] using hcol)
          subst hidx
          rfl

/-- Strict order on minor factors induced by Swan's strict minor-pair order. -/
def PairLT {m n : ℕ} (F G : MinorFactor m n) : Prop :=
  MinorIndex.PairLT F.idx G.idx

lemma PairLT.irrefl {m n : ℕ} (F : MinorFactor m n) : ¬ PairLT F F := by
  intro h
  exact h.not_pairLE_symm h.pairLE

lemma PairLT.trans {m n : ℕ} {F G H : MinorFactor m n}
    (hFG : PairLT F G) (hGH : PairLT G H) : PairLT F H := by
  refine ⟨MinorIndex.PairLE.trans hFG.pairLE hGH.pairLE, ?_⟩
  intro hHF
  exact hGH.not_pairLE_symm (MinorIndex.PairLE.trans hHF hFG.pairLE)

instance instIsTransPairLT {m n : ℕ} : IsTrans (MinorFactor m n) PairLT where
  trans := fun _ _ _ => PairLT.trans

instance instIrreflPairLT {m n : ℕ} : Std.Irrefl (@PairLT m n) where
  irrefl := PairLT.irrefl

private lemma size_le_min_of_minorIndex {m n t : ℕ} (I : MinorIndex m n t) :
    t ≤ min m n := by
  have hm : t ≤ m := by
    simpa using Fintype.card_le_of_injective I.row I.row.injective
  have hn : t ≤ n := by
    simpa using Fintype.card_le_of_injective I.col I.col.injective
  exact le_min hm hn

private def finiteCode {m n : ℕ} (F : MinorFactor m n) :
    Sigma (fun t : Fin (min m n + 1) => MinorIndex m n t.val) :=
  ⟨⟨F.t, Nat.lt_succ_of_le (size_le_min_of_minorIndex F.idx)⟩, F.idx⟩

private lemma finiteCode_injective {m n : ℕ} :
    Function.Injective (@finiteCode m n) := by
  intro F G h
  cases F with
  | mk Ft Fidx =>
      cases G with
      | mk Gt Gidx =>
          cases h
          rfl

instance instFiniteMinorFactor {m n : ℕ} : Finite (MinorFactor m n) := by
  classical
  exact Finite.of_injective (@finiteCode m n) finiteCode_injective

/-- Swan's strict first-factor order is well-founded on minor factors. -/
theorem pairLT_wellFounded {m n : ℕ} :
    WellFounded (@PairLT m n) := by
  classical
  exact Finite.wellFounded_of_trans_of_irrefl (@PairLT m n)

instance instWellFoundedRelationPairLT {m n : ℕ} :
    WellFoundedRelation (MinorFactor m n) where
  rel := PairLT
  wf := pairLT_wellFounded

end MinorFactor

/-- A local product of minors used for Swan's two-minor straightening step.

This is intentionally lighter than `YoungBitableau`: it is just a list of minor
factors and permits zero-size factors, which evaluate to `1`. -/
structure MinorWord (m n : ℕ) where
  factors : List (MinorFactor m n)

namespace MinorWord

noncomputable def toPolynomial (k : Type*) [CommRing k] {m n : ℕ}
    (W : MinorWord m n) : MvPolynomial (Fin m × Fin n) k :=
  (W.factors.map fun F => MinorFactor.toPolynomial k F).prod

@[simp] lemma toPolynomial_nil {m n : ℕ} (k : Type*) [CommRing k] :
    MinorWord.toPolynomial k ⟨([] : List (MinorFactor m n))⟩ = 1 := by
  simp [MinorWord.toPolynomial]

@[simp] lemma toPolynomial_cons {m n : ℕ} (k : Type*) [CommRing k]
    (F : MinorFactor m n) (Fs : List (MinorFactor m n)) :
    MinorWord.toPolynomial k ⟨F :: Fs⟩ =
      MinorFactor.toPolynomial k F *
        MinorWord.toPolynomial k ⟨Fs⟩ := by
  simp [MinorWord.toPolynomial]

@[simp] lemma toPolynomial_append {m n : ℕ} (k : Type*) [CommRing k]
    (Fs Gs : List (MinorFactor m n)) :
    MinorWord.toPolynomial k ⟨Fs ++ Gs⟩ =
      MinorWord.toPolynomial k ⟨Fs⟩ *
        MinorWord.toPolynomial k ⟨Gs⟩ := by
  induction Fs with
  | nil =>
      simp
  | cons F Fs ih =>
      simp [ih, mul_assoc]

/-- Remove zero-size factors, which are polynomial units by `genericMinor_zero`. -/
def eraseUnits {m n : ℕ} (W : MinorWord m n) : MinorWord m n :=
  ⟨W.factors.filter fun F => F.t ≠ 0⟩

def degree {m n : ℕ} (W : MinorWord m n) : ℕ :=
  W.factors.foldr (fun F d => F.degree + d) 0

@[simp] lemma degree_nil {m n : ℕ} :
    MinorWord.degree ⟨([] : List (MinorFactor m n))⟩ = 0 := by
  rfl

@[simp] lemma degree_cons {m n : ℕ}
    (F : MinorFactor m n) (Fs : List (MinorFactor m n)) :
    MinorWord.degree ⟨F :: Fs⟩ =
      F.degree + MinorWord.degree ⟨Fs⟩ := by
  rfl

@[simp] lemma degree_append {m n : ℕ}
    (Fs Gs : List (MinorFactor m n)) :
    MinorWord.degree ⟨Fs ++ Gs⟩ =
      MinorWord.degree ⟨Fs⟩ + MinorWord.degree ⟨Gs⟩ := by
  induction Fs with
  | nil =>
      simp
  | cons F Fs ih =>
      simp [ih, Nat.add_assoc]

def length {m n : ℕ} (W : MinorWord m n) : ℕ :=
  W.factors.foldr (fun F r => max F.length r) 0

def factorCount {m n : ℕ} (W : MinorWord m n) : ℕ :=
  W.factors.length

@[simp] lemma factorCount_nil {m n : ℕ} :
    MinorWord.factorCount ⟨([] : List (MinorFactor m n))⟩ = 0 := by
  rfl

@[simp] lemma factorCount_cons {m n : ℕ}
    (F : MinorFactor m n) (Fs : List (MinorFactor m n)) :
    MinorWord.factorCount ⟨F :: Fs⟩ =
      (MinorWord.factorCount ⟨Fs⟩) + 1 := by
  simp [MinorWord.factorCount]

@[simp] lemma factorCount_append {m n : ℕ}
    (Fs Gs : List (MinorFactor m n)) :
    MinorWord.factorCount ⟨Fs ++ Gs⟩ =
      MinorWord.factorCount ⟨Fs⟩ + MinorWord.factorCount ⟨Gs⟩ := by
  simp [MinorWord.factorCount]

@[simp] lemma length_nil {m n : ℕ} :
    MinorWord.length ⟨([] : List (MinorFactor m n))⟩ = 0 := by
  rfl

@[simp] lemma length_cons {m n : ℕ}
    (F : MinorFactor m n) (Fs : List (MinorFactor m n)) :
    MinorWord.length ⟨F :: Fs⟩ =
      max F.length (MinorWord.length ⟨Fs⟩) := by
  rfl

@[simp] lemma length_append {m n : ℕ}
    (Fs Gs : List (MinorFactor m n)) :
    MinorWord.length ⟨Fs ++ Gs⟩ =
      max (MinorWord.length ⟨Fs⟩) (MinorWord.length ⟨Gs⟩) := by
  induction Fs with
  | nil =>
      simp
  | cons F Fs ih =>
      simp [ih, max_assoc]

lemma length_le_of_mem_factor {m n : ℕ}
    {F : MinorFactor m n} {W : MinorWord m n}
    (hF : F ∈ W.factors) :
    F.t ≤ MinorWord.length W := by
  cases W with
  | mk factors =>
      induction factors with
      | nil =>
          simp at hF
      | cons G Gs ih =>
          rw [MinorWord.length_cons]
          rw [List.mem_cons] at hF
          rcases hF with rfl | hF
          · exact le_max_left F.t (MinorWord.length ⟨Gs⟩)
          · exact le_trans (ih hF) (le_max_right G.t (MinorWord.length ⟨Gs⟩))

lemma length_le_of_forall_mem_factor_le {m n : ℕ}
    {W : MinorWord m n} {r : ℕ}
    (h : ∀ F ∈ W.factors, F.t ≤ r) :
    MinorWord.length W ≤ r := by
  cases W with
  | mk factors =>
      induction factors with
      | nil =>
          simp
      | cons F Fs ih =>
          rw [MinorWord.length_cons]
          exact max_le (h F (by simp)) (ih (by
            intro G hG
            exact h G (by simp [hG])))

noncomputable def rowContent {m n : ℕ} (W : MinorWord m n) : Fin m →₀ ℕ :=
  W.factors.foldr (fun F c => F.rowContent + c) 0

@[simp] lemma rowContent_nil {m n : ℕ} :
    MinorWord.rowContent ⟨([] : List (MinorFactor m n))⟩ = 0 := by
  rfl

@[simp] lemma rowContent_cons {m n : ℕ}
    (F : MinorFactor m n) (Fs : List (MinorFactor m n)) :
    MinorWord.rowContent ⟨F :: Fs⟩ =
      F.rowContent + MinorWord.rowContent ⟨Fs⟩ := by
  rfl

@[simp] lemma rowContent_append {m n : ℕ}
    (Fs Gs : List (MinorFactor m n)) :
    MinorWord.rowContent ⟨Fs ++ Gs⟩ =
      MinorWord.rowContent ⟨Fs⟩ + MinorWord.rowContent ⟨Gs⟩ := by
  induction Fs with
  | nil =>
      simp
  | cons F Fs ih =>
      simp [ih, add_assoc]

/-- Total row-content multiplicity of a minor word is its degree. -/
lemma rowContent_total {m n : ℕ} (W : MinorWord m n) :
    (∑ i : Fin m, MinorWord.rowContent W i) = MinorWord.degree W := by
  cases W with
  | mk factors =>
      induction factors with
      | nil =>
          simp [MinorWord.rowContent, MinorWord.degree]
      | cons F Fs ih =>
          change
            (∑ i : Fin m,
              (MinorFactor.rowContent F +
                ({ factors := Fs } : MinorWord m n).rowContent) i) =
              MinorFactor.degree F + ({ factors := Fs } : MinorWord m n).degree
          simp [Finset.sum_add_distrib, MinorFactor.rowContent_total,
            MinorFactor.degree, ih]

noncomputable def colContent {m n : ℕ} (W : MinorWord m n) : Fin n →₀ ℕ :=
  W.factors.foldr (fun F c => F.colContent + c) 0

@[simp] lemma colContent_nil {m n : ℕ} :
    MinorWord.colContent ⟨([] : List (MinorFactor m n))⟩ = 0 := by
  rfl

@[simp] lemma colContent_cons {m n : ℕ}
    (F : MinorFactor m n) (Fs : List (MinorFactor m n)) :
    MinorWord.colContent ⟨F :: Fs⟩ =
      F.colContent + MinorWord.colContent ⟨Fs⟩ := by
  rfl

@[simp] lemma colContent_append {m n : ℕ}
    (Fs Gs : List (MinorFactor m n)) :
    MinorWord.colContent ⟨Fs ++ Gs⟩ =
      MinorWord.colContent ⟨Fs⟩ + MinorWord.colContent ⟨Gs⟩ := by
  induction Fs with
  | nil =>
      simp
  | cons F Fs ih =>
      simp [ih, add_assoc]

lemma eraseUnits_toPolynomial {m n : ℕ} {k : Type*} [CommRing k]
    (W : MinorWord m n) :
    MinorWord.toPolynomial k (MinorWord.eraseUnits W) =
      MinorWord.toPolynomial k W := by
  cases W with
  | mk factors =>
      induction factors with
      | nil =>
          simp [MinorWord.eraseUnits]
      | cons F Fs ih =>
          by_cases hF : F.t = 0
          · have hFpoly :
                MinorFactor.toPolynomial k F = 1 :=
              MinorFactor.toPolynomial_eq_one_of_size_zero k F hF
            simp [MinorWord.eraseUnits, hF, hFpoly]
            simpa [MinorWord.eraseUnits] using ih
          · simp only [eraseUnits, ne_eq, decide_not, hF, decide_false, Bool.not_false,
            List.filter_cons_of_pos, toPolynomial_cons]
            exact congrArg (fun P => MinorFactor.toPolynomial k F * P)
              (by simpa [MinorWord.eraseUnits] using ih)

lemma eraseUnits_degree {m n : ℕ} (W : MinorWord m n) :
    MinorWord.degree (MinorWord.eraseUnits W) = MinorWord.degree W := by
  cases W with
  | mk factors =>
      induction factors with
      | nil =>
          simp [MinorWord.eraseUnits]
      | cons F Fs ih =>
          by_cases hF : F.t = 0
          · simp [MinorWord.eraseUnits, hF, MinorFactor.degree]
            simpa [MinorWord.eraseUnits] using ih
          · simp [MinorWord.eraseUnits, hF]
            simpa [MinorWord.eraseUnits] using ih

lemma eraseUnits_length_le {m n : ℕ} (W : MinorWord m n) :
    MinorWord.length (MinorWord.eraseUnits W) ≤ MinorWord.length W := by
  cases W with
  | mk factors =>
      induction factors with
      | nil =>
          simp [MinorWord.eraseUnits]
      | cons F Fs ih =>
          by_cases hF : F.t = 0
          · simp [MinorWord.eraseUnits, hF, MinorFactor.length]
            simpa [MinorWord.eraseUnits] using ih
          · simp only [eraseUnits, ne_eq, decide_not, hF, decide_false, Bool.not_false,
            List.filter_cons_of_pos, length_cons, MinorFactor.length, le_sup_iff, sup_le_iff,
            le_refl, true_and]
            by_cases htail :
                MinorWord.length (MinorWord.eraseUnits ⟨Fs⟩) ≤ F.t
            · exact Or.inl (by simpa [MinorWord.eraseUnits] using htail)
            · refine Or.inr ⟨?_, by simpa [MinorWord.eraseUnits] using ih⟩
              have hlt :
                  F.t < MinorWord.length (MinorWord.eraseUnits ⟨Fs⟩) :=
                Nat.lt_of_not_ge htail
              exact le_trans hlt.le ih

lemma eraseUnits_length_eq {m n : ℕ} (W : MinorWord m n) :
    MinorWord.length (MinorWord.eraseUnits W) = MinorWord.length W := by
  cases W with
  | mk factors =>
      induction factors with
      | nil =>
          simp [MinorWord.eraseUnits]
      | cons F Fs ih =>
          by_cases hF : F.t = 0
          · simp [MinorWord.eraseUnits, hF, MinorFactor.length]
            simpa [MinorWord.eraseUnits] using ih
          · simp only [eraseUnits, ne_eq, decide_not, hF, decide_false, Bool.not_false,
            List.filter_cons_of_pos, length_cons, MinorFactor.length]
            have ih' :
                MinorWord.length
                    ⟨List.filter (fun F => !decide (F.t = 0)) Fs⟩ =
                  MinorWord.length ⟨Fs⟩ := by
              simpa [MinorWord.eraseUnits] using ih
            exact congrArg (fun r => max F.t r) ih'

lemma eraseUnits_factorCount_le {m n : ℕ} (W : MinorWord m n) :
    MinorWord.factorCount (MinorWord.eraseUnits W) ≤ MinorWord.factorCount W := by
  cases W with
  | mk factors =>
      induction factors with
      | nil =>
          simp [MinorWord.eraseUnits, MinorWord.factorCount]
      | cons F Fs ih =>
          by_cases hF : F.t = 0
          · simp only [factorCount, eraseUnits, ne_eq, decide_not, hF, decide_true, Bool.not_true,
            Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.length_cons]
            have ih' :
                (List.filter (fun F => !decide (F.t = 0)) Fs).length ≤
                  Fs.length := by
              simpa [MinorWord.eraseUnits, MinorWord.factorCount] using ih
            exact Nat.le_trans ih' (Nat.le_succ Fs.length)
          · simp [MinorWord.eraseUnits, MinorWord.factorCount, hF]
            simpa [MinorWord.eraseUnits, MinorWord.factorCount] using ih

lemma factorCount_pos_iff_factors_nonempty {m n : ℕ} (W : MinorWord m n) :
    0 < MinorWord.factorCount W ↔ W.factors ≠ [] := by
  cases W with
  | mk factors =>
      cases factors with
      | nil =>
          simp [MinorWord.factorCount]
      | cons F Fs =>
          simp [MinorWord.factorCount]

lemma exists_cons_of_factorCount_pos {m n : ℕ} {W : MinorWord m n}
    (hW : 0 < MinorWord.factorCount W) :
    ∃ F Fs, W.factors = F :: Fs := by
  cases W with
  | mk factors =>
      cases factors with
      | nil =>
          simp [MinorWord.factorCount] at hW
      | cons F Fs =>
          exact ⟨F, Fs, rfl⟩

/-- The local word is standard if every earlier factor is below every later
factor in Swan's pair order.  This is stored as `List.Pairwise`; the adjacent
chain condition implies it by transitivity, but this predicate is the stronger
all-pairs form. -/
def PairwisePairLE {m n : ℕ} (W : MinorWord m n) : Prop :=
  W.factors.Pairwise fun F G => MinorIndex.PairLE F.idx G.idx

@[simp] lemma PairwisePairLE_nil {m n : ℕ} :
    MinorWord.PairwisePairLE ⟨([] : List (MinorFactor m n))⟩ := by
  simp [MinorWord.PairwisePairLE]

@[simp] lemma PairwisePairLE_singleton {m n : ℕ} (F : MinorFactor m n) :
    MinorWord.PairwisePairLE ⟨[F]⟩ := by
  simp [MinorWord.PairwisePairLE]

lemma PairwisePairLE_cons_iff {m n : ℕ}
    (F : MinorFactor m n) (Fs : List (MinorFactor m n)) :
    MinorWord.PairwisePairLE ⟨F :: Fs⟩ ↔
      (∀ G ∈ Fs, MinorIndex.PairLE F.idx G.idx) ∧
        MinorWord.PairwisePairLE ⟨Fs⟩ := by
  simp [MinorWord.PairwisePairLE, List.pairwise_cons]

lemma PairwisePairLE.eraseUnits {m n : ℕ} {W : MinorWord m n}
    (hW : MinorWord.PairwisePairLE W) :
    MinorWord.PairwisePairLE (MinorWord.eraseUnits W) := by
  cases W with
  | mk factors =>
      simpa [MinorWord.PairwisePairLE, MinorWord.eraseUnits] using
        hW.filter (fun F => F.t ≠ 0)

lemma eraseUnits_pairwisePairLE {m n : ℕ} (W : MinorWord m n)
    (hW : MinorWord.PairwisePairLE W) :
    MinorWord.PairwisePairLE (MinorWord.eraseUnits W) :=
  hW.eraseUnits

lemma PairwisePairLE.cons_of_head_le_first {m n : ℕ}
    {F G : MinorFactor m n} {rest : List (MinorFactor m n)}
    (hFG : MinorIndex.PairLE F.idx G.idx)
    (hTail : MinorWord.PairwisePairLE ⟨G :: rest⟩) :
    MinorWord.PairwisePairLE ⟨F :: G :: rest⟩ := by
  rw [MinorWord.PairwisePairLE_cons_iff]
  constructor
  · intro K hK
    simp only [List.mem_cons] at hK
    rcases hK with rfl | hKrest
    · exact hFG
    · have hGK : MinorIndex.PairLE G.idx K.idx := by
        exact (MinorWord.PairwisePairLE_cons_iff G rest).mp hTail |>.1 K hKrest
      exact MinorIndex.PairLE.trans hFG hGK
  · exact hTail

lemma PairwisePairLE_of_factorCount_le_one {m n : ℕ}
    {W : MinorWord m n} (hW : MinorWord.factorCount W ≤ 1) :
    MinorWord.PairwisePairLE W := by
  cases W with
  | mk factors =>
      cases factors with
      | nil =>
          simp [MinorWord.PairwisePairLE]
      | cons F Fs =>
          cases Fs with
          | nil =>
              simp [MinorWord.PairwisePairLE]
          | cons G Gs =>
              simp [MinorWord.factorCount] at hW

lemma two_le_factorCount_of_not_pairwisePairLE {m n : ℕ}
    {W : MinorWord m n} (hW : ¬ MinorWord.PairwisePairLE W) :
    2 ≤ MinorWord.factorCount W := by
  by_contra hlt
  have hlt' : MinorWord.factorCount W < 2 := Nat.lt_of_not_ge hlt
  have hle : MinorWord.factorCount W ≤ 1 := Nat.le_of_lt_succ hlt'
  exact hW (MinorWord.PairwisePairLE_of_factorCount_le_one hle)

lemma exists_two_cons_of_two_le_factorCount {m n : ℕ}
    {W : MinorWord m n} (hW : 2 ≤ MinorWord.factorCount W) :
    ∃ F G rest, W.factors = F :: G :: rest := by
  cases W with
  | mk factors =>
      cases factors with
      | nil =>
          simp [MinorWord.factorCount] at hW
      | cons F Fs =>
          cases Fs with
          | nil =>
              simp [MinorWord.factorCount] at hW
          | cons G rest =>
              exact ⟨F, G, rest, rfl⟩

lemma tail_not_pairwisePairLE_of_cons_cons_not_pairwise_of_head_le
    {m n : ℕ} {F G : MinorFactor m n} {rest : List (MinorFactor m n)}
    (hFG : MinorIndex.PairLE F.idx G.idx)
    (hW : ¬ MinorWord.PairwisePairLE ⟨F :: G :: rest⟩) :
    ¬ MinorWord.PairwisePairLE ⟨G :: rest⟩ := by
  intro hTail
  exact hW (MinorWord.PairwisePairLE.cons_of_head_le_first hFG hTail)

/-- The two-factor word attached to an adjacent product of minors. -/
def ofPair {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) : MinorWord m n :=
  ⟨[{ t := p, idx := I }, { t := q, idx := J }]⟩

@[simp] lemma ofPair_factors {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    (MinorWord.ofPair I J).factors =
      [{ t := p, idx := I }, { t := q, idx := J }] := by
  rfl

@[simp] lemma toPolynomial_ofPair {m n p q : ℕ}
    {k : Type*} [CommRing k]
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    MinorWord.toPolynomial k (MinorWord.ofPair I J) =
      genericMinor k I * genericMinor k J := by
  simp [MinorWord.ofPair, MinorFactor.toPolynomial]

@[simp] lemma degree_ofPair {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    MinorWord.degree (MinorWord.ofPair I J) = p + q := by
  simp [MinorWord.ofPair, MinorFactor.degree]

@[simp] lemma rowContent_ofPair {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    MinorWord.rowContent (MinorWord.ofPair I J) =
      MinorIndex.rowContent I + MinorIndex.rowContent J := by
  simp [MinorWord.ofPair, MinorFactor.rowContent]

@[simp] lemma colContent_ofPair {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    MinorWord.colContent (MinorWord.ofPair I J) =
      MinorIndex.colContent I + MinorIndex.colContent J := by
  simp [MinorWord.ofPair, MinorFactor.colContent]

lemma pairwisePairLE_ofPair {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hIJ : MinorIndex.PairLE I J) :
    MinorWord.PairwisePairLE (MinorWord.ofPair I J) := by
  simp [MinorWord.PairwisePairLE, MinorWord.ofPair, hIJ]

end MinorWord

/-!
The raw-pair namespace is reopened here to connect sorted raw reshuffles with
the `MinorWord` abstraction used by the straightening recursion.
-/

namespace RawMinorPair

/-- Promote the left raw factor of a raw pair to a `MinorFactor` when its row
and column slots are already strictly increasing. -/
def leftFactorOfStrictMono {m n : ℕ} (P : RawMinorPair m n)
    (hrow : StrictMono P.left.row) (hcol : StrictMono P.left.col) :
    MinorFactor m n where
  t := P.p
  idx := P.left.toMinorIndexOfStrictMono hrow hcol

/-- Promote the right raw factor of a raw pair to a `MinorFactor` when its row
and column slots are already strictly increasing. -/
def rightFactorOfStrictMono {m n : ℕ} (P : RawMinorPair m n)
    (hrow : StrictMono P.right.row) (hcol : StrictMono P.right.col) :
    MinorFactor m n where
  t := P.q
  idx := P.right.toMinorIndexOfStrictMono hrow hcol

/-- Promote a raw two-minor product to a two-factor minor word when both raw
factors are already in increasing row and column order. -/
def toMinorWordOfStrictMono {m n : ℕ} (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col) :
    MinorWord m n :=
  { factors :=
      [P.leftFactorOfStrictMono hLrow hLcol,
        P.rightFactorOfStrictMono hRrow hRcol] }

@[simp] lemma toMinorWordOfStrictMono_factors {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col) :
    (P.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol).factors =
      [P.leftFactorOfStrictMono hLrow hLcol,
        P.rightFactorOfStrictMono hRrow hRcol] := by
  rfl

lemma toPolynomial_toMinorWordOfStrictMono {m n : ℕ}
    (k : Type*) [CommRing k]
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col) :
    MinorWord.toPolynomial k
        (P.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol) =
      RawMinorPair.toPolynomial k P := by
  simp only [MinorWord.toPolynomial, MinorFactor.toPolynomial, toMinorWordOfStrictMono,
    leftFactorOfStrictMono, rightFactorOfStrictMono, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, toPolynomial]
  rw [RawMinorIndex.toPolynomial_toMinorIndexOfStrictMono k P.left hLrow hLcol,
    RawMinorIndex.toPolynomial_toMinorIndexOfStrictMono k P.right hRrow hRcol]

lemma rowContent_toMinorWordOfStrictMono {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col) :
    MinorWord.rowContent
        (P.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol) =
      RawMinorPair.rowContent P := by
  simp [RawMinorPair.toMinorWordOfStrictMono,
    RawMinorPair.leftFactorOfStrictMono, RawMinorPair.rightFactorOfStrictMono,
    MinorWord.rowContent, MinorFactor.rowContent, RawMinorPair.rowContent]

lemma colContent_toMinorWordOfStrictMono {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col) :
    MinorWord.colContent
        (P.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol) =
      RawMinorPair.colContent P := by
  simp [RawMinorPair.toMinorWordOfStrictMono,
    RawMinorPair.leftFactorOfStrictMono, RawMinorPair.rightFactorOfStrictMono,
    MinorWord.colContent, MinorFactor.colContent, RawMinorPair.colContent]

lemma degree_toMinorWordOfStrictMono {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col) :
    MinorWord.degree
        (P.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol) =
      P.p + P.q := by
  simp [RawMinorPair.toMinorWordOfStrictMono,
    RawMinorPair.leftFactorOfStrictMono, RawMinorPair.rightFactorOfStrictMono,
    MinorWord.degree, MinorFactor.degree]

lemma length_toMinorWordOfStrictMono {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col) :
    MinorWord.length
        (P.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol) =
      max P.p P.q := by
  simp [RawMinorPair.toMinorWordOfStrictMono,
    RawMinorPair.leftFactorOfStrictMono, RawMinorPair.rightFactorOfStrictMono,
    MinorWord.length, MinorFactor.length]

noncomputable def toMinorWordOfSortedOfInjective {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : Function.Injective P.left.row)
    (hLcol : Function.Injective P.left.col)
    (hRrow : Function.Injective P.right.row)
    (hRcol : Function.Injective P.right.col) :
    MinorWord m n :=
  P.sorted.toMinorWordOfStrictMono
    (P.sorted_left_row_strictMono hLrow)
    (P.sorted_left_col_strictMono hLcol)
    (P.sorted_right_row_strictMono hRrow)
    (P.sorted_right_col_strictMono hRcol)

lemma toPolynomial_toMinorWordOfSortedOfInjective {m n : ℕ}
    (k : Type*) [CommRing k] (P : RawMinorPair m n)
    (hLrow : Function.Injective P.left.row)
    (hLcol : Function.Injective P.left.col)
    (hRrow : Function.Injective P.right.row)
    (hRcol : Function.Injective P.right.col) :
    MinorWord.toPolynomial k
        (P.toMinorWordOfSortedOfInjective hLrow hLcol hRrow hRcol) =
      RawMinorPair.sortSign k P * RawMinorPair.toPolynomial k P := by
  rw [RawMinorPair.toMinorWordOfSortedOfInjective,
    RawMinorPair.toPolynomial_toMinorWordOfStrictMono,
    RawMinorPair.toPolynomial_sorted]

lemma rowContent_toMinorWordOfSortedOfInjective {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : Function.Injective P.left.row)
    (hLcol : Function.Injective P.left.col)
    (hRrow : Function.Injective P.right.row)
    (hRcol : Function.Injective P.right.col) :
    MinorWord.rowContent
        (P.toMinorWordOfSortedOfInjective hLrow hLcol hRrow hRcol) =
      RawMinorPair.rowContent P := by
  rw [RawMinorPair.toMinorWordOfSortedOfInjective,
    RawMinorPair.rowContent_toMinorWordOfStrictMono,
    RawMinorPair.rowContent_sorted]

lemma colContent_toMinorWordOfSortedOfInjective {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : Function.Injective P.left.row)
    (hLcol : Function.Injective P.left.col)
    (hRrow : Function.Injective P.right.row)
    (hRcol : Function.Injective P.right.col) :
    MinorWord.colContent
        (P.toMinorWordOfSortedOfInjective hLrow hLcol hRrow hRcol) =
      RawMinorPair.colContent P := by
  rw [RawMinorPair.toMinorWordOfSortedOfInjective,
    RawMinorPair.colContent_toMinorWordOfStrictMono,
    RawMinorPair.colContent_sorted]

lemma degree_toMinorWordOfSortedOfInjective {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : Function.Injective P.left.row)
    (hLcol : Function.Injective P.left.col)
    (hRrow : Function.Injective P.right.row)
    (hRcol : Function.Injective P.right.col) :
    MinorWord.degree
        (P.toMinorWordOfSortedOfInjective hLrow hLcol hRrow hRcol) =
      P.p + P.q := by
  rw [RawMinorPair.toMinorWordOfSortedOfInjective,
    RawMinorPair.degree_toMinorWordOfStrictMono]
  simp [RawMinorPair.sorted]

lemma length_toMinorWordOfSortedOfInjective {m n : ℕ}
    (P : RawMinorPair m n)
    (hLrow : Function.Injective P.left.row)
    (hLcol : Function.Injective P.left.col)
    (hRrow : Function.Injective P.right.row)
    (hRcol : Function.Injective P.right.col) :
    MinorWord.length
        (P.toMinorWordOfSortedOfInjective hLrow hLcol hRrow hRcol) =
      max P.p P.q := by
  rw [RawMinorPair.toMinorWordOfSortedOfInjective,
    RawMinorPair.length_toMinorWordOfStrictMono]
  simp [RawMinorPair.sorted]

namespace Reshuffle

lemma rowContent_toMinorWord_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : RawMinorPair.Reshuffle P)
    (hLrow : StrictMono E.toPair.left.row)
    (hLcol : StrictMono E.toPair.left.col)
    (hRrow : StrictMono E.toPair.right.row)
    (hRcol : StrictMono E.toPair.right.col) :
    MinorWord.rowContent
        (E.toPair.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol) =
      RawMinorPair.rowContent P := by
  rw [RawMinorPair.rowContent_toMinorWordOfStrictMono, E.rowContent_toPair]

lemma colContent_toMinorWord_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : RawMinorPair.Reshuffle P)
    (hLrow : StrictMono E.toPair.left.row)
    (hLcol : StrictMono E.toPair.left.col)
    (hRrow : StrictMono E.toPair.right.row)
    (hRcol : StrictMono E.toPair.right.col) :
    MinorWord.colContent
        (E.toPair.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol) =
      RawMinorPair.colContent P := by
  rw [RawMinorPair.colContent_toMinorWordOfStrictMono, E.colContent_toPair]

end Reshuffle

namespace BiReshuffle

def AllInjective {m n : ℕ} {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P) : Prop :=
  Function.Injective E.toPair.left.row ∧
    Function.Injective E.toPair.left.col ∧
    Function.Injective E.toPair.right.row ∧
    Function.Injective E.toPair.right.col

noncomputable instance instFintypeAllInjective {m n : ℕ} {P : RawMinorPair m n} :
    Fintype { E : RawMinorPair.BiReshuffle P // E.AllInjective } := by
  classical
  infer_instance

lemma rowContent_toMinorWord_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (hLrow : StrictMono E.toPair.left.row)
    (hLcol : StrictMono E.toPair.left.col)
    (hRrow : StrictMono E.toPair.right.row)
    (hRcol : StrictMono E.toPair.right.col) :
    MinorWord.rowContent
        (E.toPair.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol) =
      RawMinorPair.rowContent P := by
  rw [RawMinorPair.rowContent_toMinorWordOfStrictMono, E.rowContent_toPair]

lemma colContent_toMinorWord_toPair {m n : ℕ} {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (hLrow : StrictMono E.toPair.left.row)
    (hLcol : StrictMono E.toPair.left.col)
    (hRrow : StrictMono E.toPair.right.row)
    (hRcol : StrictMono E.toPair.right.col) :
    MinorWord.colContent
        (E.toPair.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol) =
      RawMinorPair.colContent P := by
  rw [RawMinorPair.colContent_toMinorWordOfStrictMono, E.colContent_toPair]

lemma toPair_toPolynomial_eq_zero_of_left_row_not_injective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : ¬ Function.Injective E.toPair.left.row) :
    RawMinorPair.toPolynomial k E.toPair = 0 :=
  RawMinorPair.toPolynomial_eq_zero_of_left_row_not_injective k E.toPair h

lemma toPair_toPolynomial_eq_zero_of_left_col_not_injective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : ¬ Function.Injective E.toPair.left.col) :
    RawMinorPair.toPolynomial k E.toPair = 0 :=
  RawMinorPair.toPolynomial_eq_zero_of_left_col_not_injective k E.toPair h

lemma toPair_toPolynomial_eq_zero_of_right_row_not_injective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : ¬ Function.Injective E.toPair.right.row) :
    RawMinorPair.toPolynomial k E.toPair = 0 :=
  RawMinorPair.toPolynomial_eq_zero_of_right_row_not_injective k E.toPair h

lemma toPair_toPolynomial_eq_zero_of_right_col_not_injective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : ¬ Function.Injective E.toPair.right.col) :
    RawMinorPair.toPolynomial k E.toPair = 0 :=
  RawMinorPair.toPolynomial_eq_zero_of_right_col_not_injective k E.toPair h

lemma toPair_laplacePolynomial_eq_zero_of_left_row_not_injective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : ¬ Function.Injective E.toPair.left.row) :
    RawMinorPair.laplacePolynomial k E.toPair = 0 := by
  simp [RawMinorPair.laplacePolynomial,
    RawMinorPair.BiReshuffle.toPair_toPolynomial_eq_zero_of_left_row_not_injective
      k E h]

lemma toPair_laplacePolynomial_eq_zero_of_left_col_not_injective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : ¬ Function.Injective E.toPair.left.col) :
    RawMinorPair.laplacePolynomial k E.toPair = 0 := by
  simp [RawMinorPair.laplacePolynomial,
    RawMinorPair.BiReshuffle.toPair_toPolynomial_eq_zero_of_left_col_not_injective
      k E h]

lemma toPair_laplacePolynomial_eq_zero_of_right_row_not_injective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : ¬ Function.Injective E.toPair.right.row) :
    RawMinorPair.laplacePolynomial k E.toPair = 0 := by
  simp [RawMinorPair.laplacePolynomial,
    RawMinorPair.BiReshuffle.toPair_toPolynomial_eq_zero_of_right_row_not_injective
      k E h]

lemma toPair_laplacePolynomial_eq_zero_of_right_col_not_injective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : ¬ Function.Injective E.toPair.right.col) :
    RawMinorPair.laplacePolynomial k E.toPair = 0 := by
  simp [RawMinorPair.laplacePolynomial,
    RawMinorPair.BiReshuffle.toPair_toPolynomial_eq_zero_of_right_col_not_injective
      k E h]

lemma toPair_left_row_injective_of_strictMono {m n : ℕ} {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : StrictMono E.toPair.left.row) :
    Function.Injective E.toPair.left.row :=
  h.injective

lemma toPair_left_col_injective_of_strictMono {m n : ℕ} {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : StrictMono E.toPair.left.col) :
    Function.Injective E.toPair.left.col :=
  h.injective

lemma toPair_right_row_injective_of_strictMono {m n : ℕ} {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : StrictMono E.toPair.right.row) :
    Function.Injective E.toPair.right.row :=
  h.injective

lemma toPair_right_col_injective_of_strictMono {m n : ℕ} {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : StrictMono E.toPair.right.col) :
    Function.Injective E.toPair.right.col :=
  h.injective

lemma toPair_laplacePolynomial_eq_zero_of_not_all_injective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h :
      ¬ (Function.Injective E.toPair.left.row ∧
        Function.Injective E.toPair.left.col ∧
        Function.Injective E.toPair.right.row ∧
        Function.Injective E.toPair.right.col)) :
    RawMinorPair.laplacePolynomial k E.toPair = 0 := by
  classical
  push_neg at h
  by_cases hLrow : Function.Injective E.toPair.left.row
  · by_cases hLcol : Function.Injective E.toPair.left.col
    · by_cases hRrow : Function.Injective E.toPair.right.row
      · have hRcol : ¬ Function.Injective E.toPair.right.col := h hLrow hLcol hRrow
        exact RawMinorPair.BiReshuffle.toPair_laplacePolynomial_eq_zero_of_right_col_not_injective
          k E hRcol
      · exact RawMinorPair.BiReshuffle.toPair_laplacePolynomial_eq_zero_of_right_row_not_injective
          k E hRrow
    · exact RawMinorPair.BiReshuffle.toPair_laplacePolynomial_eq_zero_of_left_col_not_injective
        k E hLcol
  · exact RawMinorPair.BiReshuffle.toPair_laplacePolynomial_eq_zero_of_left_row_not_injective
      k E hLrow

lemma toPair_laplacePolynomial_eq_zero_of_not_allInjective {m n : ℕ}
    (k : Type*) [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (h : ¬ E.AllInjective) :
    RawMinorPair.laplacePolynomial k E.toPair = 0 :=
  RawMinorPair.BiReshuffle.toPair_laplacePolynomial_eq_zero_of_not_all_injective
    k E h

lemma sum_laplacePolynomial_eq_sum_allInjective {m n : ℕ}
    (k : Type*) [Field k] {P : RawMinorPair m n}
    (coeff : RawMinorPair.BiReshuffle P → k) :
    (∑ E : RawMinorPair.BiReshuffle P,
      MvPolynomial.C (coeff E) *
        RawMinorPair.laplacePolynomial k E.toPair) =
      ∑ E : { E : RawMinorPair.BiReshuffle P // E.AllInjective },
        MvPolynomial.C (coeff E.1) *
          RawMinorPair.laplacePolynomial k E.1.toPair := by
  classical
  let f : RawMinorPair.BiReshuffle P → MvPolynomial (Fin m × Fin n) k :=
    fun E =>
      MvPolynomial.C (coeff E) *
        RawMinorPair.laplacePolynomial k E.toPair
  let s : Finset (RawMinorPair.BiReshuffle P) :=
    Finset.univ.filter fun E => E.AllInjective
  have hsum_s : (∑ E : RawMinorPair.BiReshuffle P, f E) = Finset.sum s f := by
    symm
    refine Finset.sum_subset (by intro E hE; simp) ?_
    intro E _hE hnotmem
    have hnot : ¬ E.AllInjective := by
      intro h
      exact hnotmem (by simp [s, h])
    simp [RawMinorPair.BiReshuffle.toPair_laplacePolynomial_eq_zero_of_not_allInjective k E hnot]
  have hattach :
      Finset.sum s f =
        ∑ E : { E : RawMinorPair.BiReshuffle P // E.AllInjective }, f E.1 := by
    let e :
        { E : RawMinorPair.BiReshuffle P // E ∈ s } ≃
          { E : RawMinorPair.BiReshuffle P // E.AllInjective } :=
      Equiv.subtypeEquivRight fun E => by simp [s]
    calc
      Finset.sum s f = ∑ E : { E // E ∈ s }, f E.1 := by
        simpa using (s.sum_attach f).symm
      _ = ∑ E : { E : RawMinorPair.BiReshuffle P // E.AllInjective }, f E.1 := by
        exact Fintype.sum_equiv e (fun E => f E.1) (fun E => f E.1)
          (by intro E; rfl)
  rw [hsum_s, hattach]

noncomputable def toSortedMinorWordOfAllInjective {m n : ℕ}
    {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (hE : E.AllInjective) : MinorWord m n :=
  E.toPair.toMinorWordOfSortedOfInjective hE.1 hE.2.1 hE.2.2.1 hE.2.2.2

lemma toPolynomial_toSortedMinorWordOfAllInjective {m n : ℕ}
    {k : Type*} [CommRing k] {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (hE : E.AllInjective) :
    MinorWord.toPolynomial k (E.toSortedMinorWordOfAllInjective hE) =
      RawMinorPair.sortSign k E.toPair *
        RawMinorPair.toPolynomial k E.toPair := by
  exact RawMinorPair.toPolynomial_toMinorWordOfSortedOfInjective
    k E.toPair hE.1 hE.2.1 hE.2.2.1 hE.2.2.2

lemma rowContent_toSortedMinorWordOfAllInjective {m n : ℕ}
    {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (hE : E.AllInjective) :
    MinorWord.rowContent (E.toSortedMinorWordOfAllInjective hE) =
      RawMinorPair.rowContent P := by
  rw [RawMinorPair.BiReshuffle.toSortedMinorWordOfAllInjective,
    RawMinorPair.rowContent_toMinorWordOfSortedOfInjective,
    E.rowContent_toPair]

lemma colContent_toSortedMinorWordOfAllInjective {m n : ℕ}
    {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (hE : E.AllInjective) :
    MinorWord.colContent (E.toSortedMinorWordOfAllInjective hE) =
      RawMinorPair.colContent P := by
  rw [RawMinorPair.BiReshuffle.toSortedMinorWordOfAllInjective,
    RawMinorPair.colContent_toMinorWordOfSortedOfInjective,
    E.colContent_toPair]

lemma degree_toSortedMinorWordOfAllInjective {m n : ℕ}
    {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (hE : E.AllInjective) :
    MinorWord.degree (E.toSortedMinorWordOfAllInjective hE) = P.p + P.q := by
  rw [RawMinorPair.BiReshuffle.toSortedMinorWordOfAllInjective,
    RawMinorPair.degree_toMinorWordOfSortedOfInjective]
  simp [RawMinorPair.BiReshuffle.toPair]
  have hle : E.r ≤ P.p + P.q := E.hle
  omega

lemma length_toSortedMinorWordOfAllInjective {m n : ℕ}
    {P : RawMinorPair m n}
    (E : RawMinorPair.BiReshuffle P)
    (hE : E.AllInjective) :
    MinorWord.length (E.toSortedMinorWordOfAllInjective hE) =
      max E.r (P.p + P.q - E.r) := by
  rw [RawMinorPair.BiReshuffle.toSortedMinorWordOfAllInjective,
    RawMinorPair.length_toMinorWordOfSortedOfInjective]
  simp [RawMinorPair.BiReshuffle.toPair]

end BiReshuffle

end RawMinorPair

lemma sum_attach_erase_eq_neg_of_sum_eq_zero
    {α M : Type*} [Fintype α] [DecidableEq α] [AddCommGroup M]
    (pivot : α) (f : α → M)
    (hsum : (∑ x : α, f x) = 0) :
    (∑ x : { x : α // x ∈ Finset.univ.erase pivot }, f x.1) =
      -f pivot := by
  classical
  let s : Finset α := Finset.univ.erase pivot
  have hsplit :
      (∑ x : α, f x) =
        f pivot + Finset.sum s f := by
    have hsplit' :
        f pivot + Finset.sum s f = ∑ x : α, f x := by
      simp [s]
    exact hsplit'.symm
  have hsubtype :
      Finset.sum s f = ∑ x : { x : α // x ∈ s }, f x.1 := by
    simpa using (s.sum_attach f).symm
  have hrest_zero :
      f pivot + Finset.sum s f = 0 := by
    simpa [hsplit] using hsum
  have hrest :
      Finset.sum s f = -f pivot := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hrest_zero)
  simpa [s] using hsubtype.symm.trans hrest

lemma sum_option_eq_none_add_some
    {α M : Type*} [Fintype α] [AddCommMonoid M]
    (f : Option α → M) :
    (∑ x : Option α, f x) = f none + ∑ a : α, f (some a) := by
  classical
  simp

lemma sum_option_eq_zero_iff_none_add_some_eq_zero
    {α M : Type*} [Fintype α] [AddCommMonoid M]
    (f : Option α → M) :
    (∑ x : Option α, f x) = 0 ↔
      f none + ∑ a : α, f (some a) = 0 := by
  rw [sum_option_eq_none_add_some]

lemma sum_some_eq_neg_none_of_sum_option_eq_zero
    {α M : Type*} [Fintype α] [AddCommGroup M]
    (f : Option α → M)
    (hsum : (∑ x : Option α, f x) = 0) :
    (∑ a : α, f (some a)) = -f none := by
  rw [sum_option_eq_none_add_some] at hsum
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hsum)

lemma sum_some_eq_of_none_eq_neg_of_sum_option_eq_zero
    {α M : Type*} [Fintype α] [AddCommGroup M]
    (f : Option α → M) {P : M}
    (hnone : f none = -P)
    (hsum : (∑ x : Option α, f x) = 0) :
    (∑ a : α, f (some a)) = P := by
  have h := sum_some_eq_neg_none_of_sum_option_eq_zero f hsum
  simpa [hnone] using h

lemma fintype_sum_eq_sum_of_injective_support
    {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (g : β → α) (hg : Function.Injective g) (f : α → M)
    (hzero : ∀ a : α, a ∉ Set.range g → f a = 0) :
    (∑ a : α, f a) = ∑ b : β, f (g b) := by
  classical
  let s : Finset α := Finset.univ.image g
  have hsum_s : (∑ a : α, f a) = ∑ a ∈ s, f a := by
    symm
    refine Finset.sum_subset (by intro a ha; simp) ?_
    intro a _ha hnot
    exact hzero a (by
      intro hrange
      rcases hrange with ⟨b, rfl⟩
      exact hnot (by simp [s]))
  have hsum_image : (∑ a ∈ s, f a) = ∑ b : β, f (g b) := by
    rw [Finset.sum_image]
    intro x _hx y _hy hxy
    exact hg hxy
  exact hsum_s.trans hsum_image

lemma fintype_sum_eq_sum_subtype_of_eq_zero_off
    {α M : Type*} [Fintype α] [AddCommMonoid M]
    (s : Finset α) (f : α → M)
    (hzero : ∀ a : α, a ∉ s → f a = 0) :
    (∑ a : α, f a) = ∑ a : { a : α // a ∈ s }, f a.1 := by
  classical
  let g : { a : α // a ∈ s } → α := fun a => a.1
  have hg : Function.Injective g := Subtype.val_injective
  rw [fintype_sum_eq_sum_of_injective_support g hg f]
  intro a ha
  exact hzero a (by
    intro has
    exact ha ⟨⟨a, has⟩, rfl⟩)

lemma signed_subtype_sum_eq_zero_of_total_sum_eq_zero
    {α σ : Type*} (k : Type*) [Fintype α] [Field k]
    {support : α → Prop} [Fintype { a : α // support a }]
    (pivot : α) (hpivot_not : ¬ support pivot)
    (coeff : α → k) (term : α → MvPolynomial σ k)
    (hpivot_coeff : coeff pivot = (-1 : k))
    (hzero :
      ∀ a : α, a ≠ pivot → ¬ support a →
        MvPolynomial.C (coeff a) * term a = 0)
    (hsum :
      (∑ a : α, MvPolynomial.C (coeff a) * term a) = 0) :
    ∃ coeffSupport : { a : α // support a } → k,
      - term pivot +
        ∑ a : { a : α // support a },
          MvPolynomial.C (coeffSupport a) * term a.1 = 0 := by
  classical
  let g : Option { a : α // support a } → α :=
    fun x =>
      match x with
      | none => pivot
      | some a => a.1
  let f : α → MvPolynomial σ k :=
    fun a => MvPolynomial.C (coeff a) * term a
  have hg : Function.Injective g := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            exfalso
            change pivot = y.1 at hxy
            have hy : support pivot := by
              rw [hxy]
              exact y.2
            exact hpivot_not hy
    | some x =>
        cases y with
        | none =>
            exfalso
            change x.1 = pivot at hxy
            have hx : support pivot := by
              rw [← hxy]
              exact x.2
            exact hpivot_not hx
        | some y =>
            change x.1 = y.1 at hxy
            exact congrArg some (Subtype.ext hxy)
  have hzero_range : ∀ a : α, a ∉ Set.range g → f a = 0 := by
    intro a ha
    by_cases hap : a = pivot
    · exact False.elim (ha ⟨none, by rw [hap]⟩)
    · by_cases hsupp : support a
      · exact False.elim (ha ⟨some ⟨a, hsupp⟩, by rfl⟩)
      · exact hzero a hap hsupp
  have hsum_range :
      (∑ a : α, f a) =
        ∑ x : Option { a : α // support a }, f (g x) := by
    exact fintype_sum_eq_sum_of_injective_support g hg f hzero_range
  have hoption :
      (∑ x : Option { a : α // support a }, f (g x)) =
        f pivot + ∑ a : { a : α // support a }, f a.1 := by
    rw [sum_option_eq_none_add_some]
  have hmain :
      f pivot + ∑ a : { a : α // support a }, f a.1 = 0 := by
    simpa [f, hsum_range, hoption] using hsum
  refine ⟨fun a => coeff a.1, ?_⟩
  simpa [f, hpivot_coeff] using hmain

lemma exists_fintype_coeff_pushforward_polynomial_sum
    {α β σ k : Type*} [Fintype α] [Fintype β] [Field k]
    (g : α → β) (coeff : α → k) (term : β → MvPolynomial σ k) :
    ∃ coeff' : β → k,
      (∑ a : α, MvPolynomial.C (coeff a) * term (g a)) =
        ∑ b : β, MvPolynomial.C (coeff' b) * term b := by
  classical
  let cα : α →₀ k := Finsupp.equivFunOnFinite.symm coeff
  let cβ : β →₀ k := Finsupp.mapDomain g cα
  refine ⟨fun b => cβ b, ?_⟩
  change
    (∑ a : α, MvPolynomial.C (coeff a) * term (g a)) =
      ∑ b : β, MvPolynomial.C (cβ b) * term b
  have hright :
      (∑ b : β, MvPolynomial.C (cβ b) * term b) =
        cβ.sum (fun b r => MvPolynomial.C r * term b) := by
    rw [Finsupp.sum_fintype]
    intro b
    simp
  rw [hright]
  change
    (∑ a : α, MvPolynomial.C (coeff a) * term (g a)) =
      (Finsupp.mapDomain g cα).sum
        (fun b r => MvPolynomial.C r * term b)
  rw [Finsupp.sum_mapDomain_index]
  · simp [cα, Finsupp.sum_fintype]
  · intro b
    simp
  · intro b a₁ a₂
    simp [add_mul, MvPolynomial.C_add]

lemma MvPolynomial.C_isUnit_of_isUnit
    {σ k : Type*} [CommSemiring k] {a : k}
    (ha : IsUnit a) :
    IsUnit (MvPolynomial.C a : MvPolynomial σ k) := by
  exact ha.map MvPolynomial.C

lemma MvPolynomial.C_unit_mul_eq_zero_iff
    {σ k : Type*} [CommSemiring k] {a : k}
    (ha : IsUnit a) (P : MvPolynomial σ k) :
    MvPolynomial.C a * P = 0 ↔ P = 0 := by
  constructor
  · intro h
    rcases MvPolynomial.C_isUnit_of_isUnit (σ := σ) ha with ⟨u, hu⟩
    have h' := congrArg (fun Q : MvPolynomial σ k => ↑u⁻¹ * Q) h
    simpa [← hu, mul_assoc] using h'
  · intro h
    simp [h]

lemma signed_sum_cancel_common_C_unit
    {α σ : Type*} (k : Type*) [Fintype α] [Field k]
    (a : k) (ha : IsUnit a)
    (coeff : α → k)
    (P : MvPolynomial σ k) (Q : α → MvPolynomial σ k)
    (h :
      -(MvPolynomial.C a * P) +
        ∑ x : α, MvPolynomial.C (coeff x) *
          (MvPolynomial.C a * Q x) = 0) :
    - P + ∑ x : α, MvPolynomial.C (coeff x) * Q x = 0 := by
  let R : MvPolynomial σ k := - P + ∑ x : α, MvPolynomial.C (coeff x) * Q x
  have hfactor :
      - (MvPolynomial.C a * P) +
        ∑ x : α, MvPolynomial.C (coeff x) *
          (MvPolynomial.C a * Q x) =
        MvPolynomial.C a * R := by
    have hsum :
        (∑ x : α, MvPolynomial.C (coeff x) *
          (MvPolynomial.C a * Q x)) =
          MvPolynomial.C a *
            ∑ x : α, MvPolynomial.C (coeff x) * Q x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    rw [hsum]
    simp [R, mul_add]
  have hzero : MvPolynomial.C a * R = 0 := by
    simpa [hfactor] using h
  exact (MvPolynomial.C_unit_mul_eq_zero_iff (σ := σ) ha R).mp hzero

lemma RawMinorPair.laplaceCoeff_isUnit
    {m n : ℕ} (k : Type*) [Field k]
    (P : RawMinorPair m n) :
    IsUnit (RawMinorPair.laplaceCoeff k P) := by
  unfold RawMinorPair.laplaceCoeff
  exact isUnit_iff_ne_zero.mpr
    (pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0)))

/-- Standard minor words: local-word analogue of standard Young bitableaux. -/
abbrev StandardMinorWord (m n : ℕ) :=
  { W : MinorWord m n // MinorWord.PairwisePairLE W }

namespace YoungBitableau

lemma isStandard_iff_adjacent_pairLE {m n : ℕ} (B : YoungBitableau m n) :
    B.IsStandard ↔
      ∀ (a b : Fin B.v), a.val + 1 = b.val →
        MinorIndex.PairLE (B.minorindex a) (B.minorindex b) := by
  constructor
  · intro hstd a b hnext
    refine ⟨B.shape_antitone a b (by grind), ?_⟩
    intro j
    exact hstd a b hnext j
  · intro hstd a b hnext j
    rcases hstd a b hnext with ⟨hsize, hcomp⟩
    specialize hcomp j
    simpa using hcomp

lemma IsStandard.adjacent_pairLE {m n : ℕ} {B : YoungBitableau m n}
    (hB : B.IsStandard) {a b : Fin B.v} (hnext : a.val + 1 = b.val) :
    MinorIndex.PairLE (B.minorindex a) (B.minorindex b) :=
  (isStandard_iff_adjacent_pairLE B).mp hB a b hnext

lemma isStandard_of_adjacent_pairLE {m n : ℕ} {B : YoungBitableau m n}
    (hB : ∀ (a b : Fin B.v), a.val + 1 = b.val →
      MinorIndex.PairLE (B.minorindex a) (B.minorindex b)) :
    B.IsStandard :=
  (isStandard_iff_adjacent_pairLE B).mpr hB

lemma IsStandard.head_pairLE {m n : ℕ} {B : YoungBitableau m n}
    (hB : B.IsStandard) (hv : 1 < B.v) :
    MinorIndex.PairLE
      (B.minorindex ⟨0, by omega⟩)
      (B.minorindex ⟨1, hv⟩) := by
  exact hB.adjacent_pairLE (a := ⟨0, by omega⟩) (b := ⟨1, hv⟩) rfl

lemma isStandard_of_v_le_one {m n : ℕ} {B : YoungBitableau m n}
    (hBv : B.v ≤ 1) : B.IsStandard := by
  intro a b hnext j
  have hb : b.val < B.v := b.isLt
  have hfalse : False := by omega
  exact False.elim hfalse

lemma two_le_v_of_not_isStandard {m n : ℕ} {B : YoungBitableau m n}
    (hB : ¬ B.IsStandard) : 2 ≤ B.v := by
  by_contra hlt
  exact hB (isStandard_of_v_le_one (B := B) (by omega))

/-- Prepend one minor to a bitableau.  The hypothesis says the new first
minor is at least as large as the old first column, so the Young shape remains
antitone. -/
noncomputable def consMinor {m n t : ℕ}
    (ht : 0 < t) (I : MinorIndex m n t)
    (B : YoungBitableau m n) (hB : B.length ≤ t) :
    YoungBitableau m n where
  v := B.v + 1
  size := Fin.cons t B.size
  size_pos := by
    intro a
    cases a using Fin.cases with
    | zero =>
        simpa [Fin.cons_zero] using ht
    | succ a =>
        simpa [Fin.cons_succ] using B.size_pos a
  minorindex := fun a => by
    cases a using Fin.cases with
    | zero =>
        simpa [Fin.cons_zero] using I
    | succ a =>
        simpa [Fin.cons_succ] using B.minorindex a
  shape_antitone := by
    intro a b hab
    cases b using Fin.cases with
    | zero =>
        cases a using Fin.cases with
        | zero =>
            rfl
        | succ a =>
            have hbad : a.succ.val ≤ (0 : Fin (B.v + 1)).val := hab
            simp at hbad
    | succ b =>
        cases a using Fin.cases with
        | zero =>
            exact le_trans (size_le_length B b) hB
        | succ a =>
            have hab' : a ≤ b := by
              simpa [Fin.succ_le_succ_iff] using hab
            exact B.shape_antitone a b hab'

@[simp] lemma consMinor_size_zero {m n t : ℕ}
    (ht : 0 < t) (I : MinorIndex m n t)
    (B : YoungBitableau m n) (hB : B.length ≤ t) :
    (consMinor ht I B hB).size ⟨0, Nat.succ_pos B.v⟩ = t := by
  simp [consMinor]

@[simp] lemma consMinor_size_succ {m n t : ℕ}
    (ht : 0 < t) (I : MinorIndex m n t)
    (B : YoungBitableau m n) (hB : B.length ≤ t)
    (a : Fin B.v) :
    (consMinor ht I B hB).size a.succ = B.size a := by
  simp [consMinor]

@[simp] lemma toPolynomial_consMinor {m n t : ℕ}
    {k : Type*} [CommRing k]
    (ht : 0 < t) (I : MinorIndex m n t)
    (B : YoungBitableau m n) (hB : B.length ≤ t) :
    toPolynomial k (consMinor ht I B hB) =
      genericMinor k I * toPolynomial k B := by
  change
    (∏ a : Fin (B.v + 1), genericMinor k ((consMinor ht I B hB).minorindex a)) =
      genericMinor k I *
        ∏ a : Fin B.v, genericMinor k (B.minorindex a)
  rw [Fin.prod_univ_succ]
  simp [consMinor]

@[simp] lemma degree_consMinor {m n t : ℕ}
    (ht : 0 < t) (I : MinorIndex m n t)
    (B : YoungBitableau m n) (hB : B.length ≤ t) :
    degree (consMinor ht I B hB) = t + degree B := by
  change
    (∑ a : Fin (B.v + 1), (consMinor ht I B hB).size a) =
      t + ∑ a : Fin B.v, B.size a
  rw [Fin.sum_univ_succ]
  simp [consMinor]

@[simp] lemma length_consMinor {m n t : ℕ}
    (ht : 0 < t) (I : MinorIndex m n t)
    (B : YoungBitableau m n) (hB : B.length ≤ t) :
    length (consMinor ht I B hB) = t := by
  rw [length_eq_size_zero (consMinor ht I B hB) (Nat.succ_pos B.v)]
  simp [consMinor]

lemma consMinor_isStandard {m n t : ℕ}
    (ht : 0 < t) (I : MinorIndex m n t)
    (B : YoungBitableau m n) (hBlen : B.length ≤ t)
    (hIB : ∀ hv : 0 < B.v,
      MinorIndex.PairLE I (B.minorindex ⟨0, hv⟩))
    (hBstd : B.IsStandard) :
    (consMinor ht I B hBlen).IsStandard := by
  rw [isStandard_iff_adjacent_pairLE]
  intro a b hnext
  cases a using Fin.cases with
  | zero =>
      cases b using Fin.cases with
      | zero =>
          have hbad := hnext
          simp at hbad
      | succ b =>
          have hbval : b.val = 0 := by
            exact (Nat.succ.inj hnext).symm
          have hv : 0 < B.v := by
            simpa [hbval] using b.isLt
          have hb0 : b = ⟨0, hv⟩ := by
            apply Fin.ext
            exact hbval
          change MinorIndex.PairLE I (B.minorindex b)
          rw [hb0]
          exact hIB hv
  | succ a =>
      cases b using Fin.cases with
      | zero =>
          have hbad := hnext
          simp at hbad
      | succ b =>
          have hnext' : a.val + 1 = b.val := by
            simpa using hnext
          have htail :=
            (isStandard_iff_adjacent_pairLE B).mp hBstd a b hnext'
          simpa [consMinor] using htail

lemma consMinor_consMinor_isStandard {m n p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (B : YoungBitableau m n)
    (hBlen : B.length ≤ q)
    (hIJ : MinorIndex.PairLE I J)
    (hJB : ∀ hv : 0 < B.v,
      MinorIndex.PairLE J (B.minorindex ⟨0, hv⟩))
    (hBstd : B.IsStandard) :
    (consMinor hp I
      (consMinor hq J B hBlen)
      (by simpa [length_consMinor] using hIJ.size_le)).IsStandard := by
  refine consMinor_isStandard hp I
    (consMinor hq J B hBlen)
    (by simpa [length_consMinor] using hIJ.size_le)
    ?_ ?_
  · intro _hv
    change MinorIndex.PairLE I J
    exact hIJ
  · exact consMinor_isStandard hq J B hBlen hJB hBstd

@[simp] lemma toPolynomial_consMinor_consMinor {m n p q : ℕ}
    {k : Type*} [CommRing k]
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (B : YoungBitableau m n)
    (hBlen : B.length ≤ q)
    (hpq : q ≤ p) :
    toPolynomial k
      (consMinor hp I (consMinor hq J B hBlen)
        (by simpa [length_consMinor] using hpq)) =
      genericMinor k I * genericMinor k J *
        toPolynomial k B := by
  simp [mul_assoc]

@[simp] lemma degree_consMinor_consMinor {m n p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (B : YoungBitableau m n)
    (hBlen : B.length ≤ q)
    (hpq : q ≤ p) :
    degree
      (consMinor hp I (consMinor hq J B hBlen)
        (by simpa [length_consMinor] using hpq)) =
      p + q + degree B := by
  simp [Nat.add_assoc]

@[simp] lemma length_consMinor_consMinor {m n p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (B : YoungBitableau m n)
    (hBlen : B.length ≤ q)
    (hpq : q ≤ p) :
    length
      (consMinor hp I (consMinor hq J B hBlen)
        (by simpa [length_consMinor] using hpq)) = p := by
  simp

/-- Remove the first minor from a nonempty bitableau. -/
noncomputable def tail {m n : ℕ}
    (B : YoungBitableau m n) (hv : 0 < B.v) :
    YoungBitableau m n where
  v := B.v - 1
  size := fun a => B.size ⟨a.val + 1, by omega⟩
  size_pos := by
    intro a
    exact B.size_pos ⟨a.val + 1, by omega⟩
  minorindex := fun a => B.minorindex ⟨a.val + 1, by omega⟩
  shape_antitone := by
    intro a b hab
    apply B.shape_antitone
    change a.val + 1 ≤ b.val + 1
    exact Nat.succ_le_succ hab

@[simp] lemma tail_v {m n : ℕ}
    (B : YoungBitableau m n) (hv : 0 < B.v) :
    (tail B hv).v = B.v - 1 := rfl

lemma tail_v_lt {m n : ℕ}
    (B : YoungBitableau m n) (hv : 0 < B.v) :
    (tail B hv).v < B.v := by
  simp [tail]
  omega

@[simp] lemma tail_size {m n : ℕ}
    (B : YoungBitableau m n) (hv : 0 < B.v)
    (a : Fin (B.v - 1)) :
    (tail B hv).size a = B.size ⟨a.val + 1, by omega⟩ := rfl

@[simp] lemma tail_minorindex {m n : ℕ}
    (B : YoungBitableau m n) (hv : 0 < B.v)
    (a : Fin (B.v - 1)) :
    (tail B hv).minorindex a = B.minorindex ⟨a.val + 1, by omega⟩ := rfl

lemma length_tail_le_head {m n : ℕ}
    (B : YoungBitableau m n) (hv : 0 < B.v) :
    (tail B hv).length ≤ B.size ⟨0, hv⟩ := by
  unfold length
  change
    (Finset.univ.sup
      (fun a : Fin (B.v - 1) => B.size ⟨a.val + 1, by omega⟩)) ≤
      B.size ⟨0, hv⟩
  apply Finset.sup_le
  intro a _ha
  exact B.shape_antitone ⟨0, hv⟩ ⟨a.val + 1, by omega⟩ (by
    change 0 ≤ a.val + 1
    omega)

lemma tail_isStandard_of_isStandard {m n : ℕ}
    (B : YoungBitableau m n) (hv : 0 < B.v)
    (hB : B.IsStandard) :
    (tail B hv).IsStandard := by
  apply isStandard_of_adjacent_pairLE
  intro a b hnext
  have ha : a.val < B.v - 1 := by
    change a.val < B.v - 1
    exact a.isLt
  have hb : b.val < B.v - 1 := by
    change b.val < B.v - 1
    exact b.isLt
  change
    MinorIndex.PairLE
      (B.minorindex ⟨a.val + 1, by omega⟩)
      (B.minorindex ⟨b.val + 1, by omega⟩)
  apply hB.adjacent_pairLE
  change a.val + 1 + 1 = b.val + 1
  omega

lemma head_pairLE_tail_head_of_isStandard {m n : ℕ}
    (B : YoungBitableau m n) (hv : 1 < B.v)
    (hB : B.IsStandard) :
    MinorIndex.PairLE
      (B.minorindex ⟨0, by omega⟩)
      ((tail B (by omega)).minorindex ⟨0, by simp [tail]; omega⟩) := by
  change
    MinorIndex.PairLE
      (B.minorindex ⟨0, by omega⟩)
      (B.minorindex ⟨1, by omega⟩)
  exact hB.head_pairLE hv

lemma toPolynomial_eq_head_mul_tail {m n : ℕ}
    (k : Type*) [CommRing k]
    (B : YoungBitableau m n) (hv : 0 < B.v) :
    toPolynomial k B =
      genericMinor k (B.minorindex ⟨0, hv⟩) *
        toPolynomial k (tail B hv) := by
  cases B with
  | mk v size size_pos minorindex shape_antitone =>
      cases v with
      | zero =>
          cases hv
      | succ v =>
          change
            (∏ a : Fin (v + 1), genericMinor k (minorindex a)) =
              genericMinor k (minorindex ⟨0, Nat.succ_pos v⟩) *
                ∏ a : Fin v,
                  genericMinor k (minorindex ⟨a.val + 1, by omega⟩)
          rw [Fin.prod_univ_succ]
          rfl

lemma degree_eq_head_add_tail {m n : ℕ}
    (B : YoungBitableau m n) (hv : 0 < B.v) :
    degree B = B.size ⟨0, hv⟩ + degree (tail B hv) := by
  cases B with
  | mk v size size_pos minorindex shape_antitone =>
      cases v with
      | zero =>
          cases hv
      | succ v =>
          change
            (∑ a : Fin (v + 1), size a) =
              size ⟨0, Nat.succ_pos v⟩ +
                ∑ a : Fin v, size ⟨a.val + 1, by omega⟩
          rw [Fin.sum_univ_succ]
          rfl

/-- Forget the Young-shape proof and view a Young bitableau as a minor word. -/
noncomputable def toMinorWord {m n : ℕ} (B : YoungBitableau m n) : MinorWord m n :=
  ⟨List.ofFn fun a : Fin B.v => { t := B.size a, idx := B.minorindex a }⟩

lemma toMinorWord_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (B : YoungBitableau m n) :
    MinorWord.toPolynomial k (YoungBitableau.toMinorWord B) =
      YoungBitableau.toPolynomial k B := by
  cases B with
  | mk v size size_pos minorindex shape_antitone =>
      simpa [YoungBitableau.toMinorWord, YoungBitableau.toPolynomial,
        MinorWord.toPolynomial, MinorFactor.toPolynomial,
        Function.comp_def] using
        (Fin.prod_ofFn
          (fun a : Fin v => genericMinor k (minorindex a)))

lemma toMinorWord_degree {m n : ℕ} (B : YoungBitableau m n) :
    MinorWord.degree (YoungBitableau.toMinorWord B) =
      YoungBitableau.degree B := by
  cases B with
  | mk v size size_pos minorindex shape_antitone =>
      change
        List.foldr (fun F d => F.t + d) 0
            (List.ofFn fun a : Fin v =>
              ({ t := size a, idx := minorindex a } : MinorFactor m n)) =
          ∑ x : Fin v, size x
      revert size size_pos minorindex shape_antitone
      induction v with
      | zero =>
          intro size size_pos minorindex shape_antitone
          simp
      | succ v ih =>
          intro size size_pos minorindex shape_antitone
          have htail := ih
            (fun a : Fin v => size a.succ)
            (fun a : Fin v => size_pos a.succ)
            (fun a : Fin v => minorindex a.succ)
            (fun a b hab => shape_antitone a.succ b.succ
              (Fin.succ_le_succ_iff.mpr hab))
          rw [List.ofFn_succ, Fin.sum_univ_succ]
          simpa using htail

lemma toMinorWord_length {m n : ℕ} (B : YoungBitableau m n) :
    MinorWord.length (YoungBitableau.toMinorWord B) =
      YoungBitableau.length B := by
  classical
  apply le_antisymm
  · apply MinorWord.length_le_of_forall_mem_factor_le
    intro F hF
    rw [YoungBitableau.toMinorWord] at hF
    rcases (List.mem_ofFn' _ F).mp hF with ⟨a, ha⟩
    have ht : F.t = B.size a := by
      simpa using congrArg MinorFactor.t ha.symm
    rw [ht]
    exact YoungBitableau.size_le_length B a
  · by_cases hv : 0 < B.v
    · let F : MinorFactor m n :=
        { t := B.size ⟨0, hv⟩, idx := B.minorindex ⟨0, hv⟩ }
      have hFmem : F ∈ (YoungBitableau.toMinorWord B).factors := by
        rw [YoungBitableau.toMinorWord]
        exact (List.mem_ofFn' _ F).mpr ⟨⟨0, hv⟩, rfl⟩
      have hle : F.t ≤ MinorWord.length (YoungBitableau.toMinorWord B) :=
        MinorWord.length_le_of_mem_factor hFmem
      simpa [F, YoungBitableau.length_eq_size_zero B hv] using hle
    · have hv0 : B.v = 0 := by omega
      haveI : IsEmpty (Fin B.v) := by
        rw [hv0]
        infer_instance
      simp [YoungBitableau.toMinorWord, YoungBitableau.length]

lemma toPolynomial_eq_head_minorWord_mul_erased_tail
    {m n : ℕ} (k : Type*) [CommRing k]
    (B : YoungBitableau m n) (hv : 0 < B.v) :
    YoungBitableau.toPolynomial k B =
      MinorWord.toPolynomial k
        ⟨({ t := B.size ⟨0, hv⟩,
            idx := B.minorindex ⟨0, hv⟩ } : MinorFactor m n) ::
          (MinorWord.eraseUnits
            (YoungBitableau.toMinorWord (YoungBitableau.tail B hv))).factors⟩ := by
  rw [YoungBitableau.toPolynomial_eq_head_mul_tail k B hv]
  rw [← YoungBitableau.toMinorWord_toPolynomial
    k (YoungBitableau.tail B hv)]
  rw [← MinorWord.eraseUnits_toPolynomial
    (W := YoungBitableau.toMinorWord (YoungBitableau.tail B hv))]
  simp [MinorFactor.toPolynomial]

lemma degree_eq_head_minorWord_add_erased_tail
    {m n : ℕ} (B : YoungBitableau m n) (hv : 0 < B.v) :
    B.size ⟨0, hv⟩ +
        MinorWord.degree
          (MinorWord.eraseUnits
            (YoungBitableau.toMinorWord (YoungBitableau.tail B hv))) =
      YoungBitableau.degree B := by
  rw [YoungBitableau.degree_eq_head_add_tail B hv]
  rw [MinorWord.eraseUnits_degree]
  rw [YoungBitableau.toMinorWord_degree]

lemma length_eq_head_size {m n : ℕ}
    (B : YoungBitableau m n) (hv : 0 < B.v) :
    YoungBitableau.length B = B.size ⟨0, hv⟩ :=
  YoungBitableau.length_eq_size_zero B hv

end YoungBitableau

namespace MinorWord

noncomputable def toYoungBitableauOfPositivePairwise {m n : ℕ}
    (W : MinorWord m n)
    (hpos : ∀ F ∈ W.factors, 0 < F.t)
    (hpair : MinorWord.PairwisePairLE W) :
    YoungBitableau m n where
  v := W.factors.length
  size := fun a => (W.factors.get a).t
  size_pos := by
    intro a
    exact hpos (W.factors.get a) (List.get_mem W.factors a)
  minorindex := fun a => (W.factors.get a).idx
  shape_antitone := by
    intro a b hab
    by_cases hlt : a < b
    · have hpairList :
          W.factors.Pairwise fun F G => MinorIndex.PairLE F.idx G.idx := by
        simpa [MinorWord.PairwisePairLE] using hpair
      have hrel :
          MinorIndex.PairLE (W.factors.get a).idx (W.factors.get b).idx :=
        hpairList.rel_get_of_lt hlt
      exact MinorIndex.PairLE.size_le hrel
    · have hba : b ≤ a := le_of_not_gt hlt
      have habeq : a = b := le_antisymm hab hba
      subst habeq
      rfl

@[simp] lemma toYoungBitableauOfPositivePairwise_v {m n : ℕ}
    (W : MinorWord m n)
    (hpos : ∀ F ∈ W.factors, 0 < F.t)
    (hpair : MinorWord.PairwisePairLE W) :
    (W.toYoungBitableauOfPositivePairwise hpos hpair).v = W.factors.length := rfl

@[simp] lemma toYoungBitableauOfPositivePairwise_size {m n : ℕ}
    (W : MinorWord m n)
    (hpos : ∀ F ∈ W.factors, 0 < F.t)
    (hpair : MinorWord.PairwisePairLE W)
    (a : Fin (W.toYoungBitableauOfPositivePairwise hpos hpair).v) :
    (W.toYoungBitableauOfPositivePairwise hpos hpair).size a =
      (W.factors.get (Fin.cast (by simp) a)).t := by
  rfl

lemma toMinorWord_toYoungBitableauOfPositivePairwise {m n : ℕ}
    (W : MinorWord m n)
    (hpos : ∀ F ∈ W.factors, 0 < F.t)
    (hpair : MinorWord.PairwisePairLE W) :
    YoungBitableau.toMinorWord
      (W.toYoungBitableauOfPositivePairwise hpos hpair) = W := by
  cases W with
  | mk factors =>
      simp [YoungBitableau.toMinorWord,
        MinorWord.toYoungBitableauOfPositivePairwise]

end MinorWord

namespace StandardMinorWord

noncomputable def toYoungBitableauAfterEraseUnits {m n : ℕ}
    (S : StandardMinorWord m n) : StandardYoungBitableau m n :=
  let W : MinorWord m n := MinorWord.eraseUnits S.1
  let hpos : ∀ F ∈ W.factors, 0 < F.t := by
    intro F hF
    have hFne : F.t ≠ 0 := by
      have hF' : F ∈ S.1.factors ∧ F.t ≠ 0 := by
        simpa [W, MinorWord.eraseUnits] using hF
      exact hF'.2
    exact Nat.pos_of_ne_zero hFne
  let hpair : MinorWord.PairwisePairLE W := S.2.eraseUnits
  ⟨W.toYoungBitableauOfPositivePairwise hpos hpair,
    YoungBitableau.isStandard_of_adjacent_pairLE (by
      intro a b hnext
      have hab : a < b := by
        rw [Fin.lt_def]
        omega
      have hpairList :
          W.factors.Pairwise fun F G => MinorIndex.PairLE F.idx G.idx := by
        simpa [MinorWord.PairwisePairLE] using hpair
      exact hpairList.rel_get_of_lt hab)⟩

lemma toMinorWord_toYoungBitableauAfterEraseUnits {m n : ℕ}
    (S : StandardMinorWord m n) :
    YoungBitableau.toMinorWord (S.toYoungBitableauAfterEraseUnits.1) =
      MinorWord.eraseUnits S.1 := by
  classical
  let W : MinorWord m n := MinorWord.eraseUnits S.1
  let hpos : ∀ F ∈ W.factors, 0 < F.t := by
    intro F hF
    have hFne : F.t ≠ 0 := by
      have hF' : F ∈ S.1.factors ∧ F.t ≠ 0 := by
        simpa [W, MinorWord.eraseUnits] using hF
      exact hF'.2
    exact Nat.pos_of_ne_zero hFne
  let hpair : MinorWord.PairwisePairLE W := S.2.eraseUnits
  unfold toYoungBitableauAfterEraseUnits
  exact MinorWord.toMinorWord_toYoungBitableauOfPositivePairwise
    W hpos hpair

lemma toYoungBitableauAfterEraseUnits_toPolynomial {m n : ℕ}
    (k : Type*) [CommRing k] (S : StandardMinorWord m n) :
    YoungBitableau.toPolynomial k
        S.toYoungBitableauAfterEraseUnits.1 =
      MinorWord.toPolynomial k S.1 := by
  rw [← YoungBitableau.toMinorWord_toPolynomial
    k S.toYoungBitableauAfterEraseUnits.1]
  rw [toMinorWord_toYoungBitableauAfterEraseUnits]
  rw [MinorWord.eraseUnits_toPolynomial]

lemma toYoungBitableauAfterEraseUnits_degree {m n : ℕ}
    (S : StandardMinorWord m n) :
    YoungBitableau.degree S.toYoungBitableauAfterEraseUnits.1 =
      MinorWord.degree S.1 := by
  rw [← YoungBitableau.toMinorWord_degree
    S.toYoungBitableauAfterEraseUnits.1]
  rw [toMinorWord_toYoungBitableauAfterEraseUnits]
  rw [MinorWord.eraseUnits_degree]

lemma toYoungBitableauAfterEraseUnits_length {m n : ℕ}
    (S : StandardMinorWord m n) :
    YoungBitableau.length S.toYoungBitableauAfterEraseUnits.1 =
      MinorWord.length S.1 := by
  rw [← YoungBitableau.toMinorWord_length
    S.toYoungBitableauAfterEraseUnits.1]
  rw [toMinorWord_toYoungBitableauAfterEraseUnits]
  rw [MinorWord.eraseUnits_length_eq]

lemma length_le_toYoungBitableauAfterEraseUnits_length
    {m n : ℕ} (S : StandardMinorWord m n)
    {H : MinorFactor m n} (hHmem : H ∈ S.1.factors) (hH : 0 < H.t) :
    H.t ≤ YoungBitableau.length S.toYoungBitableauAfterEraseUnits.1 := by
  have hmemErase : H ∈ (MinorWord.eraseUnits S.1).factors := by
    simpa [MinorWord.eraseUnits, hH.ne'] using hHmem
  have hmemWord :
      H ∈ (YoungBitableau.toMinorWord
        S.toYoungBitableauAfterEraseUnits.1).factors := by
    simpa [toMinorWord_toYoungBitableauAfterEraseUnits S] using hmemErase
  have hle :
      H.t ≤ MinorWord.length
        (YoungBitableau.toMinorWord S.toYoungBitableauAfterEraseUnits.1) :=
    MinorWord.length_le_of_mem_factor hmemWord
  rwa [YoungBitableau.toMinorWord_length] at hle

end StandardMinorWord

lemma standardMinorWord_pushforward_toYoungBitableauAfterEraseUnits
    {m n : ℕ} (k : Type*) [Field k]
    (c : StandardMinorWord m n →₀ k) :
    ∃ cY : StandardYoungBitableau m n →₀ k,
      c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1) =
        cY.sum (fun S a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k S.1)
      ∧
      ∀ S : StandardYoungBitableau m n, cY S ≠ 0 →
        ∃ U : StandardMinorWord m n,
          c U ≠ 0 ∧ U.toYoungBitableauAfterEraseUnits = S := by
  classical
  let toY : StandardMinorWord m n → StandardYoungBitableau m n :=
    fun U => U.toYoungBitableauAfterEraseUnits
  let cY : StandardYoungBitableau m n →₀ k := Finsupp.mapDomain toY c
  refine ⟨cY, ?_, ?_⟩
  · change
      c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1) =
        (Finsupp.mapDomain toY c).sum (fun S a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k S.1)
    rw [Finsupp.sum_mapDomain_index]
    · apply Finsupp.sum_congr
      intro U a
      rw [StandardMinorWord.toYoungBitableauAfterEraseUnits_toPolynomial
        k U]
    · intro S
      simp
    · intro S a b
      simp [add_mul, MvPolynomial.C_add]
  · intro S hS
    have hSmem : S ∈ cY.support := by
      simpa [Finsupp.mem_support_iff] using hS
    have hSimage : S ∈ Finset.image toY c.support := by
      exact Finsupp.mapDomain_support hSmem
    rcases Finset.mem_image.mp hSimage with ⟨U, hUmem, hUS⟩
    refine ⟨U, ?_, hUS⟩
    simpa [Finsupp.mem_support_iff] using hUmem

/-- The paper's determinantal ideal `J_r`, generated by the `(r + 1) × (r + 1)` minors. -/
abbrev Jr (m n r : ℕ) (k : Type*) [CommRing k] :=
  detIdeal m n (r + 1) k

/-- The paper's set `G_{r+1}` of all `(r + 1) × (r + 1)` minors. -/
abbrev GrPlusOne (m n r : ℕ) (k : Type*) [CommRing k] :=
  minorSet k m n (r + 1)

/-- The paper's `init(G_{r+1})` under the anti-diagonal lexicographic order.

The paper records initial monomials without coefficients, so this is the ideal generated by the
anti-diagonal monomials of the `(r + 1) × (r + 1)` minors rather than by Lean's
coefficient-carrying `leadingTerm`.
-/
noncomputable abbrev initGrPlusOne (m n r : ℕ) (k : Type*) [CommRing k] :
    Ideal (MvPolynomial (Fin m × Fin n) k) :=
  Ideal.span
    (Set.range fun I : MinorIndex m n (r + 1) => antidiagMonomial k I)

lemma monomial_mem_initGrPlusOne_iff_exists_antidiagExp_le
    {m n r : ℕ}
    (k : Type*) [Field k]
    (E : (Fin m × Fin n) →₀ ℕ) :
    MvPolynomial.monomial E (1 : k) ∈ initGrPlusOne m n r k
      ↔ ∃ I : MinorIndex m n (r + 1), antidiagExp I ≤ E := by
  classical
  rw [initGrPlusOne]
  rw [show
      (Set.range fun I : MinorIndex m n (r + 1) => antidiagMonomial k I) =
        ((fun s => MvPolynomial.monomial s (1 : k)) ''
          (Set.range fun I : MinorIndex m n (r + 1) => antidiagExp I)) by
    ext p
    constructor
    · rintro ⟨I, rfl⟩
      exact ⟨antidiagExp I, ⟨I, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨I, rfl⟩, rfl⟩
      exact ⟨I, rfl⟩]
  rw [MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h
    have hE : E ∈ (MvPolynomial.monomial E (1 : k)).support := by
      simp
    rcases h E hE with ⟨s, ⟨I, hs⟩, hle⟩
    exact ⟨I, by simpa [← hs] using hle⟩
  · rintro ⟨I, hle⟩ xi hxi
    have hxiE : E = xi := by
      simpa using hxi
    subst xi
    exact ⟨antidiagExp I, ⟨I, rfl⟩, hle⟩

/-- The paper's determinantal ring `R_r = K[X] / J_r`. -/
abbrev Rr (m n r : ℕ) (k : Type*) [CommRing k] :=
  MvPolynomial (Fin m × Fin n) k ⧸ Jr m n r k

/-- The degree-`d` homogeneous component `(R_r)_d`. -/
noncomputable abbrev RrDegree (m n r : ℕ) (k : Type*) [Field k] (d : ℕ) :
    Submodule k (Rr m n r k) :=
  Submodule.map
    (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
    (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d)

/-- The determinantal ideal is homogeneous, giving the quotient its natural grading. -/
theorem detIdeal_isHomogeneous
    {m n : ℕ}
    (k : Type*) [CommRing k]
    (r : ℕ) :
    (Jr m n r k).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k) := by
  unfold Jr detIdeal
  refine Ideal.homogeneous_span _ _ ?_
  intro f hf
  rcases (MvPolynomial.mem_determinantalMinorFinset k).1 hf with ⟨I, hI⟩
  rw [← hI]
  exact ⟨r + 1, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact genericMinor_isHomogeneous k I⟩

end Determinantal
