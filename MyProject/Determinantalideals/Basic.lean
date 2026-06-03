/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Basic definitions for determinantal ideals

This file defines the coordinate ring of a generic `m × n` matrix, the generic matrix itself,
indexing data for `t × t` minors, the corresponding minors, and the set of all such minors.
-/

namespace Determinantal

/-- The generic `m × n` matrix whose `(i,j)` entry is the variable `X (i,j)`. -/
noncomputable def genericMatrix (m n : ℕ) (k : Type*) [CommSemiring k] :
    Matrix (Fin m) (Fin n) (MvPolynomial (Fin m × Fin n) k) :=
  fun i j => MvPolynomial.X (i, j)

@[simp] lemma genericMatrix_apply {m n : ℕ} (i : Fin m) (j : Fin n)
    (k : Type*) [CommSemiring k] :
    genericMatrix m n k i j = MvPolynomial.X (i, j) := rfl

section CommRing

variable {k : Type*} [CommRing k]

/-- Index data for a `t × t` minor of an `m × n` matrix.

The row and column choices are encoded as order embeddings, so the selected indices are listed
in strictly increasing order. -/
structure MinorIndex (m n t : ℕ) where
  /-- The chosen row indices, in increasing order. -/
  row : Fin t ↪o Fin m
  /-- The chosen column indices, in increasing order. -/
  col : Fin t ↪o Fin n

/-- `genericMinor I` is the `t × t` minor of the generic `m × n` matrix selected by
the row/column order embeddings stored in `I : MinorIndex m n t`. -/
noncomputable def genericMinor {m n t : ℕ} (I : MinorIndex m n t) :
    MvPolynomial (Fin m × Fin n) k :=
  Matrix.det <| Matrix.submatrix (genericMatrix m n k) I.row I.col

@[simp] lemma genericMinor_zero {m n : ℕ} (I : MinorIndex m n 0) :
    genericMinor (k := k) I = 1 := by
  rw [genericMinor, Matrix.det_isEmpty]

@[simp] lemma genericMinor_one {m n : ℕ} (I : MinorIndex m n 1) :
    genericMinor (k := k) I = MvPolynomial.X (I.row 0, I.col 0) := by
  rw [genericMinor, Matrix.det_fin_one]
  rfl

/-- Delete one selected row and one selected column from a minor index. -/
def MinorIndex.delete {m n s : ℕ}
    (I : MinorIndex m n (s + 1)) (i j : Fin (s + 1)) :
    MinorIndex m n s where
  row := OrderEmbedding.ofStrictMono
    (fun a : Fin s => I.row (i.succAbove a))
    (by
      intro a b h
      exact I.row.strictMono ((Fin.strictMono_succAbove i) h))
  col := OrderEmbedding.ofStrictMono
    (fun a : Fin s => I.col (j.succAbove a))
    (by
      intro a b h
      exact I.col.strictMono ((Fin.strictMono_succAbove j) h))

lemma genericMinor_delete_eq_det_submatrix {m n s : ℕ}
    (I : MinorIndex m n (s + 1)) (i j : Fin (s + 1)) :
    genericMinor (k := k) (I.delete i j) =
      Matrix.det
        (((Matrix.submatrix (genericMatrix m n k) I.row I.col).submatrix
          i.succAbove j.succAbove)) := by
  simp [genericMinor, MinorIndex.delete, Matrix.submatrix_submatrix, Function.comp_def]

/-- A generic minor of size `t` is homogeneous of degree `t`. -/
lemma genericMinor_isHomogeneous
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    (genericMinor (k := k) I).IsHomogeneous t := by
  rw [genericMinor, Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  have hprod :
      (∏ i, Matrix.submatrix (genericMatrix m n k) I.row I.col (σ i) i).IsHomogeneous t := by
    convert MvPolynomial.IsHomogeneous.prod
        (Finset.univ : Finset (Fin t))
        (fun i => Matrix.submatrix (genericMatrix m n k) I.row I.col (σ i) i)
        (fun _ => 1)
        ?_ using 1
    · simp
    · intro i hi
      simp [Matrix.submatrix_apply, genericMatrix_apply, MvPolynomial.isHomogeneous_X]
  simpa only [zero_add] using (MvPolynomial.isHomogeneous_C _ _).mul hprod

/-- The set of all `t × t` minors of the generic `m × n` matrix. -/
def minorSet {m n : ℕ} (t : ℕ) : Set (MvPolynomial (Fin m × Fin n) k) :=
  Set.range (genericMinor (t := t))

@[simp] lemma mem_minorSet_iff {m n t : ℕ} {f : MvPolynomial (Fin m × Fin n) k} :
    f ∈ minorSet t ↔ ∃ I : MinorIndex m n t, genericMinor I = f := Iff.rfl

lemma minor_mem_minorSet {m n t : ℕ} (I : MinorIndex m n t) :
    genericMinor I ∈ minorSet (k := k) t := ⟨I, rfl⟩

lemma mem_minorSet_one_iff {m n : ℕ}
    {f : MvPolynomial (Fin m × Fin n) k} :
    f ∈ minorSet (k := k) (m := m) (n := n) 1
      ↔ ∃ i : Fin m, ∃ j : Fin n, f = MvPolynomial.X (i, j) := by
  constructor
  · rintro ⟨I, hI⟩
    refine ⟨I.row 0, I.col 0, ?_⟩
    calc
      f = genericMinor (k := k) I := hI.symm
      _ = MvPolynomial.X (I.row 0, I.col 0) := by rw [genericMinor_one]
  · rintro ⟨i, j, rfl⟩
    let row : Fin 1 ↪o Fin m :=
      OrderEmbedding.ofStrictMono (fun _ : Fin 1 => i) (by
        intro a b h
        have hnot : ¬ a < b := by
          rw [Fin.eq_zero a, Fin.eq_zero b]
          exact lt_irrefl 0
        exact False.elim (hnot h))
    let col : Fin 1 ↪o Fin n :=
      OrderEmbedding.ofStrictMono (fun _ : Fin 1 => j) (by
        intro a b h
        have hnot : ¬ a < b := by
          rw [Fin.eq_zero a, Fin.eq_zero b]
          exact lt_irrefl 0
        exact False.elim (hnot h))
    refine ⟨⟨row, col⟩, ?_⟩
    rw [genericMinor_one]
    rfl

end CommRing

namespace MinorIndex

@[ext] theorem ext {m n t : ℕ} {I J : MinorIndex m n t}
    (hrow : ∀ a, I.row a = J.row a)
    (hcol : ∀ a, I.col a = J.col a) :
    I = J := by
  cases I
  cases J
  congr
  · ext a
    exact congrArg Fin.val (hrow a)
  · ext a
    exact congrArg Fin.val (hcol a)

lemma genericMinor_eq_sum_delete_row_zero {m n s : ℕ}
    {k : Type*} [CommRing k]
    (I : MinorIndex m n (s + 1)) :
    genericMinor (k := k) I =
      ∑ j : Fin (s + 1),
        (-1 : MvPolynomial (Fin m × Fin n) k) ^ (j : ℕ) *
          MvPolynomial.X (I.row 0, I.col j) *
            genericMinor (k := k) (I.delete 0 j) := by
  rw [genericMinor, Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [genericMinor_delete_eq_det_submatrix]
  simp [Matrix.submatrix_apply, genericMatrix]

lemma genericMinor_eq_sum_delete_col_zero {m n s : ℕ}
    {k : Type*} [CommRing k]
    (I : MinorIndex m n (s + 1)) :
    genericMinor (k := k) I =
      ∑ i : Fin (s + 1),
        (-1 : MvPolynomial (Fin m × Fin n) k) ^ (i : ℕ) *
          MvPolynomial.X (I.row i, I.col 0) *
            genericMinor (k := k) (I.delete i 0) := by
  rw [genericMinor, Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [genericMinor_delete_eq_det_submatrix]
  simp [Matrix.submatrix_apply, genericMatrix]

lemma genericMinor_mul_eq_sum_delete_row_zero_left {m n s t : ℕ}
    {k : Type*} [CommRing k]
    (I : MinorIndex m n (s + 1)) (J : MinorIndex m n t) :
    genericMinor (k := k) I * genericMinor (k := k) J =
      ∑ j : Fin (s + 1),
        ((-1 : MvPolynomial (Fin m × Fin n) k) ^ (j : ℕ) *
          MvPolynomial.X (I.row 0, I.col j) *
            genericMinor (k := k) (I.delete 0 j)) *
          genericMinor (k := k) J := by
  rw [genericMinor_eq_sum_delete_row_zero I, Finset.sum_mul]

lemma genericMinor_mul_eq_sum_delete_row_zero_right {m n s t : ℕ}
    {k : Type*} [CommRing k]
    (I : MinorIndex m n t) (J : MinorIndex m n (s + 1)) :
    genericMinor (k := k) I * genericMinor (k := k) J =
      ∑ j : Fin (s + 1),
        genericMinor (k := k) I *
          ((-1 : MvPolynomial (Fin m × Fin n) k) ^ (j : ℕ) *
            MvPolynomial.X (J.row 0, J.col j) *
              genericMinor (k := k) (J.delete 0 j)) := by
  rw [genericMinor_eq_sum_delete_row_zero J, Finset.mul_sum]

lemma genericMinor_mul_eq_sum_delete_col_zero_left {m n s t : ℕ}
    {k : Type*} [CommRing k]
    (I : MinorIndex m n (s + 1)) (J : MinorIndex m n t) :
    genericMinor (k := k) I * genericMinor (k := k) J =
      ∑ i : Fin (s + 1),
        ((-1 : MvPolynomial (Fin m × Fin n) k) ^ (i : ℕ) *
          MvPolynomial.X (I.row i, I.col 0) *
            genericMinor (k := k) (I.delete i 0)) *
          genericMinor (k := k) J := by
  rw [genericMinor_eq_sum_delete_col_zero I, Finset.sum_mul]

lemma genericMinor_mul_eq_sum_delete_col_zero_right {m n s t : ℕ}
    {k : Type*} [CommRing k]
    (I : MinorIndex m n t) (J : MinorIndex m n (s + 1)) :
    genericMinor (k := k) I * genericMinor (k := k) J =
      ∑ i : Fin (s + 1),
        genericMinor (k := k) I *
          ((-1 : MvPolynomial (Fin m × Fin n) k) ^ (i : ℕ) *
            MvPolynomial.X (J.row i, J.col 0) *
              genericMinor (k := k) (J.delete i 0)) := by
  rw [genericMinor_eq_sum_delete_col_zero J, Finset.mul_sum]

/-- Row-index content of a minor: the multiplicity vector of its selected rows. -/
noncomputable def rowContent {m n t : ℕ} (I : MinorIndex m n t) : Fin m →₀ ℕ :=
  ∑ a : Fin t, Finsupp.single (I.row a) 1

/-- Total row-content multiplicity of a `t × t` minor is `t`. -/
lemma rowContent_total {m n t : ℕ} (I : MinorIndex m n t) :
    (∑ i : Fin m, MinorIndex.rowContent I i) = t := by
  classical
  simp only [rowContent, Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

/-- Column-index content of a minor: the multiplicity vector of its selected columns. -/
noncomputable def colContent {m n t : ℕ} (I : MinorIndex m n t) : Fin n →₀ ℕ :=
  ∑ a : Fin t, Finsupp.single (I.col a) 1

/-- Total column-content multiplicity of a `t × t` minor is `t`. -/
lemma colContent_total {m n t : ℕ} (I : MinorIndex m n t) :
    (∑ j : Fin n, MinorIndex.colContent I j) = t := by
  classical
  simp only [colContent, Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

lemma mem_rowContent_support_iff {m n t : ℕ}
    (I : MinorIndex m n t) (a : Fin m) :
    a ∈ (MinorIndex.rowContent I).support ↔ ∃ i : Fin t, I.row i = a := by
  classical
  simp only [rowContent, Finsupp.mem_support_iff, Finsupp.coe_finset_sum, Finset.sum_apply,
    ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const, not_forall]
  constructor
  · rintro ⟨i, hi⟩
    by_contra h
    have hne : I.row i ≠ a := by
      intro hia
      exact h ⟨i, hia⟩
    simp [hne] at hi
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp⟩

lemma mem_colContent_support_iff {m n t : ℕ}
    (I : MinorIndex m n t) (a : Fin n) :
    a ∈ (MinorIndex.colContent I).support ↔ ∃ i : Fin t, I.col i = a := by
  classical
  simp only [colContent, Finsupp.mem_support_iff, Finsupp.coe_finset_sum, Finset.sum_apply,
    ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const, not_forall]
  constructor
  · rintro ⟨i, hi⟩
    by_contra h
    have hne : I.col i ≠ a := by
      intro hia
      exact h ⟨i, hia⟩
    simp [hne] at hi
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp⟩

lemma rowContent_support_eq_image {m n t : ℕ}
    (I : MinorIndex m n t) :
    (MinorIndex.rowContent I).support =
      Finset.univ.map I.row.toEmbedding := by
  classical
  ext a
  rw [MinorIndex.mem_rowContent_support_iff]
  simp

lemma colContent_support_eq_image {m n t : ℕ}
    (I : MinorIndex m n t) :
    (MinorIndex.colContent I).support =
      Finset.univ.map I.col.toEmbedding := by
  classical
  ext a
  rw [MinorIndex.mem_colContent_support_iff]
  simp

lemma row_eq_of_rowContent_eq {m n t : ℕ}
    {I J : MinorIndex m n t}
    (hrow : I.rowContent = J.rowContent) :
    I.row = J.row := by
  classical
  have hrowSet :
      Finset.univ.map I.row.toEmbedding =
        Finset.univ.map J.row.toEmbedding := by
    rw [← I.rowContent_support_eq_image,
      ← J.rowContent_support_eq_image, hrow]
  have hIcard :
      (Finset.univ.map I.row.toEmbedding).card = t := by simp
  have hImem :
      ∀ i : Fin t, I.row i ∈ Finset.univ.map I.row.toEmbedding := by
    intro i
    simp
  have hJmem :
      ∀ i : Fin t, J.row i ∈ Finset.univ.map I.row.toEmbedding := by
    intro i
    rw [hrowSet]
    simp
  have hI :
      (fun i => I.row i) =
        fun i => (Finset.univ.map I.row.toEmbedding).orderEmbOfFin hIcard i :=
    Finset.orderEmbOfFin_unique
      (s := Finset.univ.map I.row.toEmbedding)
      (h := hIcard) hImem I.row.strictMono
  have hJ :
      (fun i => J.row i) =
        fun i => (Finset.univ.map I.row.toEmbedding).orderEmbOfFin hIcard i :=
    Finset.orderEmbOfFin_unique
      (s := Finset.univ.map I.row.toEmbedding)
      (h := hIcard) hJmem J.row.strictMono
  ext i
  exact congrArg Fin.val (congrFun (hI.trans hJ.symm) i)

lemma col_eq_of_colContent_eq {m n t : ℕ}
    {I J : MinorIndex m n t}
    (hcol : I.colContent = J.colContent) :
    I.col = J.col := by
  classical
  have hcolSet :
      Finset.univ.map I.col.toEmbedding =
        Finset.univ.map J.col.toEmbedding := by
    rw [← I.colContent_support_eq_image,
      ← J.colContent_support_eq_image, hcol]
  have hIcard :
      (Finset.univ.map I.col.toEmbedding).card = t := by simp
  have hImem :
      ∀ i : Fin t, I.col i ∈ Finset.univ.map I.col.toEmbedding := by
    intro i
    simp
  have hJmem :
      ∀ i : Fin t, J.col i ∈ Finset.univ.map I.col.toEmbedding := by
    intro i
    rw [hcolSet]
    simp
  have hI :
      (fun i => I.col i) =
        fun i => (Finset.univ.map I.col.toEmbedding).orderEmbOfFin hIcard i :=
    Finset.orderEmbOfFin_unique
      (s := Finset.univ.map I.col.toEmbedding)
      (h := hIcard) hImem I.col.strictMono
  have hJ :
      (fun i => J.col i) =
        fun i => (Finset.univ.map I.col.toEmbedding).orderEmbOfFin hIcard i :=
    Finset.orderEmbOfFin_unique
      (s := Finset.univ.map I.col.toEmbedding)
      (h := hIcard) hJmem J.col.strictMono
  ext a
  exact congrArg Fin.val (congrFun (hI.trans hJ.symm) a)

lemma eq_of_rowContent_eq_colContent {m n t : ℕ}
    {I J : MinorIndex m n t}
    (hrow : I.rowContent = J.rowContent)
    (hcol : I.colContent = J.colContent) :
    I = J := by
  apply MinorIndex.ext
  · intro a
    rw [row_eq_of_rowContent_eq hrow]
  · intro a
    rw [col_eq_of_colContent_eq hcol]

end MinorIndex

end Determinantal
