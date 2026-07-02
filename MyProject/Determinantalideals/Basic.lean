/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.DeterminantalIdeal
import Mathlib.Data.Finset.Sort
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Compatibility layer for determinantal ideals

This file keeps the original `Determinantal` API available while the first-PR Mathlib candidate
keeps only the basic generic-minor and determinantal-ideal API.
-/

namespace Determinantal

/-- Compatibility alias for `Matrix.mvPolynomialX`. -/
noncomputable abbrev genericMatrix (m n : ℕ) (k : Type*) [CommSemiring k] :
    Matrix (Fin m) (Fin n) (MvPolynomial (Fin m × Fin n) k) :=
  Matrix.mvPolynomialX (Fin m) (Fin n) k

@[simp] lemma genericMatrix_apply {m n : ℕ} (i : Fin m) (j : Fin n)
    (k : Type*) [CommSemiring k] :
    genericMatrix m n k i j = MvPolynomial.X (i, j) := rfl

/-- Compatibility alias for `Matrix.MinorIndex`. -/
abbrev MinorIndex (m n t : ℕ) := Matrix.MinorIndex m n t

section CommRing

/-- Compatibility alias for `Matrix.MinorIndex.mvPolynomialMinor`. -/
noncomputable abbrev genericMinor (k : Type*) [CommRing k] {m n t : ℕ}
    (I : MinorIndex m n t) :
    MvPolynomial (Fin m × Fin n) k :=
  I.mvPolynomialMinor k

@[simp] lemma genericMinor_zero (k : Type*) [CommRing k] {m n : ℕ}
    (I : MinorIndex m n 0) :
    genericMinor k I = 1 :=
  Matrix.MinorIndex.mvPolynomialMinor_zero k I

@[simp] lemma genericMinor_one (k : Type*) [CommRing k] {m n : ℕ}
    (I : MinorIndex m n 1) :
    genericMinor k I = MvPolynomial.X (I.row 0, I.col 0) :=
  Matrix.MinorIndex.mvPolynomialMinor_one k I

/-- Compatibility set of all generic `t × t` minors. -/
abbrev minorSet (k : Type*) [CommRing k] (m n t : ℕ) :
    Set (MvPolynomial (Fin m × Fin n) k) :=
  Set.range (fun I : MinorIndex m n t => genericMinor k I)

@[simp] lemma mem_minorSet_iff (k : Type*) [CommRing k] {m n t : ℕ}
    {f : MvPolynomial (Fin m × Fin n) k} :
    f ∈ minorSet k m n t ↔ ∃ I : MinorIndex m n t, genericMinor k I = f :=
  Iff.rfl

lemma minor_mem_minorSet (k : Type*) [CommRing k] {m n t : ℕ}
    (I : MinorIndex m n t) :
    genericMinor k I ∈ minorSet k m n t :=
  ⟨I, rfl⟩

lemma mem_minorSet_one_iff (k : Type*) [CommRing k] {m n : ℕ}
    {f : MvPolynomial (Fin m × Fin n) k} :
    f ∈ minorSet k m n 1
      ↔ ∃ i : Fin m, ∃ j : Fin n, f = MvPolynomial.X (i, j) := by
  constructor
  · rintro ⟨I, hI⟩
    refine ⟨I.row 0, I.col 0, ?_⟩
    rw [← hI]
    change genericMinor k I = MvPolynomial.X (I.row 0, I.col 0)
    rw [genericMinor_one k]
  · rintro ⟨i, j, rfl⟩
    let row : Fin 1 ↪o Fin m := OrderEmbedding.ofStrictMono
      (fun _ => i)
      (by
        intro a b h
        have hnot : ¬ a < b := by
          rw [Fin.eq_zero a, Fin.eq_zero b]
          exact lt_irrefl 0
        exact False.elim (hnot h))
    let col : Fin 1 ↪o Fin n := OrderEmbedding.ofStrictMono
      (fun _ => j)
      (by
        intro a b h
        have hnot : ¬ a < b := by
          rw [Fin.eq_zero a, Fin.eq_zero b]
          exact lt_irrefl 0
        exact False.elim (hnot h))
    refine ⟨⟨row, col⟩, ?_⟩
    change genericMinor k (⟨row, col⟩ : MinorIndex m n 1) =
      MvPolynomial.X (i, j)
    rw [genericMinor_one k]
    rfl

end CommRing

namespace MinorIndex

abbrev row {m n t : ℕ} (I : MinorIndex m n t) : Fin t ↪o Fin m :=
  Matrix.MinorIndex.row I

abbrev col {m n t : ℕ} (I : MinorIndex m n t) : Fin t ↪o Fin n :=
  Matrix.MinorIndex.col I

@[simp] lemma row_mk {m n t : ℕ}
    (row : Fin t ↪o Fin m) (col : Fin t ↪o Fin n) :
    MinorIndex.row ({ row := row, col := col } : MinorIndex m n t) = row :=
  rfl

@[simp] lemma col_mk {m n t : ℕ}
    (row : Fin t ↪o Fin m) (col : Fin t ↪o Fin n) :
    MinorIndex.col ({ row := row, col := col } : MinorIndex m n t) = col :=
  rfl

@[ext] theorem ext {m n t : ℕ} {I J : MinorIndex m n t}
    (hrow : ∀ a, I.row a = J.row a)
    (hcol : ∀ a, I.col a = J.col a) :
    I = J :=
  Matrix.MinorIndex.ext hrow hcol

/-- Delete one selected row and one selected column from a minor index. -/
def delete {m n s : ℕ}
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

/-- Row-index content of a minor: the multiplicity vector of its selected rows. -/
noncomputable def rowContent {m n t : ℕ} (I : MinorIndex m n t) : Fin m →₀ ℕ :=
  ∑ a : Fin t, Finsupp.single (I.row a) 1

/-- Column-index content of a minor: the multiplicity vector of its selected columns. -/
noncomputable def colContent {m n t : ℕ} (I : MinorIndex m n t) : Fin n →₀ ℕ :=
  ∑ a : Fin t, Finsupp.single (I.col a) 1

/-- Total row-content multiplicity of a `t × t` minor is `t`. -/
lemma rowContent_total {m n t : ℕ} (I : MinorIndex m n t) :
    (∑ i : Fin m, I.rowContent i) = t := by
  classical
  simp only [rowContent, Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

/-- Total column-content multiplicity of a `t × t` minor is `t`. -/
lemma colContent_total {m n t : ℕ} (I : MinorIndex m n t) :
    (∑ j : Fin n, I.colContent j) = t := by
  classical
  simp only [colContent, Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

lemma mem_rowContent_support_iff {m n t : ℕ}
    (I : MinorIndex m n t) (a : Fin m) :
    a ∈ I.rowContent.support ↔ ∃ i : Fin t, I.row i = a := by
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
    a ∈ I.colContent.support ↔ ∃ i : Fin t, I.col i = a := by
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
    I.rowContent.support = Finset.univ.map I.row.toEmbedding := by
  classical
  ext a
  rw [mem_rowContent_support_iff]
  simp

lemma colContent_support_eq_image {m n t : ℕ}
    (I : MinorIndex m n t) :
    I.colContent.support = Finset.univ.map I.col.toEmbedding := by
  classical
  ext a
  rw [mem_colContent_support_iff]
  simp

lemma row_eq_of_rowContent_eq {m n t : ℕ}
    {I J : MinorIndex m n t}
    (hrow : I.rowContent = J.rowContent) :
    I.row = J.row := by
  classical
  have hrowSet :
      Finset.univ.map I.row.toEmbedding =
        Finset.univ.map J.row.toEmbedding := by
    rw [← I.rowContent_support_eq_image, ← J.rowContent_support_eq_image, hrow]
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
    rw [← I.colContent_support_eq_image, ← J.colContent_support_eq_image, hcol]
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
  apply ext
  · intro a
    rw [row_eq_of_rowContent_eq hrow]
  · intro a
    rw [col_eq_of_colContent_eq hcol]

end MinorIndex

section ExtraMinorLemmas

lemma genericMinor_delete_eq_det_submatrix (k : Type*) [CommRing k] {m n s : ℕ}
    (I : MinorIndex m n (s + 1)) (i j : Fin (s + 1)) :
    genericMinor k (I.delete i j) =
      Matrix.det
        (((Matrix.submatrix (genericMatrix m n k) I.row I.col).submatrix
          i.succAbove j.succAbove)) := by
  simp [genericMinor, Matrix.MinorIndex.mvPolynomialMinor, Matrix.MinorIndex.detSubmatrix,
    MinorIndex.delete, genericMatrix, Matrix.submatrix_submatrix, Function.comp_def]

/-- A generic minor of size `t` is homogeneous of degree `t`. -/
lemma genericMinor_isHomogeneous (k : Type*) [CommRing k] {m n t : ℕ}
    (I : MinorIndex m n t) :
    (genericMinor k I).IsHomogeneous t := by
  rw [genericMinor, Matrix.MinorIndex.mvPolynomialMinor, Matrix.MinorIndex.detSubmatrix,
    Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  have hprod :
      (∏ i,
        Matrix.submatrix (genericMatrix m n k) I.row I.col (σ i) i).IsHomogeneous t := by
    convert MvPolynomial.IsHomogeneous.prod
        (Finset.univ : Finset (Fin t))
        (fun i => Matrix.submatrix (genericMatrix m n k) I.row I.col (σ i) i)
        (fun _ => 1)
        ?_ using 1
    · simp
    · intro i _hi
      simpa [genericMatrix] using
        MvPolynomial.isHomogeneous_X (R := k) (I.row (σ i), I.col i)
  exact hprod.C_mul _

lemma genericMinor_eq_sum_delete_row_zero (k : Type*) [CommRing k] {m n s : ℕ}
    (I : MinorIndex m n (s + 1)) :
    genericMinor k I =
      ∑ j : Fin (s + 1),
        (-1 : MvPolynomial (Fin m × Fin n) k) ^ (j : ℕ) *
          MvPolynomial.X (I.row 0, I.col j) *
            genericMinor k (I.delete 0 j) := by
  rw [genericMinor, Matrix.MinorIndex.mvPolynomialMinor, Matrix.MinorIndex.detSubmatrix,
    Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [genericMinor_delete_eq_det_submatrix k]
  simp [Matrix.submatrix_apply, genericMatrix]

lemma genericMinor_eq_sum_delete_col_zero (k : Type*) [CommRing k] {m n s : ℕ}
    (I : MinorIndex m n (s + 1)) :
    genericMinor k I =
      ∑ i : Fin (s + 1),
        (-1 : MvPolynomial (Fin m × Fin n) k) ^ (i : ℕ) *
          MvPolynomial.X (I.row i, I.col 0) *
            genericMinor k (I.delete i 0) := by
  rw [genericMinor, Matrix.MinorIndex.mvPolynomialMinor, Matrix.MinorIndex.detSubmatrix,
    Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [genericMinor_delete_eq_det_submatrix k]
  simp [Matrix.submatrix_apply, genericMatrix]

lemma genericMinor_mul_eq_sum_delete_row_zero_left (k : Type*) [CommRing k] {m n s t : ℕ}
    (I : MinorIndex m n (s + 1)) (J : MinorIndex m n t) :
    genericMinor k I * genericMinor k J =
      ∑ j : Fin (s + 1),
        ((-1 : MvPolynomial (Fin m × Fin n) k) ^ (j : ℕ) *
          MvPolynomial.X (I.row 0, I.col j) *
            genericMinor k (I.delete 0 j)) *
          genericMinor k J := by
  rw [genericMinor_eq_sum_delete_row_zero k I, Finset.sum_mul]

lemma genericMinor_mul_eq_sum_delete_row_zero_right (k : Type*) [CommRing k] {m n s t : ℕ}
    (I : MinorIndex m n t) (J : MinorIndex m n (s + 1)) :
    genericMinor k I * genericMinor k J =
      ∑ j : Fin (s + 1),
        genericMinor k I *
          ((-1 : MvPolynomial (Fin m × Fin n) k) ^ (j : ℕ) *
            MvPolynomial.X (J.row 0, J.col j) *
              genericMinor k (J.delete 0 j)) := by
  rw [genericMinor_eq_sum_delete_row_zero k J, Finset.mul_sum]

lemma genericMinor_mul_eq_sum_delete_col_zero_left (k : Type*) [CommRing k] {m n s t : ℕ}
    (I : MinorIndex m n (s + 1)) (J : MinorIndex m n t) :
    genericMinor k I * genericMinor k J =
      ∑ i : Fin (s + 1),
        ((-1 : MvPolynomial (Fin m × Fin n) k) ^ (i : ℕ) *
          MvPolynomial.X (I.row i, I.col 0) *
            genericMinor k (I.delete i 0)) *
          genericMinor k J := by
  rw [genericMinor_eq_sum_delete_col_zero k I, Finset.sum_mul]

lemma genericMinor_mul_eq_sum_delete_col_zero_right (k : Type*) [CommRing k] {m n s t : ℕ}
    (I : MinorIndex m n t) (J : MinorIndex m n (s + 1)) :
    genericMinor k I * genericMinor k J =
      ∑ i : Fin (s + 1),
        genericMinor k I *
          ((-1 : MvPolynomial (Fin m × Fin n) k) ^ (i : ℕ) *
            MvPolynomial.X (J.row i, J.col 0) *
              genericMinor k (J.delete i 0)) := by
  rw [genericMinor_eq_sum_delete_col_zero k J, Finset.mul_sum]

end ExtraMinorLemmas

end Determinantal
