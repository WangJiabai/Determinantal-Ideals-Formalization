/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.GroupTheory.Perm.Sign
import MyProject.Determinantalideals.Basic

/-!
# Sign lemmas and bridges for minors

This file contains two groups of lemmas.

* In `SignLemmas`, we record how determinants behave under row and column permutations,
  with the permutation sign coerced to the coefficient ring.
* In `MinorBridge`, we package the square submatrix of the generic matrix associated to a
  minor index, and identify the generic minor with its determinant.
-/

namespace Determinantal

section SignLemmas

variable {t : ℕ}
variable {α : Type*} [CommRing α]
variable {A : Matrix (Fin t) (Fin t) α}

/-- The sign of a permutation, coerced to the coefficient ring. -/
noncomputable def eps (σ : Equiv.Perm (Fin t)) : α :=
  (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : α)

@[simp] lemma eps_one :
    eps (α := α) (t := t) (1 : Equiv.Perm (Fin t)) = 1 := by
  simp [eps]

@[simp] lemma eps_mul_eps (σ τ : Equiv.Perm (Fin t)) :
    eps (σ * τ) = eps σ * eps (α := α)  τ := by
  simp [eps]

/-- Permuting the rows of a square matrix multiplies the determinant by the sign. -/
lemma det_submatrix_rows_perm (σ : Equiv.Perm (Fin t)) :
    (A.submatrix σ id).det = eps σ * A.det := by
  simpa [eps] using (Matrix.det_permute A (σ := σ))

/-- Permuting the columns of a square matrix multiplies the determinant by the sign. -/
lemma det_submatrix_cols_perm (σ : Equiv.Perm (Fin t)) :
    (A.submatrix id σ).det = eps σ * A.det := by
  simpa [eps] using (Matrix.det_permute' A (σ := σ))

/-- Permuting both rows and columns multiplies the determinant by the product of the signs. -/
lemma det_submatrix_rows_cols_perm (σ τ : Equiv.Perm (Fin t)) :
    (A.submatrix σ τ).det = eps σ * eps τ * A.det := by
  calc
    (A.submatrix σ τ).det
        = ((A.submatrix σ id).submatrix id τ).det := rfl
    _ = eps τ * (A.submatrix σ id).det := by
        simpa using
          (det_submatrix_cols_perm
            (A := A.submatrix σ id) τ)
    _ = eps τ * (eps σ * A.det) := by
        rw [det_submatrix_rows_perm σ]
    _ = eps σ * eps τ * A.det := by
        simp [mul_assoc, mul_left_comm]

end SignLemmas

section MinorBridge

variable {m n t : ℕ}
variable {k : Type*} [CommRing k]

/-- The square submatrix of the generic matrix corresponding to a minor index. -/
noncomputable def minorMatrix (I : MinorIndex m n t) :
    Matrix (Fin t) (Fin t) (MvPolynomial (Fin m × Fin n) k) :=
  Matrix.submatrix (genericMatrix (m := m) (n := n) k) I.row I.col

@[simp] lemma minorMatrix_apply (I : MinorIndex m n t) (i j : Fin t) :
    minorMatrix (m := m) (n := n) (k := k) I i j =
      MvPolynomial.X (I.row i, I.col j) := by
  rfl

@[simp] lemma minor_eq_det_minorMatrix (I : MinorIndex m n t) :
    genericMinor (k := k) I = (minorMatrix I).det := by
  rfl

end MinorBridge

end Determinantal
