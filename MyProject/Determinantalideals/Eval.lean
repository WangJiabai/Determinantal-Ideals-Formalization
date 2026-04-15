/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.Algebra.MvPolynomial.Eval
import MyProject.Determinantalideals.Basic

/-!
# Evaluation of generic minors

This file defines the evaluation map from the coordinate ring of the generic `m × n` matrix
to a concrete matrix over a `k`-algebra, and proves that evaluating a generic minor gives the
corresponding minor of the concrete matrix.
-/

namespace Determinantal

/-- The usual `t × t` minor of an actual matrix `A`. -/
noncomputable def matrixMinor {S : Type*} [CommRing S]
    {m n t : ℕ} (A : Matrix (Fin m) (Fin n) S) (I : MinorIndex m n t) : S :=
  Matrix.det <| Matrix.submatrix A I.row I.col

section Eval

variable {m n t : ℕ}
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]

/-- Evaluate the coordinate ring of the generic `m × n` matrix at a concrete matrix `A`. -/
noncomputable def evalMatrix (A : Matrix (Fin m) (Fin n) S) :
    MvPolynomial (Fin m × Fin n) k →ₐ[k] S :=
  MvPolynomial.aeval fun ij => A ij.1 ij.2

@[simp] lemma evalMatrix_X (A : Matrix (Fin m) (Fin n) S) (i : Fin m) (j : Fin n) :
    evalMatrix k A (MvPolynomial.X (i, j)) = A i j := by
  simp [evalMatrix]

@[simp] lemma evalMatrix_genericMatrix_apply
    (A : Matrix (Fin m) (Fin n) S) (i : Fin m) (j : Fin n) :
    evalMatrix k A (genericMatrix m n k i j) = A i j := by
  simp [genericMatrix, evalMatrix]

/-- Evaluating a generic minor gives the corresponding minor of the concrete matrix. -/
lemma evalMatrix_minor (A : Matrix (Fin m) (Fin n) S) (I : MinorIndex m n t) :
    evalMatrix k A (genericMinor I) = matrixMinor A I := by
  classical
  let M : Matrix (Fin t) (Fin t) (MvPolynomial (Fin m × Fin n) k) :=
    Matrix.submatrix (genericMatrix m n k) I.row I.col
  have hdet := (AlgHom.map_det (evalMatrix k A) M).symm
  have hM : M.map (evalMatrix k A) = Matrix.submatrix A I.row I.col := by
    ext i j
    simp [M, evalMatrix, genericMatrix]
  simpa [genericMinor, matrixMinor, M, hM] using hdet.symm

end Eval

end Determinantal
