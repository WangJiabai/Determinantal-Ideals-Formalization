/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.Basic

/-!
# Evaluation of generic minors

Compatibility layer for evaluating generic minors through the Mathlib-candidate `Matrix` API.
-/

namespace Determinantal

/-- The usual `t × t` minor of an actual matrix `A`. -/
noncomputable abbrev matrixMinor {S : Type*} [CommRing S]
    {m n t : ℕ} (A : Matrix (Fin m) (Fin n) S) (I : MinorIndex m n t) : S :=
  I.detSubmatrix A

section Eval

variable {m n t : ℕ}
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]

/-- Evaluate the coordinate ring of the generic `m × n` matrix at a concrete matrix `A`. -/
noncomputable abbrev evalMatrix (A : Matrix (Fin m) (Fin n) S) :
    MvPolynomial (Fin m × Fin n) k →ₐ[k] S :=
  MvPolynomial.aeval fun ij => A ij.1 ij.2

@[simp] lemma evalMatrix_X (A : Matrix (Fin m) (Fin n) S) (i : Fin m) (j : Fin n) :
    evalMatrix k A (MvPolynomial.X (i, j)) = A i j :=
  by
    simp [evalMatrix]

@[simp] lemma evalMatrix_genericMatrix_apply
    (A : Matrix (Fin m) (Fin n) S) (i : Fin m) (j : Fin n) :
    evalMatrix k A (genericMatrix m n k i j) = A i j :=
  by
    simp [evalMatrix, genericMatrix]

/-- Evaluating a generic minor gives the corresponding minor of the concrete matrix. -/
lemma evalMatrix_minor (A : Matrix (Fin m) (Fin n) S) (I : MinorIndex m n t) :
    evalMatrix k A (genericMinor k I) = matrixMinor A I :=
  by
    simpa [evalMatrix, genericMinor, matrixMinor] using
      Matrix.MinorIndex.eval_mvPolynomialMinor k A I

end Eval

end Determinantal
