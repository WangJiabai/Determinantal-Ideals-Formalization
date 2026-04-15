/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Hom.Basic

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

end Determinantal
