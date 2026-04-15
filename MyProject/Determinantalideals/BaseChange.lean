/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.RingTheory.Ideal.Maps
import MyProject.Determinantalideals.Basic
import MyProject.Determinantalideals.Ideal

/-!
# Base change for determinantal ideals

This file records the compatibility of the generic matrix, its minors, and the
determinantal ideal with a ring homomorphism on coefficients.
-/

namespace Determinantal

section BaseChange

variable {k : Type*} [CommRing k]
variable {S : Type*} [CommRing S]
variable {m n t : ℕ}

/-- Mapping coefficients along `f` sends the generic matrix over `k` to the generic matrix
over `S`. -/
lemma genericMatrix_map (f : k →+* S) :
    (genericMatrix m n k).map (MvPolynomial.map f) =
      genericMatrix m n S := by
  ext i j
  simp [genericMatrix]

/-- Mapping coefficients along `f` sends a generic minor over `k` to the corresponding
generic minor over `S`. -/
lemma map_minor (f : k →+* S) (I : MinorIndex m n t) :
    (MvPolynomial.map f) (genericMinor I) =
      genericMinor I := by
  classical
  unfold genericMinor
  have hdet :
      (MvPolynomial.map f) (Matrix.det (Matrix.submatrix (genericMatrix m n k) I.row I.col)) =
        Matrix.det ((Matrix.submatrix (genericMatrix m n k) I.row I.col).map
        (MvPolynomial.map f)) := by
    simpa using
      (RingHom.map_det (MvPolynomial.map f) (Matrix.submatrix (genericMatrix m n k) I.row I.col))
  simpa [Matrix.submatrix_map, ← genericMatrix_map f] using hdet

/-- Determinantal ideals are compatible with coefficient-wise base change. -/
lemma detIdeal_map (f : k →+* S) :
    Ideal.map (MvPolynomial.map f) (detIdeal m n t k) =
      detIdeal m n t S:= by
  classical
  let φ : MvPolynomial (Fin m × Fin n) k →+* MvPolynomial (Fin m × Fin n) S :=
    MvPolynomial.map f
  apply le_antisymm
  · refine (Ideal.map_le_iff_le_comap).2 ?_
    change Ideal.span (minorSet t) ≤
      Ideal.comap φ (Ideal.span (minorSet t))
    refine (Ideal.span_le).2 ?_
    intro x hx
    rcases hx with ⟨I, rfl⟩
    have hx' :
        φ (genericMinor I) ∈
          Ideal.span (minorSet t) := by
      exact Ideal.subset_span ⟨I, (map_minor f I).symm⟩
    simpa [φ, map_minor f I] using hx'
  · change Ideal.span (minorSet t) ≤
      Ideal.map (MvPolynomial.map f) (Ideal.span (minorSet t))
    refine (Ideal.span_le).2 ?_
    intro x hx
    rcases hx with ⟨I, rfl⟩
    have hmem :
        genericMinor I ∈
          detIdeal m n t k := minor_mem_detIdeal k I
    have hx' :
        (MvPolynomial.map f) (genericMinor I) ∈
          Ideal.map (MvPolynomial.map f) (detIdeal m n t k) := by
      exact Ideal.mem_map_of_mem (MvPolynomial.map f) hmem
    simpa [map_minor f I] using hx'

end BaseChange

end Determinantal
