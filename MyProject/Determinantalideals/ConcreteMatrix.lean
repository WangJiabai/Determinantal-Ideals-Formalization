/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.Eval

/-!
# Concrete matrix lemmas

This file records basic compatibility lemmas for concrete minors of actual matrices.
-/

namespace Determinantal

section ConcreteMatrix

variable {S T : Type*} [CommRing S] [CommRing T]
variable {m n t : ℕ}

/-- Concrete minors are natural with respect to a ring homomorphism:
applying `f` to a minor of `A` gives the corresponding minor of `A.map f`. -/
lemma matrixMinor_map
    (f : S →+* T) (A : Matrix (Fin m) (Fin n) S) (I : MinorIndex m n t) :
    f (matrixMinor (m := m) (n := n) (t := t) A I) =
      matrixMinor (m := m) (n := n) (t := t) (A.map f) I := by
  classical
  unfold matrixMinor
  simpa [Matrix.submatrix_map] using
    (RingHom.map_det f (Matrix.submatrix A I.row I.col))

end ConcreteMatrix

end Determinantal
