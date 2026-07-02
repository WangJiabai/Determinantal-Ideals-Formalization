/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.Eval

/-!
# Concrete matrix lemmas

Compatibility layer for concrete minors through the Mathlib-candidate `Matrix` API.
-/

namespace Determinantal

section ConcreteMatrix

variable {S T : Type*} [CommRing S] [CommRing T]
variable {m n t : ℕ}

/-- Concrete minors are natural with respect to a ring homomorphism:
applying `f` to a minor of `A` gives the corresponding minor of `A.map f`. -/
lemma matrixMinor_map
    (f : S →+* T) (A : Matrix (Fin m) (Fin n) S) (I : MinorIndex m n t) :
    f (matrixMinor A I) =
      matrixMinor (A.map f) I :=
  Matrix.MinorIndex.detSubmatrix_map f I A

end ConcreteMatrix

end Determinantal
