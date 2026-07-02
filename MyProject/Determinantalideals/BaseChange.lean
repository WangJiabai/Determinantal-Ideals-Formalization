/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.Ideal

/-!
# Base change for determinantal ideals

Compatibility layer for coefficient-wise base change through the Mathlib-candidate `Matrix` API.
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
      genericMatrix m n S :=
  by
    ext i j
    simp [genericMatrix]

/-- Mapping coefficients along `f` sends a generic minor over `k` to the corresponding
generic minor over `S`. -/
lemma map_minor (f : k →+* S) (I : MinorIndex m n t) :
    (MvPolynomial.map f) (genericMinor k I) =
      genericMinor S I :=
  Matrix.MinorIndex.map_mvPolynomialMinor f I

/-- Determinantal ideals are compatible with coefficient-wise base change. -/
lemma detIdeal_map (f : k →+* S) :
    Ideal.map (MvPolynomial.map f) (detIdeal m n t k) =
      detIdeal m n t S :=
  MvPolynomial.map_determinantalIdeal f m n t

end BaseChange

end Determinantal
