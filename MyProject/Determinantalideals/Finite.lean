/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.Basic

/-!
# Finiteness results for minors

Compatibility layer for finiteness results over the project-local `Matrix` API
following Mathlib conventions.
-/

namespace Determinantal

section FiniteInstances

variable {m n t : ℕ}

instance : Finite (MinorIndex m n t) := inferInstance

noncomputable instance : Fintype (MinorIndex m n t) := inferInstance

end FiniteInstances

section FiniteTools

variable {k : Type*} [CommRing k]

/-- A convenience description of `minorSet` as the range of `minor`. -/
@[simp] lemma minorSet_eq_range {m n : ℕ} (t : ℕ) :
    minorSet k m n t =
      Set.range (fun I : MinorIndex m n t => genericMinor k I) :=
  rfl

/-- The set of all `t × t` minors of the generic `m × n` matrix is finite. -/
lemma minorSet_finite {m n : ℕ} (t : ℕ) :
    (minorSet k m n t).Finite :=
  Set.finite_range (fun I : MinorIndex m n t => genericMinor k I)

end FiniteTools

end Determinantal
