/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.Data.Set.Finite.Basic
import MyProject.Determinantalideals.Basic

/-!
# Finiteness results for minors

This file provides finiteness instances for `MinorIndex m n t`, together with basic finiteness
results for the set of all `t × t` minors of the generic `m × n` matrix.
-/

namespace Determinantal

section FiniteInstances

variable {m n t : ℕ}

instance : Finite (MinorIndex m n t) := by
  classical
  refine Finite.of_injective (fun I : MinorIndex m n t => (I.row, I.col)) ?_
  intro I J h
  cases I
  cases J
  cases h
  rfl

noncomputable instance : Fintype (MinorIndex m n t) :=
  Fintype.ofFinite (MinorIndex m n t)

end FiniteInstances

section FiniteTools

variable {k : Type*} [CommRing k]

/-- A convenience description of `minorSet` as the range of `minor`. -/
@[simp] lemma minorSet_eq_range {m n : ℕ} (t : ℕ) :
    minorSet t =
      Set.range (genericMinor (m := m) (n := n) (k := k) (t := t)) :=
  rfl

/-- The set of all `t × t` minors of the generic `m × n` matrix is finite. -/
lemma minorSet_finite {m n : ℕ} (t : ℕ) :
    (minorSet (k := k) (m := m) (n := n) t).Finite := by
  classical
  simpa [minorSet]
    using (Set.finite_range (genericMinor (t := t)))

end FiniteTools

end Determinantal
