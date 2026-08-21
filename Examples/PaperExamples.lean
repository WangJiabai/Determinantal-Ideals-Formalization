import MyProject.Determinantalideals.ReducedGroebner

/-!
# Reviewer-facing examples

These examples show how to invoke the final public API for the verified
concrete anti-diagonal lexicographic order over an arbitrary field.
-/

/-- The original generic minors form a Gröbner basis for `antiDiagonalLex`. -/
example {m n r : ℕ} (k : Type*) [Field k] :
    (Determinantal.antiDiagonalLex m n).IsGroebnerBasis
      (Determinantal.GrPlusOne m n r k)
      (Determinantal.Jr m n r k) := by
  exact Determinantal.GrPlusOne_isGroebnerBasis_antiDiagonalLex (k := k)

/-- The coefficient-normalized minors form a reduced Gröbner basis. -/
example {m n r : ℕ} (k : Type*) [Field k] :
    ∃ hGB :
        (Determinantal.antiDiagonalLex m n).IsGroebnerBasis
          (Determinantal.normalizedGrPlusOne m n r k)
          (Determinantal.Jr m n r k),
      hGB.IsReduced := by
  exact
    Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_antiDiagonalLex
      k
