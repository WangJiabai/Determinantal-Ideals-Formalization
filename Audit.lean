import MyProject.Determinantalideals.Groebner

/-!
Reproducible artifact audit for selected descriptive declarations. The output
lists transitive logical dependencies; foundational Lean constants are not
project-specific axiom declarations.
-/

#print axioms Determinantal.KRS.krsEquiv
#print axioms Determinantal.straightening_law
#print axioms Determinantal.exists_standardBitableau_basis_determinantalRing
#print axioms Determinantal.hilbertFunction_detRing_eq_card_monomialExp_width_le
#print axioms Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
#print axioms Determinantal.GrPlusOne_isGroebnerBasis_antiDiagonalLex
