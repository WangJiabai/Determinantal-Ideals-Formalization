import MyProject.Determinantalideals.ReducedGroebner

/-!
Reproducible artifact audit for selected paper-facing declarations. The output
lists transitive logical dependencies; foundational Lean constants are not
project-specific axiom declarations.
-/

-- 1. KRS correspondence.
#print axioms Determinantal.KRS.krsEquiv
#print axioms Determinantal.exists_krsEquiv

-- 2. Filtered and unfiltered straightening.
#print axioms Determinantal.straightening_law_exists_filtered
#print axioms Determinantal.straightening_law

-- 3. Standard-bitableau quotient basis.
#print axioms Determinantal.exists_standardBitableau_basis_determinantalRing

-- 4. Total-degree Hilbert formula.
#print axioms Determinantal.hilbertFunction_detRing_eq_card_monomialExp_width_le

-- 5. Width criterion for the monomial initial ideal.
#print axioms Determinantal.monomial_mem_initGrPlusOne_iff_width
#print axioms Determinantal.lemma6_monomial_mem_initGrPlusOne_iff_width

-- 6. Raw Gröbner basis: descriptive interface, paper alias, and concrete order.
#print axioms Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
#print axioms Determinantal.theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
#print axioms Determinantal.GrPlusOne_isGroebnerBasis_antiDiagonalLex

-- 7. Support and anti-diagonal rigidity used by interreduction.
#print axioms Determinantal.support_normalizedGenericMinor
#print axioms Determinantal.leadingCoeff_normalizedGenericMinor
#print axioms Determinantal.antidiagExp_le_permExp_imp_minorIndex_eq

-- 8. Interreduction of the original minors.
#print axioms Determinantal.GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder

-- 9. Normalized Gröbner basis.
#print axioms Determinantal.normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder

-- 10. Abstract normalized reduced Gröbner basis and paper alias.
#print axioms Determinantal.normalizedGrPlusOne_isReduced_of_isAntidiagonalTermOrder
#print axioms Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder
#print axioms Determinantal.theorem1_normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder

-- 11. Concrete anti-diagonal-order reduced wrappers.
#print axioms Determinantal.normalizedGrPlusOne_isReduced_antiDiagonalLex
#print axioms Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_antiDiagonalLex
