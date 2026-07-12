import MyProject.Determinantalideals.Groebner

/-!
# Paper-facing declaration audit

This file checks the names and displayed types used by the AFM manuscript. It
does not add mathematical API; compilation fails if a referenced declaration
is renamed or if either checked signature drifts.
-/

#check Determinantal.MinorIndex
#check Determinantal.genericMinor
#check Determinantal.Jr
#check Determinantal.GrPlusOne
#check Determinantal.IsAntidiagonalTermOrder
#check Determinantal.antiDiagonalLex
#check Determinantal.degree_minor_eq_antidiagExp
#check Determinantal.leadingCoeff_minor_eq_revPermCoeff
#check Determinantal.leadingTerm_minor_eq_antidiagMonomial_coeff
#check Determinantal.exists_krsEquiv
#check Determinantal.KRS.krsEquiv
#check Determinantal.exists_krsEquiv_of_degree
#check Determinantal.exists_krsEquiv_of_degree_widthLE
#check Determinantal.straightening_law_exists_filtered
#check Determinantal.straightening_law
#check Determinantal.exists_standardBitableau_basis_determinantalRing
#check Determinantal.RrDegree
#check Determinantal.initGrPlusOne
#check Determinantal.hilbertFunction_detRing_eq_card_monomialExp_width_le
#check Determinantal.lemma6_monomial_mem_initGrPlusOne_iff_width
#check Determinantal.theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
#check Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
#check Determinantal.GrPlusOne_isGroebnerBasis_antiDiagonalLex

example {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : Determinantal.IsAntidiagonalTermOrder ord) :
    ord.IsGroebnerBasis
      (Determinantal.GrPlusOne m n r k)
      (Determinantal.Jr m n r k) := by
  exact
    Determinantal.theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
      k ord hanti

example {m n : ℕ}
    (k : Type*) [Field k]
    (r d : ℕ) :
    Module.finrank k (Determinantal.RrDegree m n r k d) =
      Nat.card
        { E : (Fin m × Fin n) →₀ ℕ //
            Finsupp.degree E = d ∧ Determinantal.monomialWidth E ≤ r } := by
  exact
    Determinantal.hilbertFunction_detRing_eq_card_monomialExp_width_le
      k r d
