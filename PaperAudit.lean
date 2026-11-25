import MyProject.Determinantalideals.ReducedGroebner

/-!
# Paper-facing declaration audit

This file checks the principal declarations and selected exact theorem
signatures. Compilation fails if a referenced declaration is renamed or if a
checked signature changes.
-/

-- Determinantal ideals, minors, and anti-diagonal orders.
#check Determinantal.MinorIndex
#check Determinantal.genericMinor
#check Determinantal.Jr
#check Determinantal.GrPlusOne
#check Determinantal.IsAntidiagonalTermOrder
#check Determinantal.antiDiagonalLex
#check Determinantal.degree_minor_eq_antidiagExp
#check Determinantal.leadingCoeff_minor_eq_revPermCoeff
#check Determinantal.leadingTerm_minor_eq_antidiagMonomial_coeff

-- KRS and straightening interfaces.
#check Determinantal.exists_krsEquiv
#check Determinantal.KRS.krsEquiv
#check Determinantal.exists_krsEquiv_of_degree
#check Determinantal.exists_krsEquiv_of_degree_widthLE
#check Determinantal.straightening_law_exists_filtered
#check Determinantal.straightening_law
#check Determinantal.exists_standardBitableau_basis_determinantalRing

-- Hilbert-function and width interfaces.
#check Determinantal.RrDegree
#check Determinantal.initGrPlusOne
#check Determinantal.hilbertFunction_detRing_eq_card_monomialExp_width_le
#check Determinantal.monomial_mem_initGrPlusOne_iff_width
#check Determinantal.lemma6_monomial_mem_initGrPlusOne_iff_width

-- Raw Gröbner-basis interfaces.
#check Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
#check Determinantal.GrPlusOne_isGroebnerBasis_antiDiagonalLex
#check Determinantal.theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder

-- Interreduction and coefficient-normalized reduced refinement.
#check Determinantal.normalizedGenericMinor
#check Determinantal.support_normalizedGenericMinor
#check Determinantal.leadingCoeff_normalizedGenericMinor
#check Determinantal.normalizedGrPlusOne
#check Determinantal.antidiagExp_le_permExp_imp_minorIndex_eq
#check Determinantal.GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder
#check Determinantal.normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
#check Determinantal.normalizedGrPlusOne_isReduced_of_isAntidiagonalTermOrder
#check Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder
#check Determinantal.theorem1_normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder
#check Determinantal.normalizedGrPlusOne_isReduced_antiDiagonalLex
#check Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_antiDiagonalLex

-- Full manuscript-facing signature: KRS equivalence.
example (m n : ℕ) :
    ∃ κ :
      ((Fin m × Fin n) →₀ ℕ) ≃
        Determinantal.StandardYoungBitableau m n,
      (∀ E : (Fin m × Fin n) →₀ ℕ,
        Determinantal.YoungBitableau.degree ((κ E).1) =
          Finsupp.degree E)
      ∧
      (∀ E : (Fin m × Fin n) →₀ ℕ,
        Determinantal.monomialWidth E =
          Determinantal.YoungBitableau.length ((κ E).1)) := by
  exact Determinantal.exists_krsEquiv m n

-- Full manuscript-facing signature: filtered straightening.
example {m n : ℕ}
    (k : Type*) [Field k]
    (B : Determinantal.YoungBitableau m n) :
    ∃ c : Determinantal.StandardYoungBitableau m n →₀ k,
      Determinantal.YoungBitableau.toPolynomial k B =
        c.sum (fun S a =>
          MvPolynomial.C a *
            Determinantal.YoungBitableau.toPolynomial k S.1)
      ∧
      (∀ S, c S ≠ 0 →
        Determinantal.YoungBitableau.degree S.1 =
          Determinantal.YoungBitableau.degree B)
      ∧
      (∀ S, c S ≠ 0 →
        Determinantal.YoungBitableau.length B ≤
          Determinantal.YoungBitableau.length S.1) := by
  exact Determinantal.straightening_law_exists_filtered k B

-- Full manuscript-facing signature: raw abstract Gröbner basis.
example {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : Determinantal.IsAntidiagonalTermOrder ord) :
    ord.IsGroebnerBasis
      (Determinantal.GrPlusOne m n r k)
      (Determinantal.Jr m n r k) := by
  exact
    Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
      k ord hanti

-- Full manuscript-facing signature: Hilbert function.
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

-- Full manuscript-facing signature: interreduction of the original minors.
example {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : Determinantal.IsAntidiagonalTermOrder ord) :
    ∀ p ∈ Determinantal.GrPlusOne m n r k,
      ord.IsRemainder p
        (Determinantal.GrPlusOne m n r k \ {p}) p := by
  exact
    Determinantal.GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder
      k ord hanti

-- Full manuscript-facing signature: normalized reduced Gröbner basis.
example {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : Determinantal.IsAntidiagonalTermOrder ord) :
    ∃ hGB :
        ord.IsGroebnerBasis
          (Determinantal.normalizedGrPlusOne m n r k)
          (Determinantal.Jr m n r k),
      hGB.IsReduced := by
  exact
    Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder
      k ord hanti

-- Concrete anti-diagonal-order corollaries used by reviewers.
example {m n r : ℕ}
    (k : Type*) [Field k] :
    (Determinantal.normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
      (r := r) k (Determinantal.antiDiagonalLex m n)
      (Determinantal.antiDiagonalLex_isAntidiagonal m n)).IsReduced := by
  exact Determinantal.normalizedGrPlusOne_isReduced_antiDiagonalLex k

example {m n r : ℕ}
    (k : Type*) [Field k] :
    ∃ hGB :
        (Determinantal.antiDiagonalLex m n).IsGroebnerBasis
          (Determinantal.normalizedGrPlusOne m n r k)
          (Determinantal.Jr m n r k),
      hGB.IsReduced := by
  exact
    Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_antiDiagonalLex
      k
