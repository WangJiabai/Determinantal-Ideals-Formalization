import Mathlib
import MyProject.Determinantalideals.MinorTerms
import MyProject.Determinantalideals.Basic
import MyProject.Determinantalideals.DiagonalOrder
open scoped BigOperators

namespace Determinantal

section Examples

/-- The `3 × 3` minor of a `4 × 3` matrix using rows `0,1,2` and columns `0,1,2`.

In one-indexed mathematical notation, this is the minor with rows `1,2,3`
and columns `1,2,3`.
-/
noncomputable def principal3MinorIn4x3 : MinorIndex 4 3 3 where
  row := Fin.castLEOrderEmb (by decide : 3 ≤ 4)
  col := Fin.castLEOrderEmb (by decide : 3 ≤ 3)

def r0 : Fin 4 := ⟨0, by decide⟩
def r1 : Fin 4 := ⟨1, by decide⟩
def r2 : Fin 4 := ⟨2, by decide⟩

def c0 : Fin 3 := ⟨0, by decide⟩
def c1 : Fin 3 := ⟨1, by decide⟩
def c2 : Fin 3 := ⟨2, by decide⟩

/-- The anti-diagonal monomial of the `3 × 3` principal minor in a `4 × 3`
generic matrix is `X₁₃ X₂₂ X₃₁`, i.e. in zero-indexed Lean notation,

`X (0,2) * X (1,1) * X (2,0)`.
-/
example {𝕜 : Type*} [CommSemiring 𝕜] :
    antidiagMonomial 𝕜 principal3MinorIn4x3 =
      MvPolynomial.X (r0, c2) *
        MvPolynomial.X (r1, c1) *
          MvPolynomial.X (r2, c0) := by
  classical
  simp [antidiagMonomial, antidiagExp, principal3MinorIn4x3,
    r0, r1, r2, c0, c1, c2,
    Fin.sum_univ_three, MvPolynomial.X, Fin.rev]

/-- The diagonal monomial of the `3 × 3` principal minor in a `4 × 3`
generic matrix is `X₁₁ X₂₂ X₃₃`, i.e in zero-indexed Lean notation,
`X (0,0) * X (1,1) * X (2,2)`.
-/
example {𝕜 : Type*} [CommSemiring 𝕜] :
    diagMonomial 𝕜 principal3MinorIn4x3 =
      MvPolynomial.X (r0, c0) *
        MvPolynomial.X (r1, c1) *
          MvPolynomial.X (r2, c2) := by
  classical
  simp [diagMonomial, diagExp, principal3MinorIn4x3,
    r0, r1, r2, c0, c1, c2,
    Fin.sum_univ_three, MvPolynomial.X]

def emb3to4 : Fin 3 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono
    (fun i : Fin 3 =>
      ![
        (⟨0, by decide⟩ : Fin 4),
        (⟨1, by decide⟩ : Fin 4),
        (⟨2, by decide⟩ : Fin 4)
      ] i)
    (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab ⊢)

def emb3to3 : Fin 3 ↪o Fin 3 :=
  OrderEmbedding.ofStrictMono
    (fun i : Fin 3 =>
      ![
        (⟨0, by decide⟩ : Fin 3),
        (⟨1, by decide⟩ : Fin 3),
        (⟨2, by decide⟩ : Fin 3)
      ] i)
    (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab ⊢)

noncomputable def principal3MinorIn4x3_2 : MinorIndex 4 3 3 where
  row := emb3to4
  col := emb3to3

example {𝕜 : Type*} [CommSemiring 𝕜] :
    diagMonomial 𝕜 principal3MinorIn4x3_2 =
      MvPolynomial.X (r0, c0) *
        MvPolynomial.X (r1, c1) *
          MvPolynomial.X (r2, c2) := by
  classical
  simp [diagMonomial, diagExp, emb3to4,emb3to3,principal3MinorIn4x3_2,
    r0, r1, r2, c0, c1, c2,
    Fin.sum_univ_three, MvPolynomial.X]

def emb5to11 : Fin 5 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono
    (fun i : Fin 5 =>
      ![
        (⟨2, by decide⟩ : Fin 11),
        (⟨5, by decide⟩ : Fin 11),
        (⟨6, by decide⟩ : Fin 11),
        (⟨7, by decide⟩ : Fin 11),
        (⟨10, by decide⟩ : Fin 11)
      ] i)
    (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab ⊢)

example [CommRing k]:genericMinor k principal3MinorIn4x3_2=
          MvPolynomial.X
            ((⟨0, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨1, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨2, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 3))
      - MvPolynomial.X
            ((⟨0, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨1, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨2, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 3))
      - MvPolynomial.X
            ((⟨0, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨1, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨2, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 3))
      + MvPolynomial.X
            ((⟨0, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨1, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨2, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 3))
      + MvPolynomial.X
            ((⟨0, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨1, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨2, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 3))
      - MvPolynomial.X
            ((⟨0, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨1, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 3)) *
          MvPolynomial.X
            ((⟨2, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 3)) := by
  classical
  simp [genericMinor, Matrix.MinorIndex.mvPolynomialMinor, Matrix.MinorIndex.detSubmatrix,
    Matrix.mvPolynomialX,
    principal3MinorIn4x3_2, emb3to4, emb3to3, Matrix.det_fin_three]

example {k} [Nontrivial k] [CommRing k] (ord : MonomialOrder (Fin 4 × Fin 3))
  (hdiag : IsDiagonalTermOrder ord) :
  MvPolynomial.monomial (ord.degree (genericMinor k principal3MinorIn4x3_2)) 1=
          MvPolynomial.X
            ((⟨0, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 3))  *
          MvPolynomial.X
            ((⟨1, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 3))  *
          MvPolynomial.X
            ((⟨2, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 3)):=by
  classical
  rw [degree_minor_eq_diagExp k ord hdiag principal3MinorIn4x3_2]
  unfold diagExp
  rw [MvPolynomial.monomial_sum_one]
  rw [Fin.prod_univ_three]
  simp [principal3MinorIn4x3_2, emb3to4, emb3to3, MvPolynomial.X]

example {k} [CommRing k] :
  ∏ i : Fin 3, (Matrix.diag
  (Matrix.submatrix (genericMatrix 4 3 k)
  principal3MinorIn4x3_2.row principal3MinorIn4x3_2.col)) i =
  MvPolynomial.X
            ((⟨0, by decide⟩ : Fin 4), (⟨0, by decide⟩ : Fin 3))  *
          MvPolynomial.X
            ((⟨1, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 3))  *
          MvPolynomial.X
            ((⟨2, by decide⟩ : Fin 4), (⟨2, by decide⟩ : Fin 3)):=by
  classical
  rw [Fin.prod_univ_three]
  simp [Matrix.diag, Matrix.submatrix, genericMatrix,
    principal3MinorIn4x3_2, emb3to4, emb3to3]

example [CommRing k] (I : MinorIndex m n t) :
 diagTerm k I = diagMonomial k I:=by
  classical
  unfold diagTerm diagMonomial
  change
      (∏ i : Fin t,
        MvPolynomial.X (I.row i, I.col i)) =
      MvPolynomial.monomial (diagExp I) (1 : k)
  rw [diagExp]
  symm
  simpa [MvPolynomial.X] using
    (MvPolynomial.monomial_sum_index
      (s := Finset.univ)
      (f := fun i : Fin t =>
        Finsupp.single (I.row i, I.col i) 1)
      (a := (1 : k)))

end Examples

end Determinantal
