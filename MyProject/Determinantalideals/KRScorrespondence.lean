/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.Bitableaux

namespace Determinantal

attribute [local instance] MvPolynomial.gradedAlgebra

/-!
## KRS proof skeleton

The following namespace records the dependency structure from `KRS.pdf`.  It is intentionally
split into paper-level statements: row insertion, reverse insertion, the KRS bijection, the
Schensted width theorem, and the conversion between semistandard tableau pairs and the Lean
`YoungBitableau` representation by columns.
-/

namespace KRS

/-- A generalized permutation, represented as a row-column lexicographically sorted biword. -/
abbrev Biword (m n : ℕ) :=
  { w : List (Fin m × Fin n) // w.Pairwise (fun x y => toLex x ≤ toLex y) }

/-- The generalized permutation attached to a monomial exponent vector. -/
noncomputable def expandedBiword {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) : Biword m n :=
  ⟨Determinantal.generalizedPermutation
      (generalizedPermutation.indicesOfMonomialExp E),
    generalizedPermutation.generalizedPermutation_sorted
      (generalizedPermutation.indicesOfMonomialExp E)⟩

/-- A thin wrapper around Mathlib semistandard Young tableaux with bounded entries. -/
structure BoundedSSYT (μ : YoungDiagram) (N : ℕ) where
  T : SemistandardYoungTableau μ
  bound : ∀ {i j : ℕ}, (i, j) ∈ μ → T i j < N

/-!
The small namespaces below are internal proof modules for dependent KRS
records.  They are kept as namespaces because their qualified names document
which record each lemma belongs to.
-/

namespace BoundedSSYT

/-- Two bounded SSYTs of the same shape are equal if their entries agree. -/
@[ext]
theorem ext {μ : YoungDiagram} {N : ℕ} {S T : BoundedSSYT μ N}
    (h : ∀ i j, S.T i j = T.T i j) : S = T := by
  cases S with
  | mk S hS =>
      cases T with
      | mk T hT =>
          have htableau : S = T := SemistandardYoungTableau.ext h
          cases htableau
          congr

/-- Heterogeneous extensionality for bounded SSYTs over propositionally equal shapes. -/
theorem heq_of_entry_eq {μ ν : YoungDiagram} {N : ℕ}
    {S : BoundedSSYT μ N} {T : BoundedSSYT ν N}
    (hμ : μ = ν) (h : ∀ i j, S.T i j = T.T i j) : HEq S T := by
  cases hμ
  exact heq_of_eq (ext h)

end BoundedSSYT

/-- Height of the first column of a Young diagram. -/
noncomputable def firstColumnHeight (μ : YoungDiagram) : ℕ :=
  μ.colLen 0

/-- A cell is addable to `μ` if adjoining exactly that cell gives another Young diagram. -/
def IsAddableCorner (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∉ μ ∧ ∃ μ' : YoungDiagram, c ∈ μ' ∧ ∀ d, d ∈ μ' ↔ d ∈ μ ∨ d = c

/-- A cell is removable from `μ` if deleting exactly that cell gives another Young diagram. -/
def IsRemovableCorner (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∈ μ ∧ ∃ μ' : YoungDiagram, c ∉ μ' ∧ ∀ d, d ∈ μ ↔ d ∈ μ' ∨ d = c

/-- A pair `(P,Q)` of bounded semistandard tableaux of the same Mathlib Young shape.

`P` is the lower tableau, with entries bounded by `n`; `Q` is the recording tableau,
with entries bounded by `m`. -/
structure TableauPair (m n : ℕ) where
  shape : YoungDiagram
  P : BoundedSSYT shape n
  Q : BoundedSSYT shape m

namespace TableauPair

/-- Heterogeneous extensionality for tableau pairs, useful when the common shape is obtained
by a non-definitional Young diagram equality. -/
theorem ext_heq {m n : ℕ} {S T : TableauPair m n}
    (hshape : S.shape = T.shape)
    (hP : HEq S.P T.P) (hQ : HEq S.Q T.Q) : S = T := by
  cases S with
  | mk Sshape SP SQ =>
      cases T with
      | mk Tshape TP TQ =>
          dsimp at hshape hP hQ
          cases hshape
          cases hP
          cases hQ
          rfl

end TableauPair

/-- The result of row insertion: the shape changes by adding one new cell. -/
structure RowInsertResult (N : ℕ) (μ : YoungDiagram) where
  shape : YoungDiagram
  tableau : BoundedSSYT shape N
  newCell : ℕ × ℕ
  old_subset : ∀ c, c ∈ μ → c ∈ shape
  newCell_mem : newCell ∈ shape
  newCell_not_mem_old : newCell ∉ μ
  shape_mem_iff : ∀ c, c ∈ shape ↔ c ∈ μ ∨ c = newCell
  newCell_addable : IsAddableCorner μ newCell
  newCell_removable : IsRemovableCorner shape newCell
  card_eq : shape.card = μ.card + 1

namespace RowInsertResult

theorem ext_heq {N : ℕ} {μ : YoungDiagram} {R S : RowInsertResult N μ}
    (hshape : R.shape = S.shape)
    (htableau : HEq R.tableau S.tableau)
    (hcell : R.newCell = S.newCell) : R = S := by
  cases R with
  | mk Rshape Rtab Rcell Ros Rmem Rnot Riff Radd Rrem Rcard =>
      cases S with
      | mk Sshape Stab Scell Sos Smem Snot Siff Sadd Srem Scard =>
          dsimp at hshape htableau hcell
          cases hshape
          cases htableau
          cases hcell
          congr

end RowInsertResult

/-- `ν` is obtained from `μ` by adjoining exactly the cell `c`. -/
def ExtendsByCell (μ ν : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  ∀ d, d ∈ ν ↔ d ∈ μ ∨ d = c

namespace ExtendsByCell

theorem old_subset {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) : μ ≤ ν := by
  intro d hd
  exact (h d).2 (Or.inl hd)

theorem new_mem {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) : c ∈ ν := by
  exact (h c).2 (Or.inr rfl)

theorem cells_eq_insert {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) : ν.cells = insert c μ.cells := by
  ext d
  rw [YoungDiagram.mem_cells, h]
  simp [or_comm]

theorem card_eq {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) (hc : c ∉ μ) :
    ν.card = μ.card + 1 := by
  change ν.cells.card = μ.cells.card + 1
  rw [cells_eq_insert h]
  rw [Finset.card_insert_of_notMem]
  simpa using hc

theorem rowLen_lt_iff {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) (i j : ℕ) :
    j < ν.rowLen i ↔ j < μ.rowLen i ∨ (i, j) = c := by
  rw [← YoungDiagram.mem_iff_lt_rowLen, h, YoungDiagram.mem_iff_lt_rowLen]

theorem colLen_lt_iff {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) (i j : ℕ) :
    i < ν.colLen j ↔ i < μ.colLen j ∨ (i, j) = c := by
  rw [← YoungDiagram.mem_iff_lt_colLen, h, YoungDiagram.mem_iff_lt_colLen]

theorem rowLen_eq_of_ne {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) {i : ℕ} (hi : i ≠ c.1) :
    ν.rowLen i = μ.rowLen i := by
  apply eq_of_forall_lt_iff
  intro j
  rw [rowLen_lt_iff h]
  constructor
  · rintro (hj | hcell)
    · exact hj
    · exact False.elim (hi (congrArg Prod.fst hcell))
  · intro hj
    exact Or.inl hj

theorem colLen_eq_of_ne {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) {j : ℕ} (hj : j ≠ c.2) :
    ν.colLen j = μ.colLen j := by
  apply eq_of_forall_lt_iff
  intro i
  rw [colLen_lt_iff h]
  constructor
  · rintro (hi | hcell)
    · exact hi
    · exact False.elim (hj (congrArg Prod.snd hcell))
  · intro hi
    exact Or.inl hi

theorem old_rowLen_at_newCell {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) (hc : c ∉ μ) :
    μ.rowLen c.1 = c.2 := by
  apply le_antisymm
  · apply Nat.le_of_not_gt
    intro hlt
    exact hc (by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      exact hlt)
  · rw [← forall_lt_iff_le]
    intro j hj
    have hcellν : (c.1, j) ∈ ν :=
      ν.up_left_mem le_rfl (Nat.le_of_lt hj) (new_mem h)
    have hcell : (c.1, j) ∈ μ ∨ (c.1, j) = c := (h (c.1, j)).1 hcellν
    rcases hcell with hcellμ | hcell_eq
    · rwa [YoungDiagram.mem_iff_lt_rowLen] at hcellμ
    · exact False.elim (Nat.ne_of_lt hj (congrArg Prod.snd hcell_eq))

theorem rowLen_at_newCell {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) (hc : c ∉ μ) :
    ν.rowLen c.1 = μ.rowLen c.1 + 1 := by
  rw [old_rowLen_at_newCell h hc]
  apply eq_of_forall_lt_iff
  intro j
  rw [rowLen_lt_iff h, old_rowLen_at_newCell h hc]
  constructor
  · rintro (hj | hcell)
    · omega
    · have hj : j = c.2 := congrArg Prod.snd hcell
      omega
  · intro hj
    by_cases hjeq : j = c.2
    · exact Or.inr (by ext <;> simp [hjeq])
    · exact Or.inl (by omega)

theorem old_colLen_at_newCell {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) (hc : c ∉ μ) :
    μ.colLen c.2 = c.1 := by
  apply le_antisymm
  · apply Nat.le_of_not_gt
    intro hlt
    exact hc (by
      rw [YoungDiagram.mem_iff_lt_colLen]
      exact hlt)
  · rw [← forall_lt_iff_le]
    intro i hi
    have hcellν : (i, c.2) ∈ ν :=
      ν.up_left_mem (Nat.le_of_lt hi) le_rfl (new_mem h)
    have hcell : (i, c.2) ∈ μ ∨ (i, c.2) = c := (h (i, c.2)).1 hcellν
    rcases hcell with hcellμ | hcell_eq
    · rwa [YoungDiagram.mem_iff_lt_colLen] at hcellμ
    · exact False.elim (Nat.ne_of_lt hi (congrArg Prod.fst hcell_eq))

theorem colLen_at_newCell {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (h : ExtendsByCell μ ν c) (hc : c ∉ μ) :
    ν.colLen c.2 = μ.colLen c.2 + 1 := by
  rw [old_colLen_at_newCell h hc]
  apply eq_of_forall_lt_iff
  intro i
  rw [colLen_lt_iff h, old_colLen_at_newCell h hc]
  constructor
  · rintro (hi | hcell)
    · omega
    · have hi : i = c.1 := congrArg Prod.fst hcell
      omega
  · intro hi
    by_cases hieq : i = c.1
    · exact Or.inr (by ext <;> simp [hieq])
    · exact Or.inl (by omega)

end ExtendsByCell

namespace IsAddableCorner

theorem exists_extension {μ : YoungDiagram} {c : ℕ × ℕ}
    (h : IsAddableCorner μ c) :
    ∃ ν : YoungDiagram, ExtendsByCell μ ν c ∧ c ∉ μ ∧ c ∈ ν := by
  rcases h with ⟨hc, ν, hmem, hν⟩
  exact ⟨ν, hν, hc, hmem⟩

end IsAddableCorner

namespace YoungDiagram

theorem not_mem_row_rowLen (μ : YoungDiagram) (row : ℕ) :
    (row, μ.rowLen row) ∉ μ := by
  rw [YoungDiagram.mem_iff_lt_rowLen]
  exact Nat.lt_irrefl _

end YoungDiagram

namespace IsAddableCorner

/-- The cell at the end of row `row` is addable if it is in the top row, or if the row
above already contains that column. This is the local Young-diagram fact needed by
the append branch of row insertion. -/
theorem row_rowLen {μ : YoungDiagram} {row : ℕ}
    (habove : row = 0 ∨ (row - 1, μ.rowLen row) ∈ μ) :
    IsAddableCorner μ (row, μ.rowLen row) := by
  classical
  let c : ℕ × ℕ := (row, μ.rowLen row)
  let ν : YoungDiagram :=
    { cells := insert c μ.cells
      isLowerSet := by
        intro upper lower hle hlower
        rw [Finset.mem_coe, Finset.mem_insert] at hlower ⊢
        rcases hlower with hlower_eq | hlowerμ
        · have hlower_le : lower ≤ c := by simpa [hlower_eq] using hle
          by_cases hlower_eq' : lower = c
          · exact Or.inl hlower_eq'
          · right
            change lower ∈ μ
            have hlower_fst : lower.1 ≤ row := (Prod.mk_le_mk.mp hlower_le).1
            have hlower_snd : lower.2 ≤ μ.rowLen row := (Prod.mk_le_mk.mp hlower_le).2
            by_cases hrow : lower.1 = row
            · have hlower_snd_lt : lower.2 < μ.rowLen row := lt_of_le_of_ne hlower_snd (by
                intro h
                exact hlower_eq' (by ext <;> simp [c, hrow, h]))
              rw [show lower = (row, lower.2) by exact Prod.ext hrow rfl,
                YoungDiagram.mem_iff_lt_rowLen]
              exact hlower_snd_lt
            · have hlower_fst_lt : lower.1 < row := lt_of_le_of_ne hlower_fst hrow
              by_cases hlower_snd_eq : lower.2 = μ.rowLen row
              · have hcell : (lower.1, μ.rowLen row) ∈ μ := by
                  rcases habove with htop | habove'
                  · omega
                  · exact μ.up_left_mem (Nat.le_pred_of_lt hlower_fst_lt) le_rfl habove'
                rw [show lower = (lower.1, lower.2) by exact Prod.eta lower,
                  hlower_snd_eq]
                exact hcell
              · have hlower_snd_lt : lower.2 < μ.rowLen row :=
                  lt_of_le_of_ne hlower_snd hlower_snd_eq
                have hrowcell : (row, lower.2) ∈ μ := by
                  rw [YoungDiagram.mem_iff_lt_rowLen]
                  exact hlower_snd_lt
                rw [show lower = (lower.1, lower.2) by exact Prod.eta lower]
                exact μ.up_left_mem hlower_fst le_rfl hrowcell
        · exact Or.inr (μ.isLowerSet hle hlowerμ) }
  refine ⟨YoungDiagram.not_mem_row_rowLen μ row, ν, ?_, ?_⟩
  · change c ∈ ν
    simp [ν]
  · intro d
    change d ∈ ν ↔ d ∈ μ ∨ d = c
    simp [ν, c, or_comm]

end IsAddableCorner

theorem IsAddableCorner.above_mem {μ : YoungDiagram} {c : ℕ × ℕ}
    (hc : IsAddableCorner μ c) (hrow : c.1 ≠ 0) :
    (c.1 - 1, c.2) ∈ μ := by
  rcases hc with ⟨hcnot, ν, hcν, hν⟩
  have haboveν : (c.1 - 1, c.2) ∈ ν := by
    exact ν.up_left_mem (by omega) le_rfl hcν
  rcases (hν (c.1 - 1, c.2)).1 haboveν with hμ | heq
  · exact hμ
  · have hrow_eq : c.1 - 1 = c.1 := congrArg Prod.fst heq
    omega

theorem IsAddableCorner.row_le_of_removable_col_lt {μ : YoungDiagram} {c d : ℕ × ℕ}
    (hc : IsAddableCorner μ c) (hd : IsRemovableCorner μ d) (hcol : d.2 < c.2) :
    c.1 ≤ d.1 := by
  by_contra hnot
  have hdrow_lt : d.1 < c.1 := Nat.lt_of_not_ge hnot
  have hcrow_ne : c.1 ≠ 0 := by omega
  have habove : (c.1 - 1, c.2) ∈ μ := hc.above_mem hcrow_ne
  have hright : (d.1, c.2) ∈ μ :=
    μ.up_left_mem (by omega) le_rfl habove
  rcases hd with ⟨hdmem, ν, hdnot, hν⟩
  have hrightν : (d.1, c.2) ∈ ν := by
    rcases (hν (d.1, c.2)).1 hright with hνmem | heq
    · exact hνmem
    · have hcol_eq' := congrArg (fun p : ℕ × ℕ => p.2) heq
      have hcol_eq : c.2 = d.2 := by simpa using hcol_eq'
      omega
  have hdν : d ∈ ν :=
    ν.up_left_mem le_rfl (Nat.le_of_lt hcol) hrightν
  exact hdnot hdν

namespace IsRemovableCorner

theorem exists_deletion {μ : YoungDiagram} {c : ℕ × ℕ}
    (h : IsRemovableCorner μ c) :
    ∃ ν : YoungDiagram, ExtendsByCell ν μ c ∧ c ∉ ν ∧ c ∈ μ := by
  rcases h with ⟨hmem, ν, hc, hν⟩
  exact ⟨ν, hν, hc, hmem⟩

/-- A cell of a Young diagram is removable if no other cell lies weakly down and
weakly right from it. -/
theorem of_ge_eq {μ : YoungDiagram} {c : ℕ × ℕ}
    (hmem : c ∈ μ)
    (hmax : ∀ {d : ℕ × ℕ}, d ∈ μ → c ≤ d → d = c) :
    IsRemovableCorner μ c := by
  classical
  let ν : YoungDiagram :=
    { cells := μ.cells.erase c
      isLowerSet := by
        intro upper lower hle hupper
        rw [Finset.mem_coe, Finset.mem_erase] at hupper ⊢
        refine ⟨?_, ?_⟩
        · intro hlower_eq
          have hupper_mem : upper ∈ μ := by
            simpa [YoungDiagram.mem_cells] using hupper.2
          have hcu : c ≤ upper := by
            simpa [hlower_eq] using hle
          exact hupper.1 (hmax hupper_mem hcu)
        · have hupper_mem : upper ∈ μ := by
            simpa [YoungDiagram.mem_cells] using hupper.2
          exact μ.isLowerSet hle hupper_mem }
  refine ⟨hmem, ν, ?_, ?_⟩
  · change c ∉ ν
    simp [ν]
  · intro d
    by_cases hd : d = c
    · simp [hd, hmem]
    · constructor
      · intro hdmem
        left
        change d ∈ μ.cells.erase c
        rw [Finset.mem_erase]
        exact ⟨hd, by simpa [YoungDiagram.mem_cells] using hdmem⟩
      · rintro (hdν | hd_eq)
        · change d ∈ μ.cells.erase c at hdν
          exact (Finset.mem_erase.mp hdν).2
        · exact False.elim (hd hd_eq)

end IsRemovableCorner

namespace RowInsertResult

theorem extendsByCell {N : ℕ} {μ : YoungDiagram} (R : RowInsertResult N μ) :
    ExtendsByCell μ R.shape R.newCell :=
  R.shape_mem_iff

theorem old_subset_of_shape_mem_iff {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) : μ ≤ R.shape :=
  ExtendsByCell.old_subset R.extendsByCell

theorem newCell_mem_of_shape_mem_iff {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) : R.newCell ∈ R.shape :=
  ExtendsByCell.new_mem R.extendsByCell

theorem card_eq_of_shape_mem_iff {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) : R.shape.card = μ.card + 1 :=
  ExtendsByCell.card_eq R.extendsByCell R.newCell_not_mem_old

theorem rowLen_lt_iff {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) (i j : ℕ) :
    j < R.shape.rowLen i ↔ j < μ.rowLen i ∨ (i, j) = R.newCell :=
  ExtendsByCell.rowLen_lt_iff R.extendsByCell i j

theorem colLen_lt_iff {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) (i j : ℕ) :
    i < R.shape.colLen j ↔ i < μ.colLen j ∨ (i, j) = R.newCell :=
  ExtendsByCell.colLen_lt_iff R.extendsByCell i j

theorem rowLen_eq_of_ne {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) {i : ℕ} (hi : i ≠ R.newCell.1) :
    R.shape.rowLen i = μ.rowLen i :=
  ExtendsByCell.rowLen_eq_of_ne R.extendsByCell hi

theorem colLen_eq_of_ne {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) {j : ℕ} (hj : j ≠ R.newCell.2) :
    R.shape.colLen j = μ.colLen j :=
  ExtendsByCell.colLen_eq_of_ne R.extendsByCell hj

theorem old_rowLen_at_newCell {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) : μ.rowLen R.newCell.1 = R.newCell.2 :=
  ExtendsByCell.old_rowLen_at_newCell R.extendsByCell R.newCell_not_mem_old

theorem rowLen_at_newCell {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) :
    R.shape.rowLen R.newCell.1 = μ.rowLen R.newCell.1 + 1 :=
  ExtendsByCell.rowLen_at_newCell R.extendsByCell R.newCell_not_mem_old

theorem old_colLen_at_newCell {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) : μ.colLen R.newCell.2 = R.newCell.1 :=
  ExtendsByCell.old_colLen_at_newCell R.extendsByCell R.newCell_not_mem_old

theorem colLen_at_newCell {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) :
    R.shape.colLen R.newCell.2 = μ.colLen R.newCell.2 + 1 :=
  ExtendsByCell.colLen_at_newCell R.extendsByCell R.newCell_not_mem_old

end RowInsertResult

/-- The result of reverse row insertion at a removable cell `c`.

The input shape `μ` is recovered from the output shape by adjoining exactly `c`. -/
structure ReverseRowInsertResult (N : ℕ) (μ : YoungDiagram)
    (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) where
  shape : YoungDiagram
  tableau : BoundedSSYT shape N
  value : Fin N
  cell_mem_old : c ∈ μ
  cell_not_mem_shape : c ∉ shape
  shape_mem_iff : ∀ d, d ∈ μ ↔ d ∈ shape ∨ d = c
  shape_addable : IsAddableCorner shape c
  card_eq : μ.card = shape.card + 1

namespace ReverseRowInsertResult

theorem extendsByCell {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) :
    ExtendsByCell R.shape μ c :=
  R.shape_mem_iff

theorem shape_subset_old {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) :
    R.shape ≤ μ :=
  ExtendsByCell.old_subset R.extendsByCell

theorem cell_mem_old_of_shape_mem_iff {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) :
    c ∈ μ :=
  ExtendsByCell.new_mem R.extendsByCell

theorem card_eq_of_shape_mem_iff {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) :
    μ.card = R.shape.card + 1 :=
  ExtendsByCell.card_eq R.extendsByCell R.cell_not_mem_shape

theorem rowLen_lt_iff {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) (i j : ℕ) :
    j < μ.rowLen i ↔ j < R.shape.rowLen i ∨ (i, j) = c :=
  ExtendsByCell.rowLen_lt_iff R.extendsByCell i j

theorem colLen_lt_iff {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) (i j : ℕ) :
    i < μ.colLen j ↔ i < R.shape.colLen j ∨ (i, j) = c :=
  ExtendsByCell.colLen_lt_iff R.extendsByCell i j

theorem rowLen_eq_of_ne {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc)
    {i : ℕ} (hi : i ≠ c.1) :
    μ.rowLen i = R.shape.rowLen i :=
  ExtendsByCell.rowLen_eq_of_ne R.extendsByCell hi

theorem colLen_eq_of_ne {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc)
    {j : ℕ} (hj : j ≠ c.2) :
    μ.colLen j = R.shape.colLen j :=
  ExtendsByCell.colLen_eq_of_ne R.extendsByCell hj

theorem new_shape_rowLen_at_removedCell {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) :
    R.shape.rowLen c.1 = c.2 :=
  ExtendsByCell.old_rowLen_at_newCell R.extendsByCell R.cell_not_mem_shape

theorem old_rowLen_at_removedCell {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) :
    μ.rowLen c.1 = R.shape.rowLen c.1 + 1 :=
  ExtendsByCell.rowLen_at_newCell R.extendsByCell R.cell_not_mem_shape

theorem new_shape_colLen_at_removedCell {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) :
    R.shape.colLen c.2 = c.1 :=
  ExtendsByCell.old_colLen_at_newCell R.extendsByCell R.cell_not_mem_shape

theorem old_colLen_at_removedCell {N : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ}
    {hc : IsRemovableCorner μ c} (R : ReverseRowInsertResult N μ c hc) :
    μ.colLen c.2 = R.shape.colLen c.2 + 1 :=
  ExtendsByCell.colLen_at_newCell R.extendsByCell R.cell_not_mem_shape

end ReverseRowInsertResult

noncomputable def restrictToSubshape {N : ℕ} {μ ν : YoungDiagram}
    (T : BoundedSSYT μ N) (hsub : ν ≤ μ) : BoundedSSYT ν N where
  T :=
    { entry := fun i j => if (i, j) ∈ ν then T.T i j else 0
      row_weak' := by
        intro i j₁ j₂ hj hcell
        have hcell₁ : (i, j₁) ∈ ν :=
          ν.up_left_mem le_rfl (Nat.le_of_lt hj) hcell
        simp only [hcell₁, ↓reduceIte, hcell, ge_iff_le]
        exact T.T.row_weak hj (hsub hcell)
      col_strict' := by
        intro i₁ i₂ j hi hcell
        have hcell₁ : (i₁, j) ∈ ν :=
          ν.up_left_mem (Nat.le_of_lt hi) le_rfl hcell
        simp only [hcell₁, ↓reduceIte, hcell, gt_iff_lt]
        exact T.T.col_strict hi (hsub hcell)
      zeros' := by
        intro i j hnot
        simp [hnot] }
  bound := by
    intro i j hcell
    change (if (i, j) ∈ ν then T.T i j else 0) < N
    simpa [hcell] using T.bound (hsub hcell)

theorem restrictToSubshape_entry {N : ℕ} {μ ν : YoungDiagram}
    (T : BoundedSSYT μ N) (hsub : ν ≤ μ)
    {i j : ℕ} (hcell : (i, j) ∈ ν) :
    (restrictToSubshape T hsub).T i j = T.T i j := by
  change (if (i, j) ∈ ν then T.T i j else 0) = T.T i j
  simp [hcell]

/-- A valid bumping position in one row: `col` is the first entry in `row`
strictly larger than the inserted value. -/
structure RowBumpLocation {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (x : Fin N) where
  col : ℕ
  cell_mem : (row, col) ∈ μ
  entry_gt : x.val < T.T row col
  left_le : ∀ {j : ℕ}, j < col → (row, j) ∈ μ → T.T row j ≤ x.val

namespace RowBumpLocation

theorem col_lt_rowLen {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (L : RowBumpLocation T row x) :
    L.col < μ.rowLen row := by
  rw [← YoungDiagram.mem_iff_lt_rowLen]
  exact L.cell_mem

theorem bumped_entry_lt_bound {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (L : RowBumpLocation T row x) :
    T.T row L.col < N :=
  T.bound L.cell_mem

end RowBumpLocation

/-- The same-shape result of one bumping step in row insertion.

It replaces the first entry larger than `x` by `x` and returns the bumped entry. -/
structure RowBumpStepResult {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (x : Fin N) where
  col : ℕ
  cell_mem : (row, col) ∈ μ
  entry_gt : x.val < T.T row col
  left_le : ∀ {j : ℕ}, j < col → (row, j) ∈ μ → T.T row j ≤ x.val
  bumped : Fin N
  bumped_eq : T.T row col = bumped.val
  tableau : BoundedSSYT μ N
  replaced_entry : tableau.T row col = x.val
  unchanged_of_ne :
    ∀ {i j : ℕ}, (i, j) ≠ (row, col) → tableau.T i j = T.T i j

namespace RowBumpStepResult

def replaceEntry {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row col : ℕ) (x : Fin N) : ℕ → ℕ → ℕ :=
  fun i j => if (i, j) = (row, col) then x.val else T.T i j

theorem replaceEntry_same {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row col : ℕ) (x : Fin N) :
    replaceEntry T row col x row col = x.val := by
  simp [replaceEntry]

theorem replaceEntry_ne {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row col : ℕ) (x : Fin N)
    {i j : ℕ} (h : (i, j) ≠ (row, col)) :
    replaceEntry T row col x i j = T.T i j := by
  simp [replaceEntry, h]

noncomputable def replaceTableau {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row col : ℕ) (x : Fin N)
    (hcell : (row, col) ∈ μ)
    (hleft : ∀ {j : ℕ}, j < col → (row, j) ∈ μ → T.T row j ≤ x.val)
    (habove : ∀ {i : ℕ}, i < row → (i, col) ∈ μ → T.T i col < x.val)
    (hgt : x.val < T.T row col) : BoundedSSYT μ N where
  T :=
    { entry := replaceEntry T row col x
      row_weak' := by
        intro (i : ℕ) (j₁ : ℕ) (j₂ : ℕ) hj hcell₂
        by_cases h₂ : ((i, j₂) : ℕ × ℕ) = (row, col)
        · have hi : i = row := congrArg Prod.fst h₂
          have hj₂eq : j₂ = col := congrArg Prod.snd h₂
          subst i
          subst j₂
          rw [replaceEntry_same]
          by_cases h₁ : j₁ = col
          · subst j₁
            exact le_imp_le_of_lt_imp_lt (fun a ↦ hgt) (hleft hj hcell)
          · have hj₁lt : j₁ < col := hj
            have hcell₁ : (row, j₁) ∈ μ :=
              μ.up_left_mem le_rfl (Nat.le_of_lt hj₁lt) hcell
            rw [replaceEntry_ne]
            · exact hleft hj₁lt hcell₁
            · intro hp
              exact h₁ (congrArg Prod.snd hp)
        · rw [replaceEntry_ne _ _ _ _ h₂]
          by_cases h₁ : ((i, j₁) : ℕ × ℕ) = (row, col)
          · have hi : i = row := congrArg Prod.fst h₁
            have hj₁eq : j₁ = col := congrArg Prod.snd h₁
            subst i
            subst j₁
            have hcell_old : (row, j₂) ∈ μ := hcell₂
            rw [replaceEntry_same]
            exact le_trans (le_of_lt hgt)
              (T.T.row_weak hj hcell_old)
          · rw [replaceEntry_ne _ _ _ _ h₁]
            exact T.T.row_weak hj hcell₂
      col_strict' := by
        intro (i₁ : ℕ) (i₂ : ℕ) (j : ℕ) hi hcell₂
        by_cases h₂ : ((i₂, j) : ℕ × ℕ) = (row, col)
        · have hi₂eq : i₂ = row := congrArg Prod.fst h₂
          have hjeq : j = col := congrArg Prod.snd h₂
          subst i₂
          subst j
          rw [replaceEntry_same]
          by_cases h₁ : i₁ = row
          · subst i₁
            exact False.elim (Nat.lt_irrefl row hi)
          · have hi₁lt : i₁ < row := hi
            have hcell₁ : (i₁, col) ∈ μ :=
              μ.up_left_mem (Nat.le_of_lt hi₁lt) le_rfl hcell
            rw [replaceEntry_ne]
            · exact habove hi₁lt hcell₁
            · intro hp
              exact h₁ (congrArg Prod.fst hp)
        · rw [replaceEntry_ne _ _ _ _ h₂]
          by_cases hirow : (i₁ : ℕ) = row
          · by_cases hjcol : j = col
            · subst i₁
              subst j
              rw [replaceEntry_same]
              exact lt_trans hgt (T.T.col_strict hi hcell₂)
            · rw [replaceEntry_ne]
              · exact T.T.col_strict hi hcell₂
              · intro hp
                exact hjcol (congrArg Prod.snd hp)
          · rw [replaceEntry_ne]
            · exact T.T.col_strict hi hcell₂
            · intro hp
              exact hirow (congrArg Prod.fst hp)
      zeros' := by
        intro i j hnot
        rw [replaceEntry_ne]
        · exact T.T.zeros hnot
        · intro hp
          exact hnot (by simpa [hp] using hcell) }
  bound := by
    intro i j hmem
    change replaceEntry T row col x i j < N
    by_cases h : ((i, j) : ℕ × ℕ) = (row, col)
    · have hi : i = row := congrArg Prod.fst h
      have hj : j = col := congrArg Prod.snd h
      subst i
      subst j
      rw [replaceEntry_same]
      exact x.isLt
    · rw [replaceEntry_ne _ _ _ _ h]
      exact T.bound hmem

noncomputable def construct {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (x : Fin N)
    (L : RowBumpLocation T row x)
    (habove : ∀ {i : ℕ}, i < row → (i, L.col) ∈ μ → T.T i L.col < x.val) :
    RowBumpStepResult T row x where
  col := L.col
  cell_mem := L.cell_mem
  entry_gt := L.entry_gt
  left_le := L.left_le
  bumped := ⟨T.T row L.col, T.bound L.cell_mem⟩
  bumped_eq := rfl
  tableau := replaceTableau T row L.col x L.cell_mem L.left_le habove L.entry_gt
  replaced_entry := replaceEntry_same T row L.col x
  unchanged_of_ne := by
    intro i j h
    exact replaceEntry_ne T row L.col x h

def location {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) : RowBumpLocation T row x where
  col := B.col
  cell_mem := B.cell_mem
  entry_gt := B.entry_gt
  left_le := B.left_le

theorem bumped_gt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) :
    x.val < B.bumped.val := by
  rw [← B.bumped_eq]
  exact B.entry_gt

theorem col_le_of_entry_gt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) {j : ℕ}
    (hcell : (row, j) ∈ μ) (hgt : x.val < T.T row j) :
    B.col ≤ j := by
  by_contra hnot
  have hjlt : j < B.col := Nat.lt_of_not_ge hnot
  exact not_lt_of_ge (B.left_le hjlt hcell) hgt

theorem bumped_le_entry_of_entry_gt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) {j : ℕ}
    (hcell : (row, j) ∈ μ) (hgt : x.val < T.T row j) :
    B.bumped.val ≤ T.T row j := by
  have hcol : B.col ≤ j := B.col_le_of_entry_gt hcell hgt
  rcases lt_or_eq_of_le hcol with hlt | heq
  · rw [← B.bumped_eq]
    exact T.T.row_weak hlt hcell
  · simpa [heq] using B.bumped_eq.symm.le

theorem unchanged_of_row_ne {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) {i j : ℕ} (hi : i ≠ row) :
    B.tableau.T i j = T.T i j := by
  exact B.unchanged_of_ne (by
    intro h
    exact hi (congrArg Prod.fst h))

theorem unchanged_of_col_ne {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) {i j : ℕ} (hj : j ≠ B.col) :
    B.tableau.T i j = T.T i j := by
  exact B.unchanged_of_ne (by
    intro h
    exact hj (congrArg Prod.snd h))

end RowBumpStepResult

/-- An append position in one row: no existing entry in that row is strictly larger
than the inserted value. -/
structure RowAppendLocation {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (x : Fin N) where
  col : ℕ
  col_eq_rowLen : col = μ.rowLen row
  row_entries_le :
    ∀ {j : ℕ}, j < μ.rowLen row → T.T row j ≤ x.val

namespace RowAppendLocation

theorem newCell_eq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (A : RowAppendLocation T row x) :
    (row, A.col) = (row, μ.rowLen row) := by
  ext <;> simp [A.col_eq_rowLen]

end RowAppendLocation

/-- In a fixed row, row insertion either bumps at the first larger entry or appends at
the row end. This is the finite search step underlying the row insertion algorithm. -/
theorem exists_rowBumpLocation_or_rowAppendLocation {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (x : Fin N) :
    (Nonempty (RowBumpLocation T row x)) ∨
      Nonempty (RowAppendLocation T row x) := by
  classical
  by_cases h :
      ∃ j : ℕ, j < μ.rowLen row ∧ x.val < T.T row j
  · let j₀ := Nat.find h
    have hj₀ : j₀ < μ.rowLen row ∧ x.val < T.T row j₀ :=
      Nat.find_spec h
    left
    refine ⟨{
      col := j₀
      cell_mem := ?_
      entry_gt := hj₀.2
      left_le := ?_ }⟩
    · rw [YoungDiagram.mem_iff_lt_rowLen]
      exact hj₀.1
    · intro j hj _hcell
      have hnot : ¬ (j < μ.rowLen row ∧ x.val < T.T row j) :=
        Nat.find_min h hj
      have hnlt : ¬ x.val < T.T row j := by
        intro hxlt
        exact hnot ⟨lt_trans hj hj₀.1, hxlt⟩
      exact le_of_not_gt hnlt
  · right
    refine ⟨{
      col := μ.rowLen row
      col_eq_rowLen := rfl
      row_entries_le := ?_ }⟩
    intro j hj
    have hnlt : ¬ x.val < T.T row j := by
      intro hxlt
      exact h ⟨j, hj, hxlt⟩
    exact le_of_not_gt hnlt

theorem rowBumpLocation_col_le_of_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (hxy : x ≤ y) (Lx : RowBumpLocation T row x)
    (Ly : RowBumpLocation T row y) :
    Lx.col ≤ Ly.col := by
  by_contra hnot
  have hy_lt_xcol : Ly.col < Lx.col := Nat.lt_of_not_ge hnot
  have hcell_y : (row, Ly.col) ∈ μ := Ly.cell_mem
  have hle_x : T.T row Ly.col ≤ x.val := Lx.left_le hy_lt_xcol hcell_y
  have hx_le_y : x.val ≤ y.val := hxy
  have hle_y : T.T row Ly.col ≤ y.val := le_trans hle_x hx_le_y
  exact not_lt_of_ge hle_y Ly.entry_gt

theorem rowBumpLocation_col_lt_append {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (Lx : RowBumpLocation T row x) (Ay : RowAppendLocation T row y) :
    Lx.col < Ay.col := by
  rw [Ay.col_eq_rowLen]
  exact Lx.col_lt_rowLen

theorem rowAppendLocation_col_le_append {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (Ax : RowAppendLocation T row x) (Ay : RowAppendLocation T row y) :
    Ax.col ≤ Ay.col := by
  rw [Ax.col_eq_rowLen, Ay.col_eq_rowLen]

theorem not_rowBumpLocation_of_append_of_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (hxy : x ≤ y) (Ax : RowAppendLocation T row x) :
    ¬ Nonempty (RowBumpLocation T row y) := by
  rintro ⟨Ly⟩
  have hy_lt_rowLen : Ly.col < μ.rowLen row := Ly.col_lt_rowLen
  have hle_x : T.T row Ly.col ≤ x.val := Ax.row_entries_le hy_lt_rowLen
  have hle_y : T.T row Ly.col ≤ y.val := le_trans hle_x hxy
  exact not_lt_of_ge hle_y Ly.entry_gt

theorem rowBumpStep_col_lt_next_bump_of_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (hxy : x ≤ y) (B : RowBumpStepResult T row x)
    (Ly : RowBumpLocation B.tableau row y) :
    B.col < Ly.col := by
  by_contra hnot
  have hle_col : Ly.col ≤ B.col := Nat.le_of_not_gt hnot
  have hentry_le_y : B.tableau.T row Ly.col ≤ y.val := by
    rcases lt_or_eq_of_le hle_col with hlt | heq
    · rw [B.unchanged_of_ne]
      · exact le_trans (B.left_le hlt Ly.cell_mem) hxy
      · intro hp
        have hcol : Ly.col = B.col := congrArg Prod.snd hp
        omega
    · rw [show Ly.col = B.col by exact heq, B.replaced_entry]
      exact hxy
  exact not_lt_of_ge hentry_le_y Ly.entry_gt

theorem rowBumpStep_col_lt_next_append {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (B : RowBumpStepResult T row x)
    (Ay : RowAppendLocation B.tableau row y) :
    B.col < Ay.col := by
  rw [Ay.col_eq_rowLen]
  exact B.location.col_lt_rowLen

theorem rowBumpStep_col_lt_next_step_of_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (hxy : x ≤ y) (B : RowBumpStepResult T row x) :
    (∀ Ly : RowBumpLocation B.tableau row y, B.col < Ly.col) ∧
      (∀ Ay : RowAppendLocation B.tableau row y, B.col < Ay.col) := by
  exact ⟨rowBumpStep_col_lt_next_bump_of_le hxy B,
    rowBumpStep_col_lt_next_append B⟩

/-- The shape-changing result of appending the inserted value at the end of one row. -/
structure RowAppendStepResult {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (x : Fin N) where
  location : RowAppendLocation T row x
  result : RowInsertResult N μ
  newCell_eq : result.newCell = (row, μ.rowLen row)
  inserted_entry : result.tableau.T row (μ.rowLen row) = x.val
  unchanged_on_old_shape :
    ∀ {i j : ℕ}, (i, j) ∈ μ → result.tableau.T i j = T.T i j

namespace RowAppendStepResult

def appendEntry {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (newCell : ℕ × ℕ) (x : Fin N) : ℕ → ℕ → ℕ :=
  fun i j => if (i, j) = newCell then x.val else T.T i j

theorem appendEntry_newCell {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (newCell : ℕ × ℕ) (x : Fin N) :
    appendEntry T newCell x newCell.1 newCell.2 = x.val := by
  simp [appendEntry]

theorem appendEntry_ne {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (newCell : ℕ × ℕ) (x : Fin N)
    {i j : ℕ} (h : (i, j) ≠ newCell) :
    appendEntry T newCell x i j = T.T i j := by
  simp [appendEntry, h]

noncomputable def appendTableau {N : ℕ} {μ ν : YoungDiagram}
    (T : BoundedSSYT μ N) (newCell : ℕ × ℕ) (x : Fin N)
    (hext : ExtendsByCell μ ν newCell)
    (hnot : newCell ∉ μ)
    (hleft : ∀ {j : ℕ}, j < newCell.2 → (newCell.1, j) ∈ μ →
      T.T newCell.1 j ≤ x.val)
    (habove : ∀ {i : ℕ}, i < newCell.1 → (i, newCell.2) ∈ μ →
      T.T i newCell.2 < x.val) :
    BoundedSSYT ν N where
  T :=
    { entry := appendEntry T newCell x
      row_weak' := by
        intro (i : ℕ) (j₁ : ℕ) (j₂ : ℕ) hj hcell₂
        have hcell₂_split : (i, j₂) ∈ μ ∨ (i, j₂) = newCell := (hext (i, j₂)).1 hcell₂
        by_cases h₂ : ((i, j₂) : ℕ × ℕ) = newCell
        · have hi : i = newCell.1 := congrArg Prod.fst h₂
          have hj₂eq : j₂ = newCell.2 := congrArg Prod.snd h₂
          subst i
          subst j₂
          rw [appendEntry_newCell]
          have hcell₁μ : (newCell.1, j₁) ∈ μ := by
            have hcell₁ν : (newCell.1, j₁) ∈ ν :=
              ν.up_left_mem le_rfl (Nat.le_of_lt hj) hcell₂
            rcases (hext (newCell.1, j₁)).1 hcell₁ν with hμ | heq
            · exact hμ
            · exact False.elim (Nat.ne_of_lt hj (congrArg Prod.snd heq))
          rw [appendEntry_ne]
          · exact hleft hj hcell₁μ
          · intro hp
            exact hnot (by simpa [hp] using hcell₁μ)
        · rw [appendEntry_ne _ _ _ h₂]
          by_cases h₁ : ((i, j₁) : ℕ × ℕ) = newCell
          · have hi : i = newCell.1 := congrArg Prod.fst h₁
            have hj₁eq : j₁ = newCell.2 := congrArg Prod.snd h₁
            subst i
            subst j₁
            exact False.elim (by
              rcases hcell₂_split with hμ | heq
              · have hj₂lt : j₂ < newCell.2 := by
                  rw [YoungDiagram.mem_iff_lt_rowLen] at hμ
                  rw [ExtendsByCell.old_rowLen_at_newCell hext hnot] at hμ
                  exact hμ
                omega
              · exact h₂ heq)
          · rw [appendEntry_ne _ _ _ h₁]
            rcases hcell₂_split with hcell₂μ | hcell₂eq
            · exact T.T.row_weak hj hcell₂μ
            · exact False.elim (h₂ hcell₂eq)
      col_strict' := by
        intro (i₁ : ℕ) (i₂ : ℕ) (j : ℕ) hi hcell₂
        have hcell₂_split : (i₂, j) ∈ μ ∨ (i₂, j) = newCell := (hext (i₂, j)).1 hcell₂
        by_cases h₂ : ((i₂, j) : ℕ × ℕ) = newCell
        · have hi₂eq : i₂ = newCell.1 := congrArg Prod.fst h₂
          have hjeq : j = newCell.2 := congrArg Prod.snd h₂
          subst i₂
          subst j
          rw [appendEntry_newCell]
          have hcell₁μ : (i₁, newCell.2) ∈ μ := by
            have hcell₁ν : (i₁, newCell.2) ∈ ν :=
              ν.up_left_mem (Nat.le_of_lt hi) le_rfl hcell₂
            rcases (hext (i₁, newCell.2)).1 hcell₁ν with hμ | heq
            · exact hμ
            · exact False.elim (Nat.ne_of_lt hi (congrArg Prod.fst heq))
          rw [appendEntry_ne]
          · exact habove hi hcell₁μ
          · intro hp
            exact hnot (by simpa [hp] using hcell₁μ)
        · rw [appendEntry_ne _ _ _ h₂]
          by_cases h₁ : ((i₁, j) : ℕ × ℕ) = newCell
          · have hi₁eq : i₁ = newCell.1 := congrArg Prod.fst h₁
            have hjeq : j = newCell.2 := congrArg Prod.snd h₁
            subst i₁
            subst j
            exact False.elim (by
              rcases hcell₂_split with hμ | heq
              · have hi₂lt : i₂ < newCell.1 := by
                  rw [YoungDiagram.mem_iff_lt_colLen] at hμ
                  rw [ExtendsByCell.old_colLen_at_newCell hext hnot] at hμ
                  exact hμ
                omega
              · exact h₂ heq)
          · rw [appendEntry_ne _ _ _ h₁]
            rcases hcell₂_split with hcell₂μ | hcell₂eq
            · exact T.T.col_strict hi hcell₂μ
            · exact False.elim (h₂ hcell₂eq)
      zeros' := by
        intro i j hnotν
        rw [appendEntry_ne]
        · exact T.T.zeros (by
            intro hμ
            exact hnotν ((hext (i, j)).2 (Or.inl hμ)))
        · intro heq
          exact hnotν (by
            rw [heq]
            exact ExtendsByCell.new_mem hext) }
  bound := by
    intro i j hmem
    change appendEntry T newCell x i j < N
    by_cases h : ((i, j) : ℕ × ℕ) = newCell
    · have hi : i = newCell.1 := congrArg Prod.fst h
      have hj : j = newCell.2 := congrArg Prod.snd h
      subst i
      subst j
      rw [appendEntry_newCell]
      exact x.isLt
    · rw [appendEntry_ne _ _ _ h]
      rcases (hext (i, j)).1 hmem with hμ | heq
      · exact T.bound hμ
      · exact False.elim (h heq)

noncomputable def construct {N : ℕ} {μ ν : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (x : Fin N)
    (A : RowAppendLocation T row x)
    (hext : ExtendsByCell μ ν (row, μ.rowLen row))
    (hnot : (row, μ.rowLen row) ∉ μ)
    (hadd : IsAddableCorner μ (row, μ.rowLen row))
    (hremove : IsRemovableCorner ν (row, μ.rowLen row))
    (habove : ∀ {i : ℕ}, i < row → (i, μ.rowLen row) ∈ μ →
      T.T i (μ.rowLen row) < x.val) :
    RowAppendStepResult T row x where
  location := A
  result :=
    { shape := ν
      tableau := appendTableau T (row, μ.rowLen row) x hext hnot
        (fun hj _ => A.row_entries_le hj) habove
      newCell := (row, μ.rowLen row)
      old_subset := fun c hc => ExtendsByCell.old_subset hext hc
      newCell_mem := ExtendsByCell.new_mem hext
      newCell_not_mem_old := hnot
      shape_mem_iff := hext
      newCell_addable := hadd
      newCell_removable := hremove
      card_eq := ExtendsByCell.card_eq hext hnot }
  newCell_eq := rfl
  inserted_entry := appendEntry_newCell T (row, μ.rowLen row) x
  unchanged_on_old_shape := by
    intro i j hμ
    exact appendEntry_ne T (row, μ.rowLen row) x (by
      intro heq
      exact hnot (by simpa [heq] using hμ))

/-- Construct the append step from the intrinsic addability criterion for the row end. -/
noncomputable def constructOfAbove {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (x : Fin N)
    (A : RowAppendLocation T row x)
    (hcorner : row = 0 ∨ (row - 1, μ.rowLen row) ∈ μ)
    (habove : ∀ {i : ℕ}, i < row → (i, μ.rowLen row) ∈ μ →
      T.T i (μ.rowLen row) < x.val) :
    RowAppendStepResult T row x := by
  classical
  let hadd : IsAddableCorner μ (row, μ.rowLen row) :=
    IsAddableCorner.row_rowLen hcorner
  let ν := (IsAddableCorner.exists_extension hadd).choose
  let hdata := (IsAddableCorner.exists_extension hadd).choose_spec
  exact construct T row x A hdata.1 hdata.2.1 hadd
    ⟨hdata.2.2, μ, hdata.2.1, hdata.1⟩ habove

theorem result_newCell_row {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (A : RowAppendStepResult T row x) :
    A.result.newCell.1 = row := by
  rw [A.newCell_eq]

theorem result_newCell_col {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (A : RowAppendStepResult T row x) :
    A.result.newCell.2 = μ.rowLen row := by
  rw [A.newCell_eq]

theorem unchanged_of_row_ne {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (A : RowAppendStepResult T row x) {i j : ℕ} (hi : i ≠ row) :
    A.result.tableau.T i j = T.T i j := by
  by_cases hμ : (i, j) ∈ μ
  · exact A.unchanged_on_old_shape hμ
  · have hresult : (i, j) ∉ A.result.shape := by
      intro hcell
      rcases (A.result.shape_mem_iff (i, j)).1 hcell with hold | hnew
      · exact hμ hold
      · exact hi (by simpa [A.newCell_eq] using congrArg Prod.fst hnew)
    rw [A.result.tableau.T.zeros hresult, T.T.zeros hμ]

theorem result_card_eq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (A : RowAppendStepResult T row x) :
    A.result.shape.card = μ.card + 1 :=
  A.result.card_eq_of_shape_mem_iff

theorem rowAppendStep_newCell_col_lt_next_append_of_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N} (A : RowAppendStepResult T row x)
    (Ay : RowAppendLocation A.result.tableau row y) :
    A.result.newCell.2 < Ay.col := by
  have hrow : A.result.newCell.1 = row := A.result_newCell_row
  have hcol : A.result.newCell.2 = μ.rowLen row := A.result_newCell_col
  rw [Ay.col_eq_rowLen, hcol]
  have hrowLen_new : A.result.shape.rowLen row = μ.rowLen row + 1 := by
    simpa [hrow] using A.result.rowLen_at_newCell
  rw [hrowLen_new]
  omega

theorem not_rowBumpLocation_after_appendStep_of_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (hxy : x ≤ y) (A : RowAppendStepResult T row x) :
    ¬ Nonempty (RowBumpLocation A.result.tableau row y) := by
  rintro ⟨L⟩
  have hentry_le : A.result.tableau.T row L.col ≤ y.val := by
    rcases (A.result.shape_mem_iff (row, L.col)).1 L.cell_mem with hold | hnew
    · have hcol_lt : L.col < μ.rowLen row := by
        rwa [YoungDiagram.mem_iff_lt_rowLen] at hold
      rw [A.unchanged_on_old_shape hold]
      exact le_trans (A.location.row_entries_le hcol_lt) hxy
    · have hcol : L.col = μ.rowLen row := by
        have hnew' : (row, L.col) = (row, μ.rowLen row) := by
          simpa [A.newCell_eq] using hnew
        exact congrArg Prod.snd hnew'
      rw [hcol, A.inserted_entry]
      exact hxy
  exact not_lt_of_ge hentry_le L.entry_gt

theorem result_eq_of_same {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (A B : RowAppendStepResult T row x) :
    A.result = B.result := by
  have hcell : A.result.newCell = B.result.newCell := by
    rw [A.newCell_eq, B.newCell_eq]
  have hshape : A.result.shape = B.result.shape := by
    ext c
    calc
      c ∈ A.result.shape ↔ c ∈ μ ∨ c = A.result.newCell :=
        A.result.shape_mem_iff c
      _ ↔ c ∈ μ ∨ c = B.result.newCell := by rw [hcell]
      _ ↔ c ∈ B.result.shape := (B.result.shape_mem_iff c).symm
  have htableau : HEq A.result.tableau B.result.tableau := by
    apply BoundedSSYT.heq_of_entry_eq hshape
    intro i j
    by_cases hμ : (i, j) ∈ μ
    · rw [A.unchanged_on_old_shape hμ, B.unchanged_on_old_shape hμ]
    · by_cases hnewA : ((i, j) : ℕ × ℕ) = A.result.newCell
      · have hnewB : ((i, j) : ℕ × ℕ) = B.result.newCell := by
          simpa [hcell] using hnewA
        calc
          A.result.tableau.T i j =
              A.result.tableau.T A.result.newCell.1 A.result.newCell.2 := by
                rw [show i = A.result.newCell.1 from congrArg Prod.fst hnewA,
                  show j = A.result.newCell.2 from congrArg Prod.snd hnewA]
          _ = x.val := by
                rw [A.newCell_eq]
                exact A.inserted_entry
          _ = B.result.tableau.T B.result.newCell.1 B.result.newCell.2 := by
                rw [B.newCell_eq]
                exact B.inserted_entry.symm
          _ = B.result.tableau.T i j := by
                rw [show i = B.result.newCell.1 from congrArg Prod.fst hnewB,
                  show j = B.result.newCell.2 from congrArg Prod.snd hnewB]
      · have hnewB : ((i, j) : ℕ × ℕ) ≠ B.result.newCell := by
          intro h
          exact hnewA (by simpa [hcell] using h)
        have hnotA : (i, j) ∉ A.result.shape := by
          intro h
          rcases (A.result.shape_mem_iff (i, j)).1 h with hold | hnew
          · exact hμ hold
          · exact hnewA hnew
        have hnotB : (i, j) ∉ B.result.shape := by
          intro h
          rcases (B.result.shape_mem_iff (i, j)).1 h with hold | hnew
          · exact hμ hold
          · exact hnewB hnew
        rw [A.result.tableau.T.zeros hnotA, B.result.tableau.T.zeros hnotB]
  exact RowInsertResult.ext_heq hshape htableau hcell

end RowAppendStepResult

/-- A full row insertion trace starting in a given row.

Each bump step keeps the same shape and passes the bumped value to the next row.
The trace terminates with an append step, which contributes the final new cell. -/
inductive RowInsertionTrace (N : ℕ) {μ : YoungDiagram} :
    BoundedSSYT μ N → ℕ → Fin N → Type where
  | done {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
      (A : RowAppendStepResult T row x) :
      RowInsertionTrace N T row x
  | bump {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
      (B : RowBumpStepResult T row x)
      (tail : RowInsertionTrace N B.tableau (row + 1) B.bumped) :
      RowInsertionTrace N T row x

namespace RowInsertionTrace

/-- The final row-insertion result encoded by a bumping trace. -/
def result {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {x : Fin N} :
    RowInsertionTrace N T row x → RowInsertResult N μ
  | done A => A.result
  | bump _ tail => result tail

/-- Source labels transported in parallel with row insertion.  Labels are intentionally
independent of the tableau alphabet: Schensted arguments use insertion times as labels. -/
abbrev OriginLabels := ℕ → ℕ → Option ℕ

def OriginLabels.replace (labels : OriginLabels) (row col tag : ℕ) : OriginLabels :=
  fun i j => if (i, j) = (row, col) then some tag else labels i j

def OriginLabels.Valid (labels : OriginLabels) (μ : YoungDiagram) : Prop :=
  ∀ {i j : ℕ}, (i, j) ∈ μ → ∃ source, labels i j = some source

@[simp]
theorem OriginLabels.replace_same (labels : OriginLabels) (row col tag : ℕ) :
    labels.replace row col tag row col = some tag := by
  simp [OriginLabels.replace]

theorem OriginLabels.replace_ne (labels : OriginLabels) (row col tag : ℕ)
    {i j : ℕ} (h : (i, j) ≠ (row, col)) :
    labels.replace row col tag i j = labels i j := by
  simp [OriginLabels.replace, h]

/-- A row-insertion trace carrying source labels.  At a bump, the incoming source label
stays in the replaced cell and the old cell label follows the bumped value downward. -/
inductive TaggedRowInsertionTrace (N : ℕ) {μ : YoungDiagram} :
    {T : BoundedSSYT μ N} →
      (labels : OriginLabels) → (row : ℕ) → (x : Fin N) → (tag : ℕ) →
        RowInsertionTrace N T row x → Type
  | done {T : BoundedSSYT μ N} {labels : OriginLabels} {row : ℕ}
      {x : Fin N} {tag : ℕ} (A : RowAppendStepResult T row x) :
      TaggedRowInsertionTrace N labels row x tag (.done A)
  | bump {T : BoundedSSYT μ N} {labels : OriginLabels} {row : ℕ}
      {x : Fin N} {tag : ℕ} (B : RowBumpStepResult T row x)
      (tail : RowInsertionTrace N B.tableau (row + 1) B.bumped)
      (bumpedTag : ℕ)
      (hbumpedTag : labels row B.col = some bumpedTag)
      (taggedTail :
        TaggedRowInsertionTrace N (labels.replace row B.col tag) (row + 1)
          B.bumped bumpedTag tail) :
      TaggedRowInsertionTrace N labels row x tag (.bump B tail)

namespace TaggedRowInsertionTrace

/-- Final source labels obtained by following a tagged insertion trace. -/
def resultLabels {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {labels : OriginLabels} {row : ℕ} {x : Fin N} {tag : ℕ}
    {tr : RowInsertionTrace N T row x} :
    TaggedRowInsertionTrace N labels row x tag tr → OriginLabels
  | .done A => labels.replace A.result.newCell.1 A.result.newCell.2 tag
  | .bump _ _ _ _ taggedTail => taggedTail.resultLabels

/-- Every ordinary insertion trace has a canonical parallel source-label trace. -/
noncomputable def ofTrace {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    (labels : OriginLabels) {row : ℕ} {x : Fin N} (tag : ℕ)
    (tr : RowInsertionTrace N T row x)
    (hlabels : labels.Valid μ) :
    TaggedRowInsertionTrace N labels row x tag tr :=
  match tr with
  | .done A => .done A
  | .bump B tail =>
      let bumpedTag := (hlabels B.cell_mem).choose
      .bump B tail bumpedTag (hlabels B.cell_mem).choose_spec
        (ofTrace (labels.replace row B.col tag) bumpedTag tail (by
          intro i j hcell
          by_cases h : (i, j) = (row, B.col)
          · exact ⟨tag, by simp [OriginLabels.replace, h]⟩
          · rcases hlabels hcell with ⟨source, hsource⟩
            exact ⟨source, by simpa [OriginLabels.replace_ne labels row B.col tag h]⟩))

theorem valid_resultLabels {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {labels : OriginLabels} {row : ℕ} {x : Fin N} {tag : ℕ}
    {tr : RowInsertionTrace N T row x}
    (tagged : TaggedRowInsertionTrace N labels row x tag tr)
    (hvalid : labels.Valid μ) :
    tagged.resultLabels.Valid tr.result.shape := by
  induction tagged with
  | done A =>
      rename_i T₀ labels₀ row₀ x₀ tag₀
      intro i j hcell
      rcases (A.result.shape_mem_iff (i, j)).1 hcell with hold | hnew
      · rcases hvalid hold with ⟨source, hsource⟩
        refine ⟨source, ?_⟩
        change OriginLabels.replace labels₀ A.result.newCell.1 A.result.newCell.2 tag₀ i j =
          some source
        rw [OriginLabels.replace_ne]
        · exact hsource
        · intro heq
          exact A.result.newCell_not_mem_old (by simpa [heq] using hold)
      · refine ⟨tag₀, ?_⟩
        change OriginLabels.replace labels₀ A.result.newCell.1 A.result.newCell.2 tag₀ i j =
          some tag₀
        simp [OriginLabels.replace, hnew]
  | bump B tail bumpedTag hbumpedTag taggedTail ih =>
      rename_i T₀ labels₀ row₀ x₀ tag₀
      apply ih
      intro i j hcell
      by_cases h : (i, j) = (row₀, B.col)
      · exact ⟨tag₀, by simp [OriginLabels.replace, h]⟩
      · rcases hvalid hcell with ⟨source, hsource⟩
        exact ⟨source, by simpa [OriginLabels.replace_ne labels₀ row₀ B.col tag₀ h]⟩

theorem resultLabels_eq_of_row_lt {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {labels : OriginLabels} {row : ℕ} {x : Fin N} {tag : ℕ}
    {tr : RowInsertionTrace N T row x}
    (tagged : TaggedRowInsertionTrace N labels row x tag tr)
    {i j : ℕ} (hi : i < row) :
    tagged.resultLabels i j = labels i j := by
  induction tagged with
  | done A =>
      rename_i T₀ labels₀ row₀ x₀ tag₀
      rw [resultLabels, OriginLabels.replace_ne]
      intro h
      have hrow : i = row₀ := by
        calc
          i = A.result.newCell.1 := congrArg Prod.fst h
          _ = row₀ := A.result_newCell_row
      omega
  | bump B tail bumpedTag hbumpedTag taggedTail ih =>
      rename_i T₀ labels₀ row₀ x₀ tag₀
      change taggedTail.resultLabels i j = labels₀ i j
      rw [ih (by omega)]
      exact OriginLabels.replace_ne _ _ _ _ (by
        intro h
        exact hi.ne (congrArg Prod.fst h))

end TaggedRowInsertionTrace

theorem exists_cast_of_heq {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {x : Fin N}
    (hμ : μ = ν) (hT : HEq T S)
    (tr : RowInsertionTrace N T row x) :
    ∃ trS : RowInsertionTrace N S row x, HEq trS tr := by
  subst ν
  have hT_eq : T = S := eq_of_heq hT
  subst S
  exact ⟨tr, HEq.rfl⟩

noncomputable def castOfHEq {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {x : Fin N}
    (hμ : μ = ν) (hT : HEq T S)
    (tr : RowInsertionTrace N T row x) :
    RowInsertionTrace N S row x :=
  Classical.choose (exists_cast_of_heq hμ hT tr)

theorem castOfHEq_heq {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {x : Fin N}
    (hμ : μ = ν) (hT : HEq T S)
    (tr : RowInsertionTrace N T row x) :
    HEq (castOfHEq hμ hT tr) tr :=
  Classical.choose_spec (exists_cast_of_heq hμ hT tr)

theorem castOfHEq_result_eq {N : ℕ} {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (hT : HEq T S)
    (tr : RowInsertionTrace N T row x) :
    (castOfHEq (rfl : μ = μ) hT tr).result = tr.result := by
  have hEq : T = S := eq_of_heq hT
  subst S
  simp [castOfHEq]

def castValue {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (h : x = y) (tr : RowInsertionTrace N T row y) :
    RowInsertionTrace N T row x := by
  cases h
  exact tr

theorem castValue_result_eq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (h : x = y) (tr : RowInsertionTrace N T row y) :
    (castValue h tr).result = tr.result := by
  cases h
  rfl

def castRow {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row row' : ℕ} {x : Fin N}
    (h : row = row') (tr : RowInsertionTrace N T row' x) :
    RowInsertionTrace N T row x := by
  cases h
  exact tr

theorem castRow_result_eq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row row' : ℕ} {x : Fin N}
    (h : row = row') (tr : RowInsertionTrace N T row' x) :
    (castRow h tr).result = tr.result := by
  cases h
  rfl

theorem result_card_eq {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {x : Fin N} (tr : RowInsertionTrace N T row x) :
    tr.result.shape.card = μ.card + 1 :=
  tr.result.card_eq_of_shape_mem_iff

theorem result_extendsByCell {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {x : Fin N} (tr : RowInsertionTrace N T row x) :
    ExtendsByCell μ tr.result.shape tr.result.newCell :=
  tr.result.extendsByCell

theorem result_newCell_row_ge {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {x : Fin N} (tr : RowInsertionTrace N T row x) :
    row ≤ tr.result.newCell.1 := by
  induction tr with
  | done A =>
      simpa [RowInsertionTrace.result] using (A.result_newCell_row).ge
  | bump B tail ih =>
      exact le_trans (Nat.le_succ _) ih

theorem result_tableau_eq_of_row_lt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (tr : RowInsertionTrace N T row x) {i j : ℕ}
    (hi : i < row) (hcell : (i, j) ∈ μ) :
    tr.result.tableau.T i j = T.T i j := by
  cases tr with
  | done A =>
      simpa [RowInsertionTrace.result] using A.unchanged_on_old_shape hcell
  | bump B tail =>
      calc
        (RowInsertionTrace.bump B tail).result.tableau.T i j = tail.result.tableau.T i j := rfl
        _ = B.tableau.T i j :=
          result_tableau_eq_of_row_lt tail (by omega) hcell
        _ = T.T i j := RowBumpStepResult.unchanged_of_row_ne B (Nat.ne_of_lt hi)
termination_by sizeOf tr

namespace TaggedRowInsertionTrace

/-- The source tag entering a trace remains attached to an entry carrying the inserted
value.  Later bumps may move older tags downward, but they never erase this source. -/
theorem exists_resultLabels_eq_tag_and_entry_eq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {labels : OriginLabels} {row : ℕ} {x : Fin N} {tag : ℕ}
    {tr : RowInsertionTrace N T row x}
    (tagged : TaggedRowInsertionTrace N labels row x tag tr) :
    ∃ c ∈ tr.result.shape,
      tagged.resultLabels c.1 c.2 = some tag ∧ tr.result.tableau.T c.1 c.2 = x.val := by
  cases tagged with
  | done A =>
      refine ⟨A.result.newCell, A.result.newCell_mem, ?_, ?_⟩
      · simp [resultLabels, OriginLabels.replace]
      · simpa [A.newCell_eq] using A.inserted_entry
  | bump B tail bumpedTag hbumpedTag taggedTail =>
      refine ⟨(row, B.col), tail.result.old_subset (row, B.col) B.cell_mem, ?_, ?_⟩
      · calc
          taggedTail.resultLabels row B.col =
              (labels.replace row B.col tag) row B.col :=
            taggedTail.resultLabels_eq_of_row_lt (by omega)
          _ = some tag := OriginLabels.replace_same labels row B.col tag
      · calc
          tail.result.tableau.T row B.col = B.tableau.T row B.col :=
            tail.result_tableau_eq_of_row_lt (by omega) B.cell_mem
          _ = x.val := B.replaced_entry

theorem exists_resultLabels_eq_of_old_entry {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {labels : OriginLabels} {row : ℕ} {x : Fin N} {tag : ℕ}
    {tr : RowInsertionTrace N T row x}
    (tagged : TaggedRowInsertionTrace N labels row x tag tr)
    {c : ℕ × ℕ} (hcell : c ∈ μ) {source value : ℕ}
    (hsource : labels c.1 c.2 = some source)
    (hvalue : T.T c.1 c.2 = value) :
    ∃ d ∈ tr.result.shape,
      tagged.resultLabels d.1 d.2 = some source ∧ tr.result.tableau.T d.1 d.2 = value := by
  induction tagged with
  | done A =>
      rename_i T₀ labels₀ row₀ x₀ tag₀
      refine ⟨c, A.result.old_subset c hcell, ?_, ?_⟩
      · change labels₀.replace A.result.newCell.1 A.result.newCell.2 tag₀ c.1 c.2 =
          some source
        exact (OriginLabels.replace_ne labels₀ A.result.newCell.1
          A.result.newCell.2 tag₀ (by
            intro heq
            apply A.result.newCell_not_mem_old
            have hc_eq : c = A.result.newCell := by
              simpa using heq
            simpa [← hc_eq] using hcell)).trans hsource
      · exact (A.unchanged_on_old_shape hcell).trans hvalue
  | bump B tail bumpedTag hbumpedTag taggedTail ih =>
      rename_i T₀ labels₀ row₀ x₀ tag₀
      by_cases hc : c = (row₀, B.col)
      · have hsource_eq : source = bumpedTag := by
          apply Option.some.inj
          calc
            some source = labels₀ c.1 c.2 := hsource.symm
            _ = labels₀ row₀ B.col := by rw [hc]
            _ = some bumpedTag := hbumpedTag
        subst source
        have hbumped_value : B.bumped.val = value := by
          calc
            B.bumped.val = T₀.T row₀ B.col := B.bumped_eq.symm
            _ = T₀.T c.1 c.2 := by rw [hc]
            _ = value := hvalue
        simpa [hbumped_value] using
          taggedTail.exists_resultLabels_eq_tag_and_entry_eq
      · apply ih
        · rw [OriginLabels.replace_ne]
          · exact hsource
          · simpa using hc
        · exact (B.unchanged_of_ne (by simpa using hc)).trans hvalue

end TaggedRowInsertionTrace

theorem result_rowLen_eq_of_row_lt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (tr : RowInsertionTrace N T row x) {i : ℕ} (hi : i < row) :
    tr.result.shape.rowLen i = μ.rowLen i := by
  exact tr.result.rowLen_eq_of_ne (by
    intro h
    have hge := tr.result_newCell_row_ge
    omega)

theorem result_eq_of_same {N : ℕ} {μ : YoungDiagram} :
    ∀ {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
      (tr₁ tr₂ : RowInsertionTrace N T row x),
      tr₁.result = tr₂.result := by
  intro T row x tr₁
  induction tr₁ with
  | done A₁ =>
      rename_i T₀ row₀ x₀
      intro tr₂
      cases tr₂ with
      | done A₂ =>
          exact RowAppendStepResult.result_eq_of_same A₁ A₂
      | bump B₂ _ =>
          exact False.elim
            ((not_lt_of_ge (A₁.location.row_entries_le B₂.location.col_lt_rowLen))
              B₂.entry_gt)
  | bump B₁ tail₁ ih =>
      rename_i T₀ row₀ x₀
      intro tr₂
      cases tr₂ with
      | done A₂ =>
          exact False.elim
            ((not_lt_of_ge (A₂.location.row_entries_le B₁.location.col_lt_rowLen))
              B₁.entry_gt)
      | bump B₂ tail₂ =>
          have hcol : B₁.col = B₂.col := by
            exact le_antisymm
              (rowBumpLocation_col_le_of_le le_rfl B₁.location B₂.location)
              (rowBumpLocation_col_le_of_le le_rfl B₂.location B₁.location)
          have hbumped : B₁.bumped = B₂.bumped := by
            apply Fin.ext
            rw [← B₁.bumped_eq, ← B₂.bumped_eq, hcol]
          have htableau : B₁.tableau = B₂.tableau := by
            apply BoundedSSYT.ext
            intro i j
            by_cases hcell₁ : ((i, j) : ℕ × ℕ) = (row₀, B₁.col)
            · have hcell₂ : ((i, j) : ℕ × ℕ) = (row₀, B₂.col) := by
                simpa [hcol] using hcell₁
              have hi : i = row₀ := congrArg Prod.fst hcell₁
              have hj : j = B₁.col := congrArg Prod.snd hcell₁
              subst i
              subst j
              calc
                B₁.tableau.T row₀ B₁.col = x₀.val := B₁.replaced_entry
                _ = B₂.tableau.T row₀ B₁.col := by
                  simpa [hcol] using B₂.replaced_entry.symm
            · have hcell₂ : ((i, j) : ℕ × ℕ) ≠ (row₀, B₂.col) := by
                intro h
                exact hcell₁ (by simpa [hcol] using h)
              calc
                B₁.tableau.T i j = T₀.T i j := B₁.unchanged_of_ne hcell₁
                _ = B₂.tableau.T i j := (B₂.unchanged_of_ne hcell₂).symm
          let tail₂m : RowInsertionTrace N B₂.tableau (row₀ + 1) B₁.bumped :=
            RowInsertionTrace.castValue hbumped tail₂
          let tail₂' : RowInsertionTrace N B₁.tableau (row₀ + 1) B₁.bumped :=
            RowInsertionTrace.castOfHEq (rfl : μ = μ) (heq_of_eq htableau.symm) tail₂m
          calc
            tail₁.result = tail₂'.result := ih tail₂'
            _ = tail₂m.result := RowInsertionTrace.castOfHEq_result_eq
              (heq_of_eq htableau.symm) tail₂m
            _ = tail₂.result := RowInsertionTrace.castValue_result_eq hbumped tail₂

end RowInsertionTrace

/-- Extract the final `RowInsertResult` from a complete row-insertion trace starting in row `0`. -/
def rowInsertFromTrace {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N)
    (tr : RowInsertionTrace N T 0 x) : RowInsertResult N μ :=
  tr.result

/-- Invariant carried by the row-insertion bumping path.

`cap` is the column of the previous bump, or the top-row length at the initial state.
The invariant says:
* entries above the current row and weakly left of `cap` are strictly below the value
  currently being inserted;
* if the current row still has a cell in column `cap`, that cell is strictly above the
  inserted value, so the next bump/append cannot pass to the right of `cap`;
* the previous row has the cap cell, except at the top row. -/
def RowInsertionPathInvariant {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row cap : ℕ) (x : Fin N) : Prop :=
  (∀ {i j : ℕ}, i < row → j ≤ cap → (i, j) ∈ μ → T.T i j < x.val) ∧
  (∀ {j : ℕ}, j = cap → (row, j) ∈ μ → x.val < T.T row j) ∧
  (row = 0 ∨ (row - 1, cap) ∈ μ)

namespace RowInsertionPathInvariant

theorem initial {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    RowInsertionPathInvariant T 0 (μ.rowLen 0) x := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi _ _
    omega
  · intro j hj hcell
    rw [hj, YoungDiagram.mem_iff_lt_rowLen] at hcell
    exact False.elim (Nat.lt_irrefl _ hcell)
  · exact Or.inl rfl

theorem bump_col_le_cap {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {x : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (L : RowBumpLocation T row x) :
    L.col ≤ cap := by
  by_contra hnot
  have hcap_lt : cap < L.col := Nat.lt_of_not_ge hnot
  have hcap_mem : (row, cap) ∈ μ :=
    μ.up_left_mem le_rfl (Nat.le_of_lt hcap_lt) L.cell_mem
  have hgt : x.val < T.T row cap := hinv.2.1 rfl hcap_mem
  have hle : T.T row cap ≤ x.val := L.left_le hcap_lt hcap_mem
  omega

theorem bump_habove {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {x : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (L : RowBumpLocation T row x) :
    ∀ {i : ℕ}, i < row → (i, L.col) ∈ μ → T.T i L.col < x.val := by
  intro i hi hcell
  exact hinv.1 hi (bump_col_le_cap hinv L) hcell

theorem append_rowLen_le_cap {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {x : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (A : RowAppendLocation T row x) :
    μ.rowLen row ≤ cap := by
  by_contra hnot
  have hcap_lt : cap < μ.rowLen row := Nat.lt_of_not_ge hnot
  have hcap_mem : (row, cap) ∈ μ := by
    rw [YoungDiagram.mem_iff_lt_rowLen]
    exact hcap_lt
  have hgt : x.val < T.T row cap := hinv.2.1 rfl hcap_mem
  have hle : T.T row cap ≤ x.val := A.row_entries_le hcap_lt
  omega

theorem append_corner {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {x : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (A : RowAppendLocation T row x) :
    row = 0 ∨ (row - 1, μ.rowLen row) ∈ μ := by
  rcases hinv.2.2 with hrow | hprev
  · exact Or.inl hrow
  · right
    exact μ.up_left_mem le_rfl (append_rowLen_le_cap hinv A) hprev

theorem append_habove {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {x : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (A : RowAppendLocation T row x) :
    ∀ {i : ℕ}, i < row → (i, μ.rowLen row) ∈ μ →
      T.T i (μ.rowLen row) < x.val := by
  intro i hi hcell
  exact hinv.1 hi (append_rowLen_le_cap hinv A) hcell

theorem next_after_bump {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {x : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (L : RowBumpLocation T row x) :
    let B := RowBumpStepResult.construct T row x L (bump_habove hinv L)
    RowInsertionPathInvariant B.tableau (row + 1) B.col B.bumped := by
  classical
  let B := RowBumpStepResult.construct T row x L (bump_habove hinv L)
  have hcol_le : B.col ≤ cap := by
    change L.col ≤ cap
    exact bump_col_le_cap hinv L
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj hcell
    have hi_cases : i < row ∨ i = row := by omega
    rcases hi_cases with hi_old | hi_eq
    · rw [RowBumpStepResult.unchanged_of_row_ne B (by omega)]
      exact lt_trans (hinv.1 hi_old (le_trans hj hcol_le) hcell)
        (RowBumpStepResult.bumped_gt B)
    · subst hi_eq
      by_cases hjcol : j = B.col
      · subst hjcol
        rw [B.replaced_entry]
        exact RowBumpStepResult.bumped_gt B
      · have hjlt : j < B.col := lt_of_le_of_ne hj hjcol
        rw [RowBumpStepResult.unchanged_of_ne B (by
          intro hp
          exact hjcol (congrArg Prod.snd hp))]
        exact lt_of_le_of_lt (B.left_le hjlt hcell) (RowBumpStepResult.bumped_gt B)
  · intro j hj hcell
    subst hj
    rw [RowBumpStepResult.unchanged_of_row_ne B (by omega)]
    rw [← B.bumped_eq]
    exact T.T.col_strict (by omega) hcell
  · exact Or.inr (by
      simpa using B.cell_mem)

/-- The bump-path invariant after an arbitrary bump step.

This is the trace-level form of `next_after_bump`; it avoids depending on the particular
constructor used to package the bump step. -/
theorem next_after_bump_step {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {x : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (B : RowBumpStepResult T row x) :
    RowInsertionPathInvariant B.tableau (row + 1) B.col B.bumped := by
  have hcol_le : B.col ≤ cap :=
    bump_col_le_cap hinv B.location
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj hcell
    have hi_cases : i < row ∨ i = row := by omega
    rcases hi_cases with hi_old | hi_eq
    · rw [RowBumpStepResult.unchanged_of_row_ne B (by omega)]
      exact lt_trans (hinv.1 hi_old (le_trans hj hcol_le) hcell)
        (RowBumpStepResult.bumped_gt B)
    · subst hi_eq
      by_cases hjcol : j = B.col
      · subst hjcol
        rw [B.replaced_entry]
        exact RowBumpStepResult.bumped_gt B
      · have hjlt : j < B.col := lt_of_le_of_ne hj hjcol
        rw [RowBumpStepResult.unchanged_of_ne B (by
          intro hp
          exact hjcol (congrArg Prod.snd hp))]
        exact lt_of_le_of_lt (B.left_le hjlt hcell) (RowBumpStepResult.bumped_gt B)
  · intro j hj hcell
    subst hj
    rw [RowBumpStepResult.unchanged_of_row_ne B (by omega)]
    rw [← B.bumped_eq]
    exact T.T.col_strict (by omega) hcell
  · exact Or.inr (by
      simpa using B.cell_mem)

/-- A complete row-insertion trace starting from a capped bump-path invariant appends
weakly to the left of that cap. -/
theorem trace_newCell_col_le_cap {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {x : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (tr : RowInsertionTrace N T row x) :
    tr.result.newCell.2 ≤ cap := by
  induction tr generalizing cap with
  | done A =>
      change A.result.newCell.2 ≤ cap
      rw [RowAppendStepResult.result_newCell_col A]
      exact append_rowLen_le_cap hinv A.location
  | bump B tail ih =>
      have hcol_le : B.col ≤ cap :=
        bump_col_le_cap hinv B.location
      have hinv' := next_after_bump_step hinv B
      exact le_trans (ih hinv') hcol_le

end RowInsertionPathInvariant

theorem RowBumpStepResult.pathInvariant_after_step {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) :
    RowInsertionPathInvariant B.tableau (row + 1) B.col B.bumped := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj hcell
    have hi_cases : i < row ∨ i = row := by omega
    rcases hi_cases with hi_old | rfl
    · rw [RowBumpStepResult.unchanged_of_row_ne B (by omega)]
      have hrow_cell : (row, j) ∈ μ :=
        μ.up_left_mem le_rfl hj B.cell_mem
      have hcol_lt : T.T i j < T.T row j :=
        T.T.col_strict hi_old hrow_cell
      have hrow_le : T.T row j ≤ T.T row B.col := by
        rcases lt_or_eq_of_le hj with hjlt | rfl
        · exact T.T.row_weak hjlt B.cell_mem
        · exact le_rfl
      rw [B.bumped_eq] at hrow_le
      exact lt_of_lt_of_le hcol_lt hrow_le
    · by_cases hjcol : j = B.col
      · subst j
        rw [B.replaced_entry]
        exact B.bumped_gt
      · have hjlt : j < B.col := lt_of_le_of_ne hj hjcol
        rw [RowBumpStepResult.unchanged_of_col_ne B hjcol]
        exact lt_of_le_of_lt (B.left_le hjlt hcell) B.bumped_gt
  · intro j hj hcell
    subst j
    rw [RowBumpStepResult.unchanged_of_row_ne B (by omega), ← B.bumped_eq]
    exact T.T.col_strict (by omega) hcell
  · exact Or.inr (by simpa using B.cell_mem)

/-- A right-hand lower-bound invariant for a row-insertion path.

The column `floor` is known to exist in every row at or below the current row, and every
entry weakly to its left in those rows is at most the current moving value. Consequently
the next bump or append must occur strictly to the right of `floor`. -/
def RowInsertionRightInvariant {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row floor : ℕ) (x : Fin N) : Prop :=
  (∀ {i j : ℕ}, row ≤ i → j ≤ floor → (i, j) ∈ μ → T.T i j ≤ x.val) ∧
  (∀ {i : ℕ}, row ≤ i → (i, floor) ∈ μ)

namespace RowInsertionRightInvariant

theorem bump_col_gt_floor {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row floor : ℕ} {x : Fin N}
    (hinv : RowInsertionRightInvariant T row floor x)
    (B : RowBumpStepResult T row x) :
    floor < B.col := by
  by_contra hnot
  have hcol_le : B.col ≤ floor := Nat.le_of_not_gt hnot
  have hle : T.T row B.col ≤ x.val := hinv.1 le_rfl hcol_le B.cell_mem
  exact not_lt_of_ge hle B.entry_gt

theorem append_col_gt_floor {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row floor : ℕ} {x : Fin N}
    (hinv : RowInsertionRightInvariant T row floor x)
    (A : RowAppendLocation T row x) :
    floor < A.col := by
  rw [A.col_eq_rowLen]
  have hcell : (row, floor) ∈ μ := hinv.2 le_rfl
  rwa [YoungDiagram.mem_iff_lt_rowLen] at hcell

theorem next_after_bump_step {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row floor : ℕ} {x : Fin N}
    (hinv : RowInsertionRightInvariant T row floor x)
    (B : RowBumpStepResult T row x) :
    RowInsertionRightInvariant B.tableau (row + 1) floor B.bumped := by
  refine ⟨?_, ?_⟩
  · intro i j hi hj hcell
    rw [RowBumpStepResult.unchanged_of_row_ne B (by omega)]
    exact le_trans (hinv.1 (by omega) hj hcell)
      (le_of_lt (RowBumpStepResult.bumped_gt B))
  · intro i hi
    exact hinv.2 (by omega)

/-- A complete row-insertion trace starting from a right-hand lower-bound invariant
appends strictly to the right of that lower-bound column. -/
theorem floor_lt_trace_newCell_col {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row floor : ℕ} {x : Fin N}
    (hinv : RowInsertionRightInvariant T row floor x)
    (tr : RowInsertionTrace N T row x) :
    floor < tr.result.newCell.2 := by
  induction tr generalizing floor with
  | done A =>
      change floor < A.result.newCell.2
      have hloc : floor < A.location.col := append_col_gt_floor hinv A.location
      simpa [A.result_newCell_col, A.location.col_eq_rowLen] using hloc
  | bump B tail ih =>
      have hinv' := next_after_bump_step hinv B
      exact ih hinv'

end RowInsertionRightInvariant

/-- Row insertion exists from any row satisfying the bump-path invariant. The recursion
terminates because every bump occurs in an existing cell, hence in a row below
`μ.colLen 0`, and the next recursive call moves to the following row. -/
theorem exists_rowInsertionTraceFromInvariant {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row cap : ℕ) (x : Fin N)
    (hinv : RowInsertionPathInvariant T row cap x) :
    Nonempty (RowInsertionTrace N T row x) := by
  classical
  rcases exists_rowBumpLocation_or_rowAppendLocation T row x with hbumps | happends
  · rcases hbumps with ⟨L⟩
    let B := RowBumpStepResult.construct T row x L
      (RowInsertionPathInvariant.bump_habove hinv L)
    have hinv' : RowInsertionPathInvariant B.tableau (row + 1) B.col B.bumped := by
      simpa [B] using RowInsertionPathInvariant.next_after_bump hinv L
    have htail : Nonempty (RowInsertionTrace N B.tableau (row + 1) B.bumped) :=
      exists_rowInsertionTraceFromInvariant B.tableau (row + 1) B.col B.bumped hinv'
    exact htail.elim (fun tail => ⟨RowInsertionTrace.bump B tail⟩)
  · rcases happends with ⟨A⟩
    let Astep := RowAppendStepResult.constructOfAbove T row x A
      (RowInsertionPathInvariant.append_corner hinv A)
      (RowInsertionPathInvariant.append_habove hinv A)
    exact ⟨RowInsertionTrace.done Astep⟩
termination_by μ.colLen 0 + 1 - row
decreasing_by
  have hrow_lt_col : row < μ.colLen L.col := by
    have hcell := L.cell_mem
    rwa [YoungDiagram.mem_iff_lt_colLen] at hcell
  have hrow_lt : row < μ.colLen 0 :=
    lt_of_lt_of_le hrow_lt_col (μ.colLen_anti 0 L.col (Nat.zero_le _))
  omega

/-- The actual row-insertion trace starting in row `0`.

It is built by iterating the single-row search step until the first append. -/
theorem exists_rowInsertionTrace {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) : Nonempty (RowInsertionTrace N T 0 x) := by
  exact exists_rowInsertionTraceFromInvariant T 0 (μ.rowLen 0) x
    (RowInsertionPathInvariant.initial T x)

/-- The actual row-insertion trace starting in row `0`.

The constructive content is isolated in `exists_rowInsertionTrace`; this definition packages
that existence result so downstream KRS interfaces can use a concrete trace. -/
noncomputable def rowInsertionTrace {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) : RowInsertionTrace N T 0 x :=
  Classical.choice (exists_rowInsertionTrace T x)

/-- The concrete trace chosen by `rowInsertionTrace` still carries the expected
one-cell extension of the original shape. -/
theorem rowInsertionTrace_result_extendsByCell {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    ExtendsByCell μ (rowInsertionTrace T x).result.shape
      (rowInsertionTrace T x).result.newCell :=
  RowInsertionTrace.result_extendsByCell (rowInsertionTrace T x)

/-- The concrete trace chosen by `rowInsertionTrace` adds exactly one cell. -/
theorem rowInsertionTrace_result_card_eq {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    (rowInsertionTrace T x).result.shape.card = μ.card + 1 :=
  RowInsertionTrace.result_card_eq (rowInsertionTrace T x)

/-- The original shape is contained in the final shape of the chosen insertion trace. -/
theorem rowInsertionTrace_result_old_subset {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    μ ≤ (rowInsertionTrace T x).result.shape :=
  (rowInsertionTrace T x).result.old_subset_of_shape_mem_iff

/-- Row insertion for bounded semistandard tableaux. -/
noncomputable def rowInsert {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) : RowInsertResult N μ :=
  rowInsertFromTrace T x (rowInsertionTrace T x)

theorem rowInsert_eq_trace_result {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    rowInsert T x = (rowInsertionTrace T x).result := rfl

theorem rowInsert_shape_eq_trace_shape {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    (rowInsert T x).shape = (rowInsertionTrace T x).result.shape := rfl

theorem rowInsert_tableau_eq_trace_tableau {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    (rowInsert T x).tableau = (rowInsertionTrace T x).result.tableau := rfl

theorem rowInsert_newCell_eq_trace_newCell {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    (rowInsert T x).newCell = (rowInsertionTrace T x).result.newCell := rfl

/-- Delete a removable corner and return the deleted entry.

This is only the first step of reverse row insertion. It deliberately is not named
`reverseRowInsert`: true reverse row insertion must continue with upward reverse bumping. -/
noncomputable def deleteCorner {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    ReverseRowInsertResult N μ c hc :=
  let μ' := (IsRemovableCorner.exists_deletion hc).choose
  let hdata := (IsRemovableCorner.exists_deletion hc).choose_spec
  have hext : ExtendsByCell μ' μ c := hdata.1
  have hnot : c ∉ μ' := hdata.2.1
  have hmem : c ∈ μ := hdata.2.2
  have hsub : μ' ≤ μ := ExtendsByCell.old_subset hext
  { shape := μ'
    tableau := restrictToSubshape T hsub
    value := ⟨T.T c.1 c.2, T.bound hmem⟩
    cell_mem_old := hmem
    cell_not_mem_shape := hnot
    shape_mem_iff := hext
    shape_addable := ⟨hnot, μ, hmem, hext⟩
    card_eq := ExtendsByCell.card_eq hext hnot }

theorem deleteCorner_tableau_entry {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    {i j : ℕ} (hcell : (i, j) ∈ (deleteCorner T c hc).shape) :
    (deleteCorner T c hc).tableau.T i j = T.T i j := by
  unfold deleteCorner
  simp only
  exact restrictToSubshape_entry T _ hcell

theorem deleteCorner_shape_eq_of_cell_eq {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hcd : c = d) :
    (deleteCorner T c hc).shape = (deleteCorner T d hd).shape := by
  cases hcd
  have hproof : hc = hd := Subsingleton.elim _ _
  cases hproof
  rfl

theorem deleteCorner_tableau_heq_of_cell_eq {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hcd : c = d) :
    HEq (deleteCorner T c hc).tableau (deleteCorner T d hd).tableau := by
  cases hcd
  have hproof : hc = hd := Subsingleton.elim _ _
  cases hproof
  exact HEq.rfl

theorem deleteCorner_value_eq_of_cell_eq {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hcd : c = d) :
    (deleteCorner T c hc).value = (deleteCorner T d hd).value := by
  cases hcd
  have hproof : hc = hd := Subsingleton.elim _ _
  cases hproof
  rfl

theorem RowInsertResult.deleteCorner_shape_inverse {N : ℕ} {μ : YoungDiagram}
    (R : RowInsertResult N μ) :
    (deleteCorner R.tableau R.newCell R.newCell_removable).shape = μ := by
  let D := deleteCorner R.tableau R.newCell R.newCell_removable
  ext c
  constructor
  · intro hcD
    have hcR : c ∈ R.shape := D.shape_subset_old hcD
    rcases (R.shape_mem_iff c).1 hcR with hμ | hnew
    · exact hμ
    · exact False.elim (D.cell_not_mem_shape (by simpa [hnew] using hcD))
  · intro hμ
    have hcR : c ∈ R.shape := R.old_subset c hμ
    rcases (D.shape_mem_iff c).1 hcR with hcD | hnew
    · exact hcD
    · exact False.elim (R.newCell_not_mem_old (by simpa [hnew] using hμ))

theorem deleteCorner_shape_mem_of_row_lt {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    {i j : ℕ} (hi : i < c.1) (hcell : (i, j) ∈ μ) :
    (i, j) ∈ (deleteCorner T c hc).shape := by
  have hne : ((i, j) : ℕ × ℕ) ≠ c := by
    intro hp
    have hi_eq : i = c.1 := congrArg Prod.fst hp
    omega
  exact ((deleteCorner T c hc).shape_mem_iff (i, j)).1 hcell |>.resolve_right hne

theorem deleteCorner_shape_mem_iff_of_row_lt {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    {i j : ℕ} (hi : i < c.1) :
    (i, j) ∈ (deleteCorner T c hc).shape ↔ (i, j) ∈ μ := by
  constructor
  · intro hcell
    exact (deleteCorner T c hc).shape_subset_old hcell
  · exact deleteCorner_shape_mem_of_row_lt T c hc hi

theorem deleteCorner_tableau_entry_of_row_lt {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    {i j : ℕ} (hi : i < c.1) (hcell : (i, j) ∈ μ) :
    (deleteCorner T c hc).tableau.T i j = T.T i j := by
  exact deleteCorner_tableau_entry T c hc
    (deleteCorner_shape_mem_of_row_lt T c hc hi hcell)

theorem RowAppendStepResult.deleteCorner_inverse {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (A : RowAppendStepResult T row x) :
    let D := deleteCorner A.result.tableau A.result.newCell A.result.newCell_removable
    D.shape = μ ∧ HEq D.tableau T ∧ D.value = x := by
  classical
  let D := deleteCorner A.result.tableau A.result.newCell A.result.newCell_removable
  have hshape : D.shape = μ := by
    ext c
    constructor
    · intro hcD
      have hcR : c ∈ A.result.shape := D.shape_subset_old hcD
      rcases (A.result.shape_mem_iff c).1 hcR with hcμ | hcnew
      · exact hcμ
      · exact False.elim (D.cell_not_mem_shape (by simpa [hcnew] using hcD))
    · intro hcμ
      have hcR : c ∈ A.result.shape :=
        A.result.old_subset c hcμ
      rcases (D.shape_mem_iff c).1 hcR with hcD | hcnew
      · exact hcD
      · exact False.elim (A.result.newCell_not_mem_old (by simpa [hcnew] using hcμ))
  have htableau : HEq D.tableau T := by
    apply BoundedSSYT.heq_of_entry_eq hshape
    intro i j
    by_cases hcellD : (i, j) ∈ D.shape
    · have hcellR : (i, j) ∈ A.result.shape := D.shape_subset_old hcellD
      have hcellμ : (i, j) ∈ μ := by
        rcases (A.result.shape_mem_iff (i, j)).1 hcellR with hμ | hnew
        · exact hμ
        · exact False.elim (D.cell_not_mem_shape (by simpa [hnew] using hcellD))
      calc
        D.tableau.T i j = A.result.tableau.T i j := by
          simpa [D] using
            deleteCorner_tableau_entry A.result.tableau A.result.newCell
              A.result.newCell_removable hcellD
        _ = T.T i j := A.unchanged_on_old_shape hcellμ
    · have hcellμ_not : (i, j) ∉ μ := by
        intro hcellμ
        have hcellD' : (i, j) ∈ D.shape := by
          simpa [hshape] using hcellμ
        exact hcellD hcellD'
      calc
        D.tableau.T i j = 0 := D.tableau.T.zeros hcellD
        _ = T.T i j := (T.T.zeros hcellμ_not).symm
  have hvalue : D.value = x := by
    apply Fin.ext
    have hval :
        D.value.val =
          A.result.tableau.T A.result.newCell.1 A.result.newCell.2 := by
      simp [D, deleteCorner]
    rw [hval]
    have hcell_eq : A.result.newCell = (row, μ.rowLen row) := A.newCell_eq
    rw [hcell_eq]
    exact A.inserted_entry
  exact ⟨hshape, htableau, hvalue⟩

noncomputable def deleteCorner_rowAppendLocation {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    RowAppendLocation (deleteCorner T c hc).tableau c.1 (deleteCorner T c hc).value where
  col := (deleteCorner T c hc).shape.rowLen c.1
  col_eq_rowLen := rfl
  row_entries_le := by
    intro j hj
    let D := deleteCorner T c hc
    have hDrow : D.shape.rowLen c.1 = c.2 := D.new_shape_rowLen_at_removedCell
    have hjc : j < c.2 := by simpa [D, hDrow] using hj
    have hcellD : (c.1, j) ∈ D.shape := by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      exact hj
    have hcellμ : (c.1, j) ∈ μ := D.shape_subset_old hcellD
    have hcμ : c ∈ μ := D.cell_mem_old
    calc
      D.tableau.T c.1 j = T.T c.1 j := deleteCorner_tableau_entry T c hc hcellD
      _ ≤ T.T c.1 c.2 := T.T.row_weak hjc hcμ
      _ = D.value.val := by
        simp [D, deleteCorner]

noncomputable def deleteCorner_rowAppendStepResult {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    RowAppendStepResult (deleteCorner T c hc).tableau c.1 (deleteCorner T c hc).value := by
  classical
  let D := deleteCorner T c hc
  exact RowAppendStepResult.constructOfAbove D.tableau c.1 D.value
    (deleteCorner_rowAppendLocation T c hc)
    (by
      by_cases hrow : c.1 = 0
      · exact Or.inl hrow
      · right
        have habove : (c.1 - 1, c.2) ∈ D.shape := D.shape_addable.above_mem hrow
        have hDrow : D.shape.rowLen c.1 = c.2 := D.new_shape_rowLen_at_removedCell
        simpa [D, hDrow] using habove)
    (by
      intro i hi hcell
      have hDrow : D.shape.rowLen c.1 = c.2 := D.new_shape_rowLen_at_removedCell
      have hcell' : (i, c.2) ∈ D.shape := by
        simpa [D, hDrow] using hcell
      have hcellμ : (i, c.2) ∈ μ := D.shape_subset_old hcell'
      calc
        D.tableau.T i (D.shape.rowLen c.1) = T.T i c.2 := by
          rw [hDrow]
          exact deleteCorner_tableau_entry T c hc hcell'
        _ < T.T c.1 c.2 := T.T.col_strict hi D.cell_mem_old
        _ = D.value.val := by
          simp [D, deleteCorner])

theorem deleteCorner_rowAppendStepResult_inverse {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    let A := deleteCorner_rowAppendStepResult T c hc
    A.result.shape = μ ∧ HEq A.result.tableau T ∧ A.result.newCell = c := by
  classical
  let D := deleteCorner T c hc
  let A := deleteCorner_rowAppendStepResult T c hc
  have hDrow : D.shape.rowLen c.1 = c.2 := D.new_shape_rowLen_at_removedCell
  have hnew : A.result.newCell = c := by
    calc
      A.result.newCell = (c.1, D.shape.rowLen c.1) := A.newCell_eq
      _ = c := by
        ext <;> simp [hDrow]
  have hshape : A.result.shape = μ := by
    ext d
    calc
      d ∈ A.result.shape ↔ d ∈ D.shape ∨ d = A.result.newCell :=
        A.result.shape_mem_iff d
      _ ↔ d ∈ D.shape ∨ d = c := by rw [hnew]
      _ ↔ d ∈ μ := (D.shape_mem_iff d).symm
  have htableau : HEq A.result.tableau T := by
    apply BoundedSSYT.heq_of_entry_eq hshape
    intro i j
    by_cases hcellA : (i, j) ∈ A.result.shape
    · rcases (A.result.shape_mem_iff (i, j)).1 hcellA with hcellD | hcellNew
      · calc
          A.result.tableau.T i j = D.tableau.T i j := A.unchanged_on_old_shape hcellD
          _ = T.T i j := deleteCorner_tableau_entry T c hc hcellD
      · have hi : i = c.1 := congrArg Prod.fst (by simpa [hnew] using hcellNew)
        have hj : j = c.2 := congrArg Prod.snd (by simpa [hnew] using hcellNew)
        subst i
        subst j
        calc
          A.result.tableau.T c.1 c.2 =
              A.result.tableau.T c.1 (D.shape.rowLen c.1) := by rw [hDrow]
          _ = D.value.val := A.inserted_entry
          _ = T.T c.1 c.2 := by
            simp [D, deleteCorner]
    · have hcellμ_not : (i, j) ∉ μ := by
        intro hcellμ
        exact hcellA (by simpa [hshape] using hcellμ)
      calc
        A.result.tableau.T i j = 0 := A.result.tableau.T.zeros hcellA
        _ = T.T i j := (T.T.zeros hcellμ_not).symm
  simpa [A] using ⟨hshape, htableau, hnew⟩

/-- In reverse row insertion, this records the rightmost entry in a row strictly
smaller than the moving value. -/
structure ReverseRowBumpLocation {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (moving : Fin N) where
  col : ℕ
  cell_mem : (row, col) ∈ μ
  entry_lt : T.T row col < moving.val
  right_ge :
    ∀ {j : ℕ}, col < j → (row, j) ∈ μ → moving.val ≤ T.T row j
  below_gt :
    ∀ {i : ℕ}, row < i → (i, col) ∈ μ → moving.val < T.T i col

namespace ReverseRowBumpLocation

/-- In the same row and tableau, increasing the moving value cannot move the
rightmost-smaller reverse bump position to the left. -/
theorem col_le_of_moving_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (Lx : ReverseRowBumpLocation T row x)
    (Ly : ReverseRowBumpLocation T row y)
    (hxy : x ≤ y) :
    Lx.col ≤ Ly.col := by
  apply le_of_not_gt
  intro hgt
  have hy_le_entry : y.val ≤ T.T row Lx.col :=
    Ly.right_ge hgt Lx.cell_mem
  have hy_lt_x : y.val < x.val :=
    lt_of_le_of_lt hy_le_entry Lx.entry_lt
  exact (not_lt_of_ge (Fin.le_def.mp hxy)) hy_lt_x

/-- Variant of `col_le_of_moving_le` for two tableaux agreeing on the compared row. -/
theorem col_le_of_moving_le_of_row_eq {N : ℕ} {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (Lx : ReverseRowBumpLocation T row x)
    (Ly : ReverseRowBumpLocation S row y)
    (hxy : x ≤ y)
    (hrow : ∀ {j : ℕ}, (row, j) ∈ μ → S.T row j = T.T row j) :
    Lx.col ≤ Ly.col := by
  apply le_of_not_gt
  intro hgt
  have hy_le_entryS : y.val ≤ S.T row Lx.col :=
    Ly.right_ge hgt Lx.cell_mem
  have hy_le_entryT : y.val ≤ T.T row Lx.col := by
    rwa [hrow Lx.cell_mem] at hy_le_entryS
  have hy_lt_x : y.val < x.val :=
    lt_of_le_of_lt hy_le_entryT Lx.entry_lt
  exact (not_lt_of_ge (Fin.le_def.mp hxy)) hy_lt_x

theorem col_lt_of_moving_le_of_row_eq_of_not_valid_at_right {N : ℕ}
    {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (Lx : ReverseRowBumpLocation T row x)
    (Ly : ReverseRowBumpLocation S row y)
    (hxy : x ≤ y)
    (hrow : ∀ {j : ℕ}, (row, j) ∈ μ → S.T row j = T.T row j)
    (hnot_valid : x.val ≤ T.T row Ly.col) :
    Lx.col < Ly.col := by
  have hle : Lx.col ≤ Ly.col :=
    Lx.col_le_of_moving_le_of_row_eq Ly hxy hrow
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hentry : T.T row Ly.col < x.val := by
      simpa [heq] using Lx.entry_lt
    exact (not_lt_of_ge hnot_valid) hentry

theorem col_lt_of_not_valid_at_col {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (Lx : ReverseRowBumpLocation T row x) {j : ℕ}
    (_hjmem : (row, j) ∈ μ) (hnot_valid : x.val ≤ T.T row j) :
    Lx.col < j := by
  apply lt_of_not_ge
  intro hge
  rcases lt_or_eq_of_le hge with hjlt | heq
  · have hle : T.T row j ≤ T.T row Lx.col :=
      T.T.row_weak hjlt Lx.cell_mem
    have hx_le : x.val ≤ T.T row Lx.col := le_trans hnot_valid hle
    exact (not_lt_of_ge hx_le) Lx.entry_lt
  · have hx_le : x.val ≤ T.T row Lx.col := by simpa [heq] using hnot_valid
    exact (not_lt_of_ge hx_le) Lx.entry_lt

theorem col_lt_of_moving_le_of_row_equiv_of_not_valid_at_right {N : ℕ}
    {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {x y : Fin N}
    (Lx : ReverseRowBumpLocation T row x)
    (Ly : ReverseRowBumpLocation S row y)
    (hxy : x ≤ y)
    (hμν : ∀ {j : ℕ}, (row, j) ∈ μ → (row, j) ∈ ν)
    (hrow :
      ∀ {j : ℕ}, (row, j) ∈ μ → (row, j) ∈ ν →
        S.T row j = T.T row j)
    (hnot_valid : x.val ≤ T.T row Ly.col) :
    Lx.col < Ly.col := by
  have hle : Lx.col ≤ Ly.col := by
    apply le_of_not_gt
    intro hgt
    have hy_le_entryS : y.val ≤ S.T row Lx.col :=
      Ly.right_ge hgt (hμν Lx.cell_mem)
    have hy_le_entryT : y.val ≤ T.T row Lx.col := by
      rwa [hrow Lx.cell_mem (hμν Lx.cell_mem)] at hy_le_entryS
    have hy_lt_x : y.val < x.val :=
      lt_of_le_of_lt hy_le_entryT Lx.entry_lt
    exact (not_lt_of_ge (Fin.le_def.mp hxy)) hy_lt_x
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hentry : T.T row Ly.col < x.val := by
      simpa [heq] using Lx.entry_lt
    exact (not_lt_of_ge hnot_valid) hentry

theorem cap_le_col_of_cap_lt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {moving : Fin N}
    (L : ReverseRowBumpLocation T row moving)
    (hcap_mem : (row, cap) ∈ μ)
    (hcap_lt : T.T row cap < moving.val) :
    cap ≤ L.col := by
  apply le_of_not_gt
  intro hlt
  have hle : moving.val ≤ T.T row cap := L.right_ge hlt hcap_mem
  exact (not_lt_of_ge hle) hcap_lt

theorem col_eq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (L₁ L₂ : ReverseRowBumpLocation T row moving) :
    L₁.col = L₂.col := by
  exact le_antisymm
    (L₁.col_le_of_moving_le L₂ le_rfl)
    (L₂.col_le_of_moving_le L₁ le_rfl)

end ReverseRowBumpLocation

/-- Finite search for the rightmost entry strictly smaller than the moving value. -/
theorem exists_reverseRowBumpLocation_of_exists {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (moving : Fin N)
    (hex : ∃ j : ℕ, (row, j) ∈ μ ∧ T.T row j < moving.val)
    (hbelow :
      ∀ {i j : ℕ}, row < i → (i, j) ∈ μ → T.T row j < moving.val →
        moving.val < T.T i j) :
    Nonempty (ReverseRowBumpLocation T row moving) := by
  classical
  let P : ℕ → Prop := fun j => (row, j) ∈ μ ∧ T.T row j < moving.val
  have hWitness : ∃ j : ℕ, j ≤ μ.rowLen row ∧ P j := by
    rcases hex with ⟨j, hmem, hlt⟩
    refine ⟨j, ?_, hmem, hlt⟩
    rw [YoungDiagram.mem_iff_lt_rowLen] at hmem
    exact Nat.le_of_lt hmem
  rcases hWitness with ⟨j₀, hj₀le, hj₀P⟩
  let col := Nat.findGreatest P (μ.rowLen row)
  have hcolP : P col := Nat.findGreatest_spec hj₀le hj₀P
  refine ⟨{
    col := col
    cell_mem := hcolP.1
    entry_lt := hcolP.2
    right_ge := ?_
    below_gt := ?_ }⟩
  · intro j hcol_lt_j hmem
    rw [YoungDiagram.mem_iff_lt_rowLen] at hmem
    apply le_of_not_gt
    intro hlt
    have hjle : j ≤ μ.rowLen row := Nat.le_of_lt hmem
    exact Nat.findGreatest_is_greatest (P := P) hcol_lt_j hjle ⟨by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      exact hmem, hlt⟩
  · intro i hi hmem
    exact hbelow hi hmem hcolP.2

/-- Finite search for the rightmost-smaller entry, with a lower-bound column invariant.

The `cap` column is already known to be a valid smaller entry. The selected rightmost
smaller entry is therefore weakly to the right of `cap`; this is the form needed in
the reverse bumping path invariant. -/
theorem exists_reverseRowBumpLocation_fromCap {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row cap : ℕ) (moving : Fin N)
    (hcap_mem : (row, cap) ∈ μ)
    (hcap_lt : T.T row cap < moving.val)
    (hbelow :
      ∀ {i j : ℕ}, row < i → cap ≤ j → (i, j) ∈ μ →
        moving.val < T.T i j) :
    Nonempty (ReverseRowBumpLocation T row moving) := by
  classical
  let P : ℕ → Prop := fun j => (row, j) ∈ μ ∧ T.T row j < moving.val
  have hcap_le_rowLen : cap ≤ μ.rowLen row := by
    rw [YoungDiagram.mem_iff_lt_rowLen] at hcap_mem
    exact Nat.le_of_lt hcap_mem
  let col := Nat.findGreatest P (μ.rowLen row)
  have hcolP : P col := Nat.findGreatest_spec hcap_le_rowLen ⟨hcap_mem, hcap_lt⟩
  have hcap_le_col : cap ≤ col :=
    Nat.le_findGreatest hcap_le_rowLen ⟨hcap_mem, hcap_lt⟩
  refine ⟨{
    col := col
    cell_mem := hcolP.1
    entry_lt := hcolP.2
    right_ge := ?_
    below_gt := ?_ }⟩
  · intro j hcol_lt_j hmem
    rw [YoungDiagram.mem_iff_lt_rowLen] at hmem
    apply le_of_not_gt
    intro hlt
    exact Nat.findGreatest_is_greatest (P := P) hcol_lt_j (Nat.le_of_lt hmem)
      ⟨by
        rw [YoungDiagram.mem_iff_lt_rowLen]
        exact hmem, hlt⟩
  · intro i hi hmem
    exact hbelow hi hcap_le_col hmem

/-- One upward reverse-bumping step: replace the chosen entry by the moving value and
continue upward with the displaced entry. The semistandard proof obligations are the
reverse-row-insertion analogue of `RowBumpStepResult.replaceTableau`. -/
structure ReverseRowBumpStepResult {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (moving : Fin N) where
  location : ReverseRowBumpLocation T row moving
  bumped : Fin N
  bumped_eq : T.T row location.col = bumped.val
  tableau : BoundedSSYT μ N
  replaced_entry : tableau.T row location.col = moving.val
  unchanged_of_ne :
    ∀ {i j : ℕ}, (i, j) ≠ (row, location.col) → tableau.T i j = T.T i j

namespace ReverseRowBumpStepResult

theorem bumped_lt_moving {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (B : ReverseRowBumpStepResult T row moving) :
    B.bumped.val < moving.val := by
  rw [← B.bumped_eq]
  exact B.location.entry_lt

theorem location_col_eq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (B C : ReverseRowBumpStepResult T row moving) :
    B.location.col = C.location.col :=
  B.location.col_eq C.location

theorem bumped_eq_of_same {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (B C : ReverseRowBumpStepResult T row moving) :
    B.bumped = C.bumped := by
  apply Fin.ext
  calc
    B.bumped.val = T.T row B.location.col := B.bumped_eq.symm
    _ = T.T row C.location.col := by rw [B.location_col_eq C]
    _ = C.bumped.val := C.bumped_eq

theorem tableau_eq_of_same {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (B C : ReverseRowBumpStepResult T row moving) :
    B.tableau = C.tableau := by
  apply BoundedSSYT.ext
  intro i j
  by_cases hB : ((i, j) : ℕ × ℕ) = (row, B.location.col)
  · have hC : ((i, j) : ℕ × ℕ) = (row, C.location.col) := by
      simpa [B.location_col_eq C] using hB
    have hi : i = row := congrArg Prod.fst hB
    have hj : j = B.location.col := congrArg Prod.snd hB
    subst i
    subst j
    calc
      B.tableau.T row B.location.col = moving.val := B.replaced_entry
      _ = C.tableau.T row B.location.col := by
        rw [B.location_col_eq C]
        exact C.replaced_entry.symm
  · have hC : ((i, j) : ℕ × ℕ) ≠ (row, C.location.col) := by
      intro hc
      exact hB (by simpa [B.location_col_eq C] using hc)
    calc
      B.tableau.T i j = T.T i j := B.unchanged_of_ne hB
      _ = C.tableau.T i j := (C.unchanged_of_ne hC).symm

/-- In the same row and tableau, increasing the moving value makes the reverse-bumped
value weakly increase. -/
theorem bumped_le_of_moving_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (Bx : ReverseRowBumpStepResult T row x)
    (By : ReverseRowBumpStepResult T row y)
    (hxy : x ≤ y) :
    Bx.bumped ≤ By.bumped := by
  rw [Fin.le_def, ← Bx.bumped_eq, ← By.bumped_eq]
  have hcol : Bx.location.col ≤ By.location.col :=
    Bx.location.col_le_of_moving_le By.location hxy
  rcases lt_or_eq_of_le hcol with hlt | heq
  · exact T.T.row_weak hlt By.location.cell_mem
  · simp [heq]

/-- Variant of `bumped_le_of_moving_le` for two tableaux agreeing on the compared row. -/
theorem bumped_le_of_moving_le_of_row_eq {N : ℕ} {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (Bx : ReverseRowBumpStepResult T row x)
    (By : ReverseRowBumpStepResult S row y)
    (hxy : x ≤ y)
    (hrow : ∀ {j : ℕ}, (row, j) ∈ μ → S.T row j = T.T row j) :
    Bx.bumped ≤ By.bumped := by
  rw [Fin.le_def, ← Bx.bumped_eq, ← By.bumped_eq]
  have hcol : Bx.location.col ≤ By.location.col :=
    Bx.location.col_le_of_moving_le_of_row_eq By.location hxy hrow
  rcases lt_or_eq_of_le hcol with hlt | heq
  · calc
      T.T row Bx.location.col ≤ T.T row By.location.col :=
        T.T.row_weak hlt By.location.cell_mem
      _ = S.T row By.location.col := (hrow By.location.cell_mem).symm
  · rw [heq]
    exact le_of_eq (hrow By.location.cell_mem).symm

theorem bumped_le_of_moving_le_of_row_equiv {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {x y : Fin N}
    (Bx : ReverseRowBumpStepResult T row x)
    (By : ReverseRowBumpStepResult S row y)
    (hxy : x ≤ y)
    (hμν : ∀ {j : ℕ}, (row, j) ∈ μ → (row, j) ∈ ν)
    (hνμ : ∀ {j : ℕ}, (row, j) ∈ ν → (row, j) ∈ μ)
    (hrow :
      ∀ {j : ℕ}, (row, j) ∈ μ → (row, j) ∈ ν →
        S.T row j = T.T row j) :
    Bx.bumped ≤ By.bumped := by
  rw [Fin.le_def, ← Bx.bumped_eq, ← By.bumped_eq]
  have hcol : Bx.location.col ≤ By.location.col := by
    apply le_of_not_gt
    intro hgt
    have hy_le_entryS : y.val ≤ S.T row Bx.location.col :=
      By.location.right_ge hgt (hμν Bx.location.cell_mem)
    have hy_le_entryT : y.val ≤ T.T row Bx.location.col := by
      rwa [hrow Bx.location.cell_mem (hμν Bx.location.cell_mem)] at hy_le_entryS
    have hy_lt_x : y.val < x.val :=
      lt_of_le_of_lt hy_le_entryT Bx.location.entry_lt
    exact (not_lt_of_ge (Fin.le_def.mp hxy)) hy_lt_x
  rcases lt_or_eq_of_le hcol with hlt | heq
  · calc
      T.T row Bx.location.col ≤ T.T row By.location.col :=
        T.T.row_weak hlt (hνμ By.location.cell_mem)
      _ = S.T row By.location.col := by
        have hcellT : (row, By.location.col) ∈ μ :=
          hνμ By.location.cell_mem
        exact (hrow hcellT By.location.cell_mem).symm
  · rw [heq]
    have hcellT : (row, By.location.col) ∈ μ := hνμ By.location.cell_mem
    exact le_of_eq (hrow hcellT By.location.cell_mem).symm

noncomputable def replaceTableau {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row col : ℕ) (moving : Fin N)
    (hcell : (row, col) ∈ μ)
    (hentry_lt : T.T row col < moving.val)
    (hright : ∀ {j : ℕ}, col < j → (row, j) ∈ μ → moving.val ≤ T.T row j)
    (hbelow : ∀ {i : ℕ}, row < i → (i, col) ∈ μ → moving.val < T.T i col) :
    BoundedSSYT μ N where
  T :=
    { entry := RowBumpStepResult.replaceEntry T row col moving
      row_weak' := by
        intro (i : ℕ) (j₁ : ℕ) (j₂ : ℕ) hj hcell₂
        by_cases h₂ : ((i, j₂) : ℕ × ℕ) = (row, col)
        · have hi : i = row := congrArg Prod.fst h₂
          have hj₂eq : j₂ = col := congrArg Prod.snd h₂
          subst i
          subst j₂
          rw [RowBumpStepResult.replaceEntry_same]
          have hj₁lt : j₁ < col := hj
          have hcell₁ : (row, j₁) ∈ μ :=
            μ.up_left_mem le_rfl (Nat.le_of_lt hj₁lt) hcell
          rw [RowBumpStepResult.replaceEntry_ne]
          · exact le_trans (T.T.row_weak hj₁lt hcell) (le_of_lt hentry_lt)
          · intro hp
            exact Nat.lt_irrefl col (by
              have hcol : j₁ = col := congrArg Prod.snd hp
              simp [hcol] at hj₁lt)
        · rw [RowBumpStepResult.replaceEntry_ne _ _ _ _ h₂]
          by_cases h₁ : ((i, j₁) : ℕ × ℕ) = (row, col)
          · have hi : i = row := congrArg Prod.fst h₁
            have hj₁eq : j₁ = col := congrArg Prod.snd h₁
            subst i
            subst j₁
            rw [RowBumpStepResult.replaceEntry_same]
            exact hright hj hcell₂
          · rw [RowBumpStepResult.replaceEntry_ne _ _ _ _ h₁]
            exact T.T.row_weak hj hcell₂
      col_strict' := by
        intro (i₁ : ℕ) (i₂ : ℕ) (j : ℕ) hi hcell₂
        by_cases h₂ : ((i₂, j) : ℕ × ℕ) = (row, col)
        · have hi₂eq : i₂ = row := congrArg Prod.fst h₂
          have hjeq : j = col := congrArg Prod.snd h₂
          subst i₂
          subst j
          rw [RowBumpStepResult.replaceEntry_same]
          have hi₁lt : i₁ < row := hi
          have hcell₁ : (i₁, col) ∈ μ :=
            μ.up_left_mem (Nat.le_of_lt hi₁lt) le_rfl hcell
          rw [RowBumpStepResult.replaceEntry_ne]
          · exact lt_trans (T.T.col_strict hi₁lt hcell) hentry_lt
          · intro hp
            exact Nat.lt_irrefl row (by
              have hrow : i₁ = row := congrArg Prod.fst hp
              simp [hrow] at hi₁lt)
        · rw [RowBumpStepResult.replaceEntry_ne _ _ _ _ h₂]
          by_cases h₁ : ((i₁, j) : ℕ × ℕ) = (row, col)
          · have hi₁eq : i₁ = row := congrArg Prod.fst h₁
            have hjeq : j = col := congrArg Prod.snd h₁
            subst i₁
            subst j
            rw [RowBumpStepResult.replaceEntry_same]
            exact hbelow hi hcell₂
          · rw [RowBumpStepResult.replaceEntry_ne _ _ _ _ h₁]
            exact T.T.col_strict hi hcell₂
      zeros' := by
        intro i j hnot
        rw [RowBumpStepResult.replaceEntry_ne]
        · exact T.T.zeros hnot
        · intro hp
          exact hnot (by simpa [hp] using hcell) }
  bound := by
    intro i j hmem
    change RowBumpStepResult.replaceEntry T row col moving i j < N
    by_cases h : ((i, j) : ℕ × ℕ) = (row, col)
    · have hi : i = row := congrArg Prod.fst h
      have hj : j = col := congrArg Prod.snd h
      subst i
      subst j
      rw [RowBumpStepResult.replaceEntry_same]
      exact moving.isLt
    · rw [RowBumpStepResult.replaceEntry_ne _ _ _ _ h]
      exact T.bound hmem

end ReverseRowBumpStepResult

/-- Construct one reverse-bumping step from the rightmost-smaller location. -/
noncomputable def reverseRowBumpStep {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row : ℕ) (moving : Fin N)
    (L : ReverseRowBumpLocation T row moving) :
    ReverseRowBumpStepResult T row moving where
  location := L
  bumped := ⟨T.T row L.col, T.bound L.cell_mem⟩
  bumped_eq := rfl
  tableau :=
    ReverseRowBumpStepResult.replaceTableau T row L.col moving L.cell_mem
      L.entry_lt L.right_ge L.below_gt
  replaced_entry := RowBumpStepResult.replaceEntry_same T row L.col moving
  unchanged_of_ne := by
    intro i j h
    exact RowBumpStepResult.replaceEntry_ne T row L.col moving h

/-- A forward row-bump step gives the matching reverse-bump location in the modified
row: the replaced entry `x` is the rightmost entry strictly smaller than the bumped
value. -/
def RowBumpStepResult.reverseLocation {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) :
    ReverseRowBumpLocation B.tableau row B.bumped where
  col := B.col
  cell_mem := B.cell_mem
  entry_lt := by
    rw [B.replaced_entry]
    exact B.bumped_gt
  right_ge := by
    intro j hj hcell
    have hne : ((row, j) : ℕ × ℕ) ≠ (row, B.col) := by
      intro hp
      have hcol : j = B.col := congrArg Prod.snd hp
      omega
    rw [B.unchanged_of_ne hne]
    rw [← B.bumped_eq]
    exact T.T.row_weak hj hcell
  below_gt := by
    intro i hi hcell
    have hne : ((i, B.col) : ℕ × ℕ) ≠ (row, B.col) := by
      intro hp
      have hrow : i = row := congrArg Prod.fst hp
      omega
    rw [B.unchanged_of_ne hne]
    rw [← B.bumped_eq]
    exact T.T.col_strict hi hcell

theorem reverseRowBumpStep_forward_bump_bumped {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) :
    (reverseRowBumpStep B.tableau row B.bumped B.reverseLocation).bumped = x := by
  apply Fin.ext
  change B.tableau.T row B.col = x.val
  exact B.replaced_entry

theorem reverseRowBumpStep_forward_bump_tableau_entry {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) (i j : ℕ) :
    (reverseRowBumpStep B.tableau row B.bumped B.reverseLocation).tableau.T i j =
      T.T i j := by
  by_cases hcell : ((i, j) : ℕ × ℕ) = (row, B.col)
  · have hi : i = row := congrArg Prod.fst hcell
    have hj : j = B.col := congrArg Prod.snd hcell
    subst i
    subst j
    calc
      (reverseRowBumpStep B.tableau row B.bumped B.reverseLocation).tableau.T row B.col =
          B.bumped.val := by
            simpa [RowBumpStepResult.reverseLocation] using
              (reverseRowBumpStep B.tableau row B.bumped B.reverseLocation).replaced_entry
      _ = T.T row B.col := B.bumped_eq.symm
  · rw [(reverseRowBumpStep B.tableau row B.bumped B.reverseLocation).unchanged_of_ne hcell]
    exact B.unchanged_of_ne hcell

theorem reverseRowBumpStep_forward_bump_tableau_heq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (B : RowBumpStepResult T row x) :
    HEq (reverseRowBumpStep B.tableau row B.bumped B.reverseLocation).tableau T := by
  exact heq_of_eq (BoundedSSYT.ext (reverseRowBumpStep_forward_bump_tableau_entry B))

/-- A reverse row-bump step determines the matching forward bump location in the
modified row. -/
def ReverseRowBumpStepResult.forwardLocation {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (B : ReverseRowBumpStepResult T row moving) :
    RowBumpLocation B.tableau row B.bumped where
  col := B.location.col
  cell_mem := B.location.cell_mem
  entry_gt := by
    rw [B.replaced_entry]
    exact B.bumped_lt_moving
  left_le := by
    intro j hj hcell
    have hne : ((row, j) : ℕ × ℕ) ≠ (row, B.location.col) := by
      intro hp
      have hcol : j = B.location.col := congrArg Prod.snd hp
      omega
    calc
      B.tableau.T row j = T.T row j := B.unchanged_of_ne hne
      _ ≤ T.T row B.location.col := T.T.row_weak hj B.location.cell_mem
      _ = B.bumped.val := B.bumped_eq

/-- Forward row bumping after one reverse row-bump recovers the moving value. -/
theorem rowBumpStep_reverse_bump_bumped {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (B : ReverseRowBumpStepResult T row moving) :
    (RowBumpStepResult.construct B.tableau row B.bumped B.forwardLocation
      (by
        intro i hi _hcell
        have hne : ((i, B.location.col) : ℕ × ℕ) ≠ (row, B.location.col) := by
          intro hp
          have hrow : i = row := congrArg Prod.fst hp
          omega
        calc
          B.tableau.T i B.location.col = T.T i B.location.col := B.unchanged_of_ne hne
          _ < T.T row B.location.col := T.T.col_strict hi B.location.cell_mem
          _ = B.bumped.val := B.bumped_eq)).bumped = moving := by
  apply Fin.ext
  change B.tableau.T row B.location.col = moving.val
  exact B.replaced_entry

/-- Forward row bumping after one reverse row-bump restores the previous tableau. -/
theorem rowBumpStep_reverse_bump_tableau_heq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (B : ReverseRowBumpStepResult T row moving) :
    HEq
      (RowBumpStepResult.construct B.tableau row B.bumped B.forwardLocation
        (by
          intro i hi _hcell
          have hne : ((i, B.location.col) : ℕ × ℕ) ≠ (row, B.location.col) := by
            intro hp
            have hrow : i = row := congrArg Prod.fst hp
            omega
          calc
            B.tableau.T i B.location.col = T.T i B.location.col := B.unchanged_of_ne hne
            _ < T.T row B.location.col := T.T.col_strict hi B.location.cell_mem
            _ = B.bumped.val := B.bumped_eq)).tableau
      T := by
  apply heq_of_eq
  apply BoundedSSYT.ext
  intro i j
  by_cases hcell : ((i, j) : ℕ × ℕ) = (row, B.location.col)
  · have hi : i = row := congrArg Prod.fst hcell
    have hj : j = B.location.col := congrArg Prod.snd hcell
    subst i
    subst j
    calc
      (RowBumpStepResult.construct B.tableau row B.bumped B.forwardLocation
        (by
          intro i hi _hcell
          have hne : ((i, B.location.col) : ℕ × ℕ) ≠ (row, B.location.col) := by
            intro hp
            have hrow : i = row := congrArg Prod.fst hp
            omega
          calc
            B.tableau.T i B.location.col = T.T i B.location.col := B.unchanged_of_ne hne
            _ < T.T row B.location.col := T.T.col_strict hi B.location.cell_mem
            _ = B.bumped.val := B.bumped_eq)).tableau.T row B.location.col =
          B.bumped.val := by
            exact (RowBumpStepResult.construct B.tableau row B.bumped B.forwardLocation
              (by
                intro i hi _hcell
                have hne : ((i, B.location.col) : ℕ × ℕ) ≠
                    (row, B.location.col) := by
                  intro hp
                  have hrow : i = row := congrArg Prod.fst hp
                  omega
                calc
                  B.tableau.T i B.location.col = T.T i B.location.col :=
                    B.unchanged_of_ne hne
                  _ < T.T row B.location.col := T.T.col_strict hi B.location.cell_mem
                  _ = B.bumped.val := B.bumped_eq)).replaced_entry
      _ = T.T row B.location.col := B.bumped_eq.symm
  · calc
      (RowBumpStepResult.construct B.tableau row B.bumped B.forwardLocation
        (by
          intro i hi _hcell
          have hne : ((i, B.location.col) : ℕ × ℕ) ≠ (row, B.location.col) := by
            intro hp
            have hrow : i = row := congrArg Prod.fst hp
            omega
          calc
            B.tableau.T i B.location.col = T.T i B.location.col := B.unchanged_of_ne hne
            _ < T.T row B.location.col := T.T.col_strict hi B.location.cell_mem
            _ = B.bumped.val := B.bumped_eq)).tableau.T i j =
          B.tableau.T i j := by
            exact (RowBumpStepResult.construct B.tableau row B.bumped B.forwardLocation
              (by
                intro i hi _hcell
                have hne : ((i, B.location.col) : ℕ × ℕ) ≠
                    (row, B.location.col) := by
                  intro hp
                  have hrow : i = row := congrArg Prod.fst hp
                  omega
                calc
                  B.tableau.T i B.location.col = T.T i B.location.col :=
                    B.unchanged_of_ne hne
                  _ < T.T row B.location.col := T.T.col_strict hi B.location.cell_mem
                  _ = B.bumped.val := B.bumped_eq)).unchanged_of_ne hcell
      _ = T.T i j := B.unchanged_of_ne hcell

/-- A full reverse row-insertion trace after the outside corner has been deleted.

The trace starts with the deleted corner value and the row just above the deleted corner.
Each step moves one row upward. At row `0`, the moving value is the value ejected by
reverse insertion. -/
inductive ReverseRowInsertionTrace (N : ℕ) {μ : YoungDiagram} :
    BoundedSSYT μ N → ℕ → Fin N → Type where
  | done {T : BoundedSSYT μ N} {moving : Fin N}
      (B : ReverseRowBumpStepResult T 0 moving) :
      ReverseRowInsertionTrace N T 0 moving
  | bump {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
      (hrow : row ≠ 0)
      (B : ReverseRowBumpStepResult T row moving)
      (tail : ReverseRowInsertionTrace N B.tableau (row - 1) B.bumped) :
      ReverseRowInsertionTrace N T row moving

/-- The final tableau and ejected value produced by a reverse row-insertion trace. -/
def ReverseRowInsertionTrace.result {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {moving : Fin N} :
    ReverseRowInsertionTrace N T row moving → Sigma fun _ : BoundedSSYT μ N => Fin N
  | .done B => ⟨B.tableau, B.bumped⟩
  | .bump _ _ tail => tail.result

namespace ReverseRowInsertionTrace

theorem exists_cast_of_heq {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {moving : Fin N}
    (hμ : μ = ν) (hT : HEq T S)
    (tr : ReverseRowInsertionTrace N T row moving) :
    ∃ trS : ReverseRowInsertionTrace N S row moving, HEq trS tr := by
  subst ν
  have hT_eq : T = S := eq_of_heq hT
  subst S
  exact ⟨tr, HEq.rfl⟩

noncomputable def castOfHEq {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {moving : Fin N}
    (hμ : μ = ν) (hT : HEq T S)
    (tr : ReverseRowInsertionTrace N T row moving) :
    ReverseRowInsertionTrace N S row moving :=
  Classical.choose (exists_cast_of_heq hμ hT tr)

theorem castOfHEq_heq {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {moving : Fin N}
    (hμ : μ = ν) (hT : HEq T S)
    (tr : ReverseRowInsertionTrace N T row moving) :
    HEq (castOfHEq hμ hT tr) tr :=
  (Classical.choose_spec (exists_cast_of_heq hμ hT tr))

theorem castOfHEq_result_value_eq {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {moving : Fin N}
    (hμ : μ = ν) (hT : HEq T S)
    (tr : ReverseRowInsertionTrace N T row moving) :
    (castOfHEq hμ hT tr).result.2 = tr.result.2 := by
  subst ν
  have hT_eq : T = S := eq_of_heq hT
  subst S
  simp [castOfHEq]

theorem castOfHEq_result_tableau_heq {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {moving : Fin N}
    (hμ : μ = ν) (hT : HEq T S)
    (tr : ReverseRowInsertionTrace N T row moving) :
    HEq (castOfHEq hμ hT tr).result.1 tr.result.1 := by
  subst ν
  have hT_eq : T = S := eq_of_heq hT
  subst S
  simp [castOfHEq]

theorem castMoving_result_value_eq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving moving' : Fin N}
    (h : moving = moving')
    (tr : ReverseRowInsertionTrace N T row moving') :
    (h ▸ tr : ReverseRowInsertionTrace N T row moving).result.2 = tr.result.2 := by
  subst h
  rfl

noncomputable def castMoving {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving moving' : Fin N}
    (h : moving = moving')
    (tr : ReverseRowInsertionTrace N T row moving') :
    ReverseRowInsertionTrace N T row moving := by
  subst h
  exact tr

theorem castMoving_def_result_value_eq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving moving' : Fin N}
    (h : moving = moving')
    (tr : ReverseRowInsertionTrace N T row moving') :
    (castMoving h tr).result.2 = tr.result.2 := by
  subst h
  rfl

theorem castMoving_def_result_tableau_heq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving moving' : Fin N}
    (h : moving = moving')
    (tr : ReverseRowInsertionTrace N T row moving') :
    HEq (castMoving h tr).result.1 tr.result.1 := by
  subst h
  exact HEq.rfl

theorem castMoving_result_tableau_heq {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving moving' : Fin N}
    (h : moving = moving')
    (tr : ReverseRowInsertionTrace N T row moving') :
    HEq (h ▸ tr : ReverseRowInsertionTrace N T row moving).result.1 tr.result.1 := by
  subst h
  exact HEq.rfl

theorem result_value_eq_of_same {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr₁ tr₂ : ReverseRowInsertionTrace N T row moving) :
    tr₁.result.2 = tr₂.result.2 := by
  induction tr₁ with
  | done B₁ =>
      cases tr₂ with
      | done B₂ =>
          simpa [ReverseRowInsertionTrace.result] using B₁.bumped_eq_of_same B₂
      | bump hrow _ _ =>
          exact False.elim (hrow rfl)
  | bump hrow₁ B₁ tail₁ ih =>
      cases tr₂ with
      | done _ =>
          exact False.elim (hrow₁ rfl)
      | bump _ B₂ tail₂ =>
          have htableau : B₁.tableau = B₂.tableau := B₁.tableau_eq_of_same B₂
          have hbumped : B₁.bumped = B₂.bumped := B₁.bumped_eq_of_same B₂
          let tail₂m := castMoving hbumped tail₂
          let tail₂' := castOfHEq (rfl : μ = μ) (heq_of_eq htableau.symm) tail₂m
          calc
            tail₁.result.2 = tail₂'.result.2 := ih tail₂'
            _ = tail₂m.result.2 :=
              by simpa [tail₂'] using
                (castOfHEq_result_value_eq (rfl : μ = μ)
                  (heq_of_eq htableau.symm) tail₂m)
            _ = tail₂.result.2 :=
              by simpa [tail₂m] using castMoving_def_result_value_eq hbumped tail₂

theorem result_tableau_heq_of_same {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr₁ tr₂ : ReverseRowInsertionTrace N T row moving) :
    HEq tr₁.result.1 tr₂.result.1 := by
  induction tr₁ with
  | done B₁ =>
      cases tr₂ with
      | done B₂ =>
          exact heq_of_eq (B₁.tableau_eq_of_same B₂)
      | bump hrow _ _ =>
          exact False.elim (hrow rfl)
  | bump hrow₁ B₁ tail₁ ih =>
      cases tr₂ with
      | done _ =>
          exact False.elim (hrow₁ rfl)
      | bump _ B₂ tail₂ =>
          have htableau : B₁.tableau = B₂.tableau := B₁.tableau_eq_of_same B₂
          have hbumped : B₁.bumped = B₂.bumped := B₁.bumped_eq_of_same B₂
          let tail₂m := castMoving hbumped tail₂
          let tail₂' := castOfHEq (rfl : μ = μ) (heq_of_eq htableau.symm) tail₂m
          have hrec : HEq tail₁.result.1 tail₂'.result.1 := ih tail₂'
          have hcastT : HEq tail₂'.result.1 tail₂m.result.1 :=
            by simpa [tail₂'] using
              castOfHEq_result_tableau_heq (rfl : μ = μ) (heq_of_eq htableau.symm) tail₂m
          have hcastM : HEq tail₂m.result.1 tail₂.result.1 :=
            by simpa [tail₂m] using castMoving_def_result_tableau_heq hbumped tail₂
          exact hrec.trans (hcastT.trans hcastM)

theorem rowInsertionTrace_with_continuation {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (cont : RowInsertionTrace N T (row + 1) moving) :
    ∃ ftr : RowInsertionTrace N tr.result.1 0 tr.result.2,
      ftr.result = cont.result := by
  induction tr with
  | done B =>
      rename_i T₀ moving₀
      let F : RowBumpStepResult B.tableau 0 B.bumped :=
        RowBumpStepResult.construct B.tableau 0 B.bumped B.forwardLocation
          (by
            intro i hi _hcell
            omega)
      have hbumped : F.bumped = moving₀ := by
        simpa [F] using rowBumpStep_reverse_bump_bumped B
      have htableau : HEq F.tableau T₀ := by
        simpa [F] using rowBumpStep_reverse_bump_tableau_heq B
      let contVal : RowInsertionTrace N T₀ (0 + 1) F.bumped :=
        RowInsertionTrace.castValue hbumped cont
      let contTab : RowInsertionTrace N F.tableau (0 + 1) F.bumped :=
        RowInsertionTrace.castOfHEq (rfl : μ = μ) htableau.symm contVal
      refine ⟨RowInsertionTrace.bump F contTab, ?_⟩
      calc
        (RowInsertionTrace.bump F contTab).result = contTab.result := rfl
        _ = contVal.result := RowInsertionTrace.castOfHEq_result_eq htableau.symm contVal
        _ = cont.result := RowInsertionTrace.castValue_result_eq hbumped cont
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      let F : RowBumpStepResult B.tableau row₀ B.bumped :=
        RowBumpStepResult.construct B.tableau row₀ B.bumped B.forwardLocation
          (by
            intro i hi _hcell
            have hne : ((i, B.location.col) : ℕ × ℕ) ≠ (row₀, B.location.col) := by
              intro hp
              have hrowi : i = row₀ := congrArg Prod.fst hp
              omega
            calc
              B.tableau.T i B.location.col = T₀.T i B.location.col := B.unchanged_of_ne hne
              _ < T₀.T row₀ B.location.col := T₀.T.col_strict hi B.location.cell_mem
              _ = B.bumped.val := B.bumped_eq)
      have hbumped : F.bumped = moving₀ := by
        simpa [F] using rowBumpStep_reverse_bump_bumped B
      have htableau : HEq F.tableau T₀ := by
        simpa [F] using rowBumpStep_reverse_bump_tableau_heq B
      let contVal : RowInsertionTrace N T₀ (row₀ + 1) F.bumped :=
        RowInsertionTrace.castValue hbumped cont
      let contTab : RowInsertionTrace N F.tableau (row₀ + 1) F.bumped :=
        RowInsertionTrace.castOfHEq (rfl : μ = μ) htableau.symm contVal
      let contTailRaw : RowInsertionTrace N B.tableau row₀ B.bumped :=
        RowInsertionTrace.bump F contTab
      have hroweq : row₀ - 1 + 1 = row₀ := by
        omega
      let contTail : RowInsertionTrace N B.tableau (row₀ - 1 + 1) B.bumped :=
        RowInsertionTrace.castRow hroweq contTailRaw
      rcases ih contTail with ⟨ftr, hftr⟩
      refine ⟨ftr, ?_⟩
      calc
        ftr.result = contTail.result := hftr
        _ = contTailRaw.result := RowInsertionTrace.castRow_result_eq hroweq contTailRaw
        _ = contTab.result := rfl
        _ = contVal.result := RowInsertionTrace.castOfHEq_result_eq htableau.symm contVal
        _ = cont.result := RowInsertionTrace.castValue_result_eq hbumped cont

def RespectsLowerCap {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) (cap : ℕ) : Prop :=
  match tr with
  | .done B => cap ≤ B.location.col
  | .bump _ B tail => cap ≤ B.location.col ∧ tail.RespectsLowerCap B.location.col

def movingAt {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) (target : ℕ) : Fin N :=
  match tr with
  | .done _ => moving
  | .bump _ _ tail =>
      if target = row then moving else tail.movingAt target

def tableauAt {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) (target : ℕ) :
    BoundedSSYT μ N :=
  match tr with
  | .done _ => T
  | .bump _ _ tail =>
      if target = row then T else tail.tableauAt target

def topCol {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) : ℕ :=
  match tr with
  | .done B => B.location.col
  | .bump _ _ tail => tail.topCol

def bumpColAt {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) (target : ℕ) : ℕ :=
  match tr with
  | .done B => B.location.col
  | .bump _ B tail =>
      if target = row then B.location.col else tail.bumpColAt target

theorem movingAt_bump_of_target_le_pred {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target : ℕ} {moving : Fin N}
    (hrow : row ≠ 0) (B : ReverseRowBumpStepResult T row moving)
    (tail : ReverseRowInsertionTrace N B.tableau (row - 1) B.bumped)
    (htarget : target ≤ row - 1) :
    (ReverseRowInsertionTrace.bump hrow B tail).movingAt target =
      tail.movingAt target := by
  have hne : target ≠ row := by omega
  simp [movingAt, hne]

theorem tableauAt_bump_of_target_le_pred {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target : ℕ} {moving : Fin N}
    (hrow : row ≠ 0) (B : ReverseRowBumpStepResult T row moving)
    (tail : ReverseRowInsertionTrace N B.tableau (row - 1) B.bumped)
    (htarget : target ≤ row - 1) :
    (ReverseRowInsertionTrace.bump hrow B tail).tableauAt target =
      tail.tableauAt target := by
  have hne : target ≠ row := by omega
  simp [tableauAt, hne]

theorem bumpColAt_bump_of_target_le_pred {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target : ℕ} {moving : Fin N}
    (hrow : row ≠ 0) (B : ReverseRowBumpStepResult T row moving)
    (tail : ReverseRowInsertionTrace N B.tableau (row - 1) B.bumped)
    (htarget : target ≤ row - 1) :
    (ReverseRowInsertionTrace.bump hrow B tail).bumpColAt target =
      tail.bumpColAt target := by
  have hne : target ≠ row := by omega
  simp [bumpColAt, hne]

theorem movingAt_self {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) :
    tr.movingAt row = moving := by
  cases tr with
  | done B =>
      simp [movingAt]
  | bump hrow B tail =>
      simp [movingAt]

theorem exists_tailFrom {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) (htarget : target ≤ row) :
    ∃ _tail : ReverseRowInsertionTrace N (tr.tableauAt target) target (tr.movingAt target),
      True := by
  induction tr generalizing target with
  | done B =>
      have htarget0 : target = 0 := by omega
      subst target
      exact ⟨ReverseRowInsertionTrace.done B, trivial⟩
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases htarget_eq : target = row₀
      · subst target
        simpa [tableauAt, movingAt] using
          (show ∃ tail' : ReverseRowInsertionTrace N T₀ row₀ moving₀, True from
            ⟨ReverseRowInsertionTrace.bump hrow B tail, trivial⟩)
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        rcases ih htarget_tail with ⟨tail', htail'⟩
        simpa [tableauAt, movingAt, htarget_eq] using
          (show ∃ tail' : ReverseRowInsertionTrace N (tail.tableauAt target) target
              (tail.movingAt target), True from
            ⟨tail', htail'⟩)

noncomputable def tailFrom {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (target : ℕ) (htarget : target ≤ row) :
    ReverseRowInsertionTrace N (tr.tableauAt target) target (tr.movingAt target) :=
  Classical.choose (tr.exists_tailFrom htarget)

theorem exists_stepAt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) (htarget : target ≤ row) :
    ∃ _B : ReverseRowBumpStepResult (tr.tableauAt target) target (tr.movingAt target),
      True := by
  induction tr generalizing target with
  | done B =>
      have htarget0 : target = 0 := by omega
      subst target
      exact ⟨B, trivial⟩
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases htarget_eq : target = row₀
      · subst target
        simpa [tableauAt, movingAt] using
          (show ∃ B' : ReverseRowBumpStepResult T₀ row₀ moving₀, True from
            ⟨B, trivial⟩)
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        rcases ih htarget_tail with ⟨B', hB'⟩
        simpa [tableauAt, movingAt, htarget_eq] using
          (show ∃ B' : ReverseRowBumpStepResult (tail.tableauAt target) target
              (tail.movingAt target), True from
            ⟨B', hB'⟩)

noncomputable def stepAt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (target : ℕ) (htarget : target ≤ row) :
    ReverseRowBumpStepResult (tr.tableauAt target) target (tr.movingAt target) :=
  Classical.choose (tr.exists_stepAt htarget)

theorem movingAt_le_tableauAt_of_bumpColAt_lt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) (htarget : target ≤ row)
    {j : ℕ} (hcol : tr.bumpColAt target < j)
    (hcell : (target, j) ∈ μ) :
    (tr.movingAt target).val ≤ (tr.tableauAt target).T target j := by
  induction tr generalizing target with
  | done B =>
      have htarget0 : target = 0 := by omega
      subst target
      simpa [movingAt, tableauAt, bumpColAt] using
        B.location.right_ge hcol hcell
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases htarget_eq : target = row₀
      · subst target
        have hcol0 : B.location.col < j := by
          simpa [bumpColAt] using hcol
        simpa [movingAt, tableauAt, bumpColAt] using
          B.location.right_ge hcol0 hcell
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        have hcol_tail : tail.bumpColAt target < j := by
          simpa [bumpColAt, htarget_eq] using hcol
        have hcell_tail : (target, j) ∈ μ := hcell
        simpa [movingAt, tableauAt, bumpColAt, htarget_eq] using
          ih htarget_tail hcol_tail hcell_tail

theorem movingAt_pred_val_eq_tableauAt_succ_bumpColAt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (htarget : target + 1 ≤ row) :
    (tr.movingAt target).val =
      (tr.tableauAt (target + 1)).T (target + 1) (tr.bumpColAt (target + 1)) := by
  induction tr generalizing target with
  | done B =>
      omega
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases hsucc : target + 1 = row₀
      · have htarget_eq : target = row₀ - 1 := by omega
        subst target
        have hne : row₀ - 1 ≠ row₀ := by omega
        simp [movingAt, tableauAt, bumpColAt, hsucc, hne, tail.movingAt_self, B.bumped_eq]
      · have htail : target + 1 ≤ row₀ - 1 := by omega
        have htarget_ne : target ≠ row₀ := by omega
        simpa [movingAt, tableauAt, bumpColAt, hsucc, htarget_ne] using ih htail

theorem movingAt_le_movingAt_of_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row r s : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (hrs : r ≤ s) (hsrow : s ≤ row) :
    tr.movingAt r ≤ tr.movingAt s := by
  induction tr generalizing r s with
  | done B =>
      have hr0 : r = 0 := by omega
      have hs0 : s = 0 := by omega
      subst r
      subst s
      simp [movingAt]
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases hs_eq : s = row₀
      · subst s
        by_cases hr_eq : r = row₀
        · subst r
          simp [movingAt]
        · have hr_tail : r ≤ row₀ - 1 := by omega
          have htail_le : tail.movingAt r ≤ B.bumped := by
            simpa [tail.movingAt_self] using ih hr_tail le_rfl
          have hbumped_le : B.bumped ≤ moving₀ := by
            rw [Fin.le_def]
            exact le_of_lt B.bumped_lt_moving
          simpa [movingAt, hr_eq] using le_trans htail_le hbumped_le
      · have hs_tail : s ≤ row₀ - 1 := by omega
        by_cases hr_eq : r = row₀
        · omega
        · have hr_tail : r ≤ row₀ - 1 := by omega
          simpa [movingAt, hs_eq, hr_eq] using ih hrs hs_tail

theorem not_valid_at_right_of_bumpColAt_lt {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N}
    {row target : ℕ} {moving y : Fin N}
    (trx : ReverseRowInsertionTrace N T row moving)
    (trY : ReverseRowInsertionTrace N S target y)
    (htarget : target ≤ row)
    (hcell :
      ∀ {r : ℕ}, r ≤ target → (r, trY.bumpColAt r) ∈ μ)
    (hcols :
      ∀ {r : ℕ}, r ≤ target → trx.bumpColAt r < trY.bumpColAt r) :
    ∀ {r : ℕ}, r ≤ target →
      (trx.movingAt r).val ≤
        (trx.tableauAt r).T r (trY.bumpColAt r) := by
  intro r hr
  exact trx.movingAt_le_tableauAt_of_bumpColAt_lt
    (by omega) (hcols hr) (hcell hr)

theorem not_valid_at_right_of_bumpColAt_lt_floor {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N}
    {row target floor : ℕ} {moving y : Fin N}
    (trx : ReverseRowInsertionTrace N T row moving)
    (trY : ReverseRowInsertionTrace N S target y)
    (htarget : target ≤ row)
    (hcell :
      ∀ {r : ℕ}, r ≤ target → (r, trY.bumpColAt r) ∈ μ)
    (hleft :
      ∀ {r : ℕ}, r ≤ target → trx.bumpColAt r < floor)
    (hright :
      ∀ {r : ℕ}, r ≤ target → floor ≤ trY.bumpColAt r) :
    ∀ {r : ℕ}, r ≤ target →
      (trx.movingAt r).val ≤
        (trx.tableauAt r).T r (trY.bumpColAt r) := by
  apply not_valid_at_right_of_bumpColAt_lt trx trY htarget hcell
  intro r hr
  exact lt_of_lt_of_le (hleft hr) (hright hr)

theorem bumpColAt_mem {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) (htarget : target ≤ row) :
    (target, tr.bumpColAt target) ∈ μ := by
  induction tr generalizing target with
  | done B =>
      have htarget0 : target = 0 := by omega
      subst target
      simpa [bumpColAt] using B.location.cell_mem
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases htarget_eq : target = row₀
      · subst target
        simpa [bumpColAt] using B.location.cell_mem
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        simpa [bumpColAt, htarget_eq] using ih htarget_tail

theorem lowerCap_le_bumpColAt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target cap : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (hcap : tr.RespectsLowerCap cap) (htarget : target ≤ row) :
    cap ≤ tr.bumpColAt target := by
  induction tr generalizing target cap with
  | done B =>
      have htarget0 : target = 0 := by omega
      subst target
      simpa [RespectsLowerCap, bumpColAt] using hcap
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases htarget_eq : target = row₀
      · subst target
        simpa [RespectsLowerCap, bumpColAt] using hcap.1
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        have htail : B.location.col ≤ tail.bumpColAt target :=
          ih hcap.2 htarget_tail
        have hcap_le : cap ≤ B.location.col := hcap.1
        have hcap_tail : cap ≤ tail.bumpColAt target := le_trans hcap_le htail
        simpa [bumpColAt, htarget_eq] using hcap_tail

theorem bumpColAt_anti_of_respectsLowerCap {N cap : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row r s : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (hcap : tr.RespectsLowerCap cap) (hrs : r ≤ s) (hsrow : s ≤ row) :
    tr.bumpColAt s ≤ tr.bumpColAt r := by
  induction tr generalizing r s cap with
  | done B =>
      have hr0 : r = 0 := by omega
      have hs0 : s = 0 := by omega
      subst r
      subst s
      simp [bumpColAt]
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases hs_eq : s = row₀
      · subst s
        by_cases hr_eq : r = row₀
        · subst r
          simp [bumpColAt]
        · have hr_tail : r ≤ row₀ - 1 := by omega
          have htail_col : B.location.col ≤ tail.bumpColAt r :=
            tail.lowerCap_le_bumpColAt hcap.2 hr_tail
          simpa [bumpColAt, hr_eq] using htail_col
      · have hs_tail : s ≤ row₀ - 1 := by omega
        by_cases hr_eq : r = row₀
        · subst r
          omega
        · have hr_tail : r ≤ row₀ - 1 := by omega
          simpa [bumpColAt, hs_eq, hr_eq] using
            ih hcap.2 hrs hs_tail

theorem bumpColAt_zero_eq_topCol {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) :
    tr.bumpColAt 0 = tr.topCol := by
  induction tr with
  | done B =>
      simp [bumpColAt, topCol]
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      have hne : 0 ≠ row₀ := by omega
      simp [bumpColAt, topCol, hne, ih]

theorem bumpColAt_le_topCol_of_respectsLowerCap {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target cap : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (hcap : tr.RespectsLowerCap cap) (htarget : target ≤ row) :
    tr.bumpColAt target ≤ tr.topCol := by
  have h := tr.bumpColAt_anti_of_respectsLowerCap hcap (r := 0) (s := target)
    (Nat.zero_le target) htarget
  simpa [tr.bumpColAt_zero_eq_topCol] using h

theorem bumpColAt_lt_floor_of_topCol_lt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target cap floor : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (hcap : tr.RespectsLowerCap cap) (htarget : target ≤ row)
    (htop : tr.topCol < floor) :
    tr.bumpColAt target < floor :=
  lt_of_le_of_lt (tr.bumpColAt_le_topCol_of_respectsLowerCap hcap htarget) htop

theorem not_valid_at_right_of_bumpColAt_lt_respectsLowerCap {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N}
    {row target floor : ℕ} {moving y : Fin N}
    (trx : ReverseRowInsertionTrace N T row moving)
    (trY : ReverseRowInsertionTrace N S target y)
    (htarget : target ≤ row)
    (hcell :
      ∀ {r : ℕ}, r ≤ target → (r, trY.bumpColAt r) ∈ μ)
    (hleft :
      ∀ {r : ℕ}, r ≤ target → trx.bumpColAt r < floor)
    (hcapY : trY.RespectsLowerCap floor) :
    ∀ {r : ℕ}, r ≤ target →
      (trx.movingAt r).val ≤
        (trx.tableauAt r).T r (trY.bumpColAt r) := by
  apply not_valid_at_right_of_bumpColAt_lt_floor trx trY htarget hcell hleft
  intro r hr
  exact trY.lowerCap_le_bumpColAt hcapY hr

theorem tableauAt_entry_eq_of_row_le_target {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row target : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    (htarget : target ≤ row) {i j : ℕ} (hi : i ≤ target) :
    (tr.tableauAt target).T i j = T.T i j := by
  induction tr generalizing target with
  | done B =>
      simp [tableauAt]
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases htarget_eq : target = row₀
      · simp [tableauAt, htarget_eq]
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        have htail : (tail.tableauAt target).T i j = B.tableau.T i j :=
          ih htarget_tail hi
        have hB : B.tableau.T i j = T₀.T i j := by
          rw [B.unchanged_of_ne]
          intro hp
          have hirow : i = row₀ := congrArg Prod.fst hp
          omega
        simpa [tableauAt, htarget_eq] using htail.trans hB

/-- Reverse row insertion ejects a value strictly smaller than the value currently moving
through the trace. -/
theorem result_value_lt_moving {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) :
    tr.result.2.val < moving.val := by
  induction tr with
  | done B =>
      exact B.bumped_lt_moving
  | bump hrow B tail ih =>
      exact lt_trans ih B.bumped_lt_moving

/-- The ejected value is weakly bounded by the value currently moving through the trace. -/
theorem result_value_le_moving {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N}
    {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) :
    tr.result.2 ≤ moving := by
  rw [Fin.le_def]
  exact le_of_lt tr.result_value_lt_moving

theorem result_value_le_movingAt_of_target_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) {target : ℕ}
    (htarget : target ≤ row) :
    tr.result.2 ≤ tr.movingAt target := by
  induction tr generalizing target
  case done B =>
      simp only [result, movingAt]
      exact le_of_lt B.bumped_lt_moving
  case bump T₀ row₀ moving₀ hrow B tail ih =>
      unfold movingAt
      by_cases htarget_eq : target = row₀
      · simp only [result, htarget_eq, ↓reduceIte]
        rw [Fin.le_def]
        exact le_trans (Fin.le_def.mp tail.result_value_le_moving) (le_of_lt B.bumped_lt_moving)
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        simp only [result, htarget_eq, ↓reduceIte, ge_iff_le]
        exact ih htarget_tail

/-- Trace-level comparison for reverse row insertion.

If two traces start in the same row with weakly ordered moving values, and the two
tableaux agree in all rows weakly above the current row, then the ejected values are
weakly ordered in the same direction. -/
theorem result_value_le_of_moving_le_of_rows_eq {N : ℕ} {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (trx : ReverseRowInsertionTrace N T row x)
    (trY : ReverseRowInsertionTrace N S row y)
    (hxy : x ≤ y)
    (hrows : ∀ {i j : ℕ}, i ≤ row → (i, j) ∈ μ → S.T i j = T.T i j) :
    trx.result.2 ≤ trY.result.2 := by
  induction trx generalizing S y with
  | done Bx =>
      cases trY with
      | done By =>
          exact Bx.bumped_le_of_moving_le_of_row_eq By hxy (fun {j} hcell => hrows le_rfl hcell)
      | bump hrow By tail =>
          exact False.elim (hrow rfl)
  | bump hrowx Bx tailx ih =>
      cases trY with
      | done By =>
          exact False.elim (hrowx rfl)
      | bump hrowy By taily =>
          have hbumped : Bx.bumped ≤ By.bumped :=
            Bx.bumped_le_of_moving_le_of_row_eq By hxy (fun {j} hcell => hrows le_rfl hcell)
          exact ih taily hbumped (by
            intro i j hi hcell
            calc
              By.tableau.T i j = S.T i j := by
                rw [By.unchanged_of_ne]
                intro hp
                have hirow := congrArg Prod.fst hp
                omega
              _ = Bx.tableau.T i j := by
                rw [Bx.unchanged_of_ne]
                · exact hrows (by omega) hcell
                · intro hp
                  have hirow := congrArg Prod.fst hp
                  omega)

theorem topCol_le_of_moving_le_of_rows_eq {N : ℕ} {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (trx : ReverseRowInsertionTrace N T row x)
    (trY : ReverseRowInsertionTrace N S row y)
    (hxy : x ≤ y)
    (hrows : ∀ {i j : ℕ}, i ≤ row → (i, j) ∈ μ → S.T i j = T.T i j) :
    trx.topCol ≤ trY.topCol := by
  induction trx generalizing S y with
  | done Bx =>
      cases trY with
      | done By =>
          exact Bx.location.col_le_of_moving_le_of_row_eq By.location hxy
            (fun {j} hcell => hrows le_rfl hcell)
      | bump hrow By tail =>
          exact False.elim (hrow rfl)
  | bump hrowx Bx tailx ih =>
      cases trY with
      | done By =>
          exact False.elim (hrowx rfl)
      | bump hrowy By taily =>
          have hbumped : Bx.bumped ≤ By.bumped :=
            Bx.bumped_le_of_moving_le_of_row_eq By hxy
              (fun {j} hcell => hrows le_rfl hcell)
          simpa [topCol] using ih taily hbumped (by
            intro i j hi hcell
            calc
              By.tableau.T i j = S.T i j := by
                rw [By.unchanged_of_ne]
                intro hp
                have hirow := congrArg Prod.fst hp
                omega
              _ = Bx.tableau.T i j := by
                rw [Bx.unchanged_of_ne]
                · exact hrows (by omega) hcell
                · intro hp
                  have hirow := congrArg Prod.fst hp
                  omega)

theorem topCol_lt_of_moving_le_of_rows_eq_of_not_valid_at_right {N : ℕ}
    {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
    (trx : ReverseRowInsertionTrace N T row x)
    (trY : ReverseRowInsertionTrace N S row y)
    (hxy : x ≤ y)
    (hrows : ∀ {i j : ℕ}, i ≤ row → (i, j) ∈ μ → S.T i j = T.T i j)
    (hnot :
      ∀ {target : ℕ}, target ≤ row →
        (trx.movingAt target).val ≤
          (trx.tableauAt target).T target (trY.bumpColAt target)) :
    trx.topCol < trY.topCol := by
  induction trx generalizing S y with
  | done Bx =>
      cases trY with
      | done By =>
          simpa [topCol] using
            Bx.location.col_lt_of_moving_le_of_row_eq_of_not_valid_at_right
              By.location hxy (fun {j} hcell => hrows le_rfl hcell)
              (by simpa [movingAt, tableauAt, bumpColAt] using hnot le_rfl)
      | bump hrow By tail =>
          exact False.elim (hrow rfl)
  | bump hrowx Bx tailx ih =>
      cases trY with
      | done By =>
          exact False.elim (hrowx rfl)
      | bump hrowy By taily =>
          have hbumped : Bx.bumped ≤ By.bumped :=
            Bx.bumped_le_of_moving_le_of_row_eq By hxy
              (fun {j} hcell => hrows le_rfl hcell)
          simpa [topCol] using ih taily hbumped (by
            intro i j hi hcell
            calc
              By.tableau.T i j = S.T i j := by
                rw [By.unchanged_of_ne]
                intro hp
                have hirow := congrArg Prod.fst hp
                omega
              _ = Bx.tableau.T i j := by
                rw [Bx.unchanged_of_ne]
                · exact hrows (by omega) hcell
                · intro hp
                  have hirow := congrArg Prod.fst hp
                  omega) (by
            intro target htarget
            have h := hnot (target := target) (by omega)
            rw [movingAt_bump_of_target_le_pred hrowx Bx tailx htarget] at h
            rw [tableauAt_bump_of_target_le_pred hrowx Bx tailx htarget] at h
            rw [bumpColAt_bump_of_target_le_pred hrowy By taily htarget] at h
            exact h)

theorem topCol_lt_of_moving_le_of_rows_equiv_of_not_valid_at_right {N : ℕ}
    {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {x y : Fin N}
    (trx : ReverseRowInsertionTrace N T row x)
    (trY : ReverseRowInsertionTrace N S row y)
    (hxy : x ≤ y)
    (hμν : ∀ {i j : ℕ}, i ≤ row → (i, j) ∈ μ → (i, j) ∈ ν)
    (hνμ : ∀ {i j : ℕ}, i ≤ row → (i, j) ∈ ν → (i, j) ∈ μ)
    (hrows :
      ∀ {i j : ℕ}, i ≤ row → (i, j) ∈ μ → (i, j) ∈ ν →
        S.T i j = T.T i j)
    (hnot :
      ∀ {target : ℕ}, target ≤ row →
        (trx.movingAt target).val ≤
          (trx.tableauAt target).T target (trY.bumpColAt target)) :
    trx.topCol < trY.topCol := by
  induction trx generalizing ν S y with
  | done Bx =>
      cases trY with
      | done By =>
          simpa [topCol] using
            Bx.location.col_lt_of_moving_le_of_row_equiv_of_not_valid_at_right
              By.location hxy
              (fun {j} hcell => hμν le_rfl hcell)
              (fun {j} hcellμ hcellν => hrows le_rfl hcellμ hcellν)
              (by simpa [movingAt, tableauAt, bumpColAt] using hnot le_rfl)
      | bump hrow By tail =>
          exact False.elim (hrow rfl)
  | bump hrowx Bx tailx ih =>
      cases trY with
      | done By =>
          exact False.elim (hrowx rfl)
      | bump hrowy By taily =>
          have hbumped : Bx.bumped ≤ By.bumped :=
            Bx.bumped_le_of_moving_le_of_row_equiv By hxy
              (fun {j} hcell => hμν le_rfl hcell)
              (fun {j} hcell => hνμ le_rfl hcell)
              (fun {j} hcellμ hcellν => hrows le_rfl hcellμ hcellν)
          simpa [topCol] using ih taily hbumped (by
            intro i j hi hcell
            exact hμν (by omega) hcell) (by
            intro i j hi hcell
            exact hνμ (by omega) hcell) (by
            intro i j hi hcellμ hcellν
            calc
              By.tableau.T i j = S.T i j := by
                rw [By.unchanged_of_ne]
                intro hp
                have hirow := congrArg Prod.fst hp
                omega
              _ = Bx.tableau.T i j := by
                rw [Bx.unchanged_of_ne]
                · exact hrows (by omega) hcellμ hcellν
                · intro hp
                  have hirow := congrArg Prod.fst hp
                  omega) (by
            intro target htarget
            have h := hnot (target := target) (by omega)
            rw [movingAt_bump_of_target_le_pred hrowx Bx tailx htarget] at h
            rw [tableauAt_bump_of_target_le_pred hrowx Bx tailx htarget] at h
            rw [bumpColAt_bump_of_target_le_pred hrowy By taily htarget] at h
            exact h)

theorem topCol_lt_of_movingAt_le_of_rows_eq_of_not_valid_at_right {N : ℕ}
    {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row target : ℕ} {moving y : Fin N}
    (trx : ReverseRowInsertionTrace N T row moving)
    (trY : ReverseRowInsertionTrace N S target y)
    (htarget : target ≤ row)
    (hmov : trx.movingAt target ≤ y)
    (hrows :
      ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ →
        S.T i j = (trx.tableauAt target).T i j)
    (hnot :
      ∀ {r : ℕ}, r ≤ target →
        (trx.movingAt r).val ≤
          (trx.tableauAt r).T r (trY.bumpColAt r)) :
    trx.topCol < trY.topCol := by
  induction trx generalizing S y target
  case done B =>
      have htarget0 : target = 0 := by omega
      subst target
      simpa [movingAt, tableauAt] using
        topCol_lt_of_moving_le_of_rows_eq_of_not_valid_at_right
          (ReverseRowInsertionTrace.done B) trY hmov hrows (by
            intro r hr
            have hr0 : r = 0 := by omega
            subst r
            simpa [movingAt, tableauAt] using hnot le_rfl)
  case bump T₀ row₀ moving₀ hrow B tail ih =>
      by_cases htarget_eq : target = row₀
      · subst target
        have hmov0 : moving₀ ≤ y := by
          simpa [movingAt] using hmov
        have hrows0 :
            ∀ {i j : ℕ}, i ≤ row₀ → (i, j) ∈ μ → S.T i j = T₀.T i j := by
          intro i j hi hcell
          simpa [tableauAt] using hrows hi hcell
        have hnot0 :
            ∀ {r : ℕ}, r ≤ row₀ →
              ((ReverseRowInsertionTrace.bump hrow B tail).movingAt r).val ≤
                ((ReverseRowInsertionTrace.bump hrow B tail).tableauAt r).T r
                  (trY.bumpColAt r) := by
          intro r hr
          exact hnot hr
        simpa [movingAt, tableauAt] using
          topCol_lt_of_moving_le_of_rows_eq_of_not_valid_at_right
            (ReverseRowInsertionTrace.bump hrow B tail) trY hmov0 hrows0 hnot0
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        have hmov_tail : tail.movingAt target ≤ y := by
          simpa [movingAt, htarget_eq] using hmov
        have hrows_tail :
            ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ →
              S.T i j = (tail.tableauAt target).T i j := by
          intro i j hi hcell
          simpa [tableauAt, htarget_eq] using hrows hi hcell
        have hnot_tail :
            ∀ {r : ℕ}, r ≤ target →
              (tail.movingAt r).val ≤ (tail.tableauAt r).T r (trY.bumpColAt r) := by
          intro r hr
          have hr_ne : r ≠ row₀ := by omega
          simpa [movingAt, tableauAt, hr_ne] using hnot hr
        simpa [topCol] using
          ih trY htarget_tail hmov_tail hrows_tail hnot_tail

theorem topCol_lt_of_movingAt_le_of_rows_equiv_of_not_valid_at_right {N : ℕ}
    {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row target : ℕ} {moving y : Fin N}
    (trx : ReverseRowInsertionTrace N T row moving)
    (trY : ReverseRowInsertionTrace N S target y)
    (htarget : target ≤ row)
    (hmov : trx.movingAt target ≤ y)
    (hμν : ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ → (i, j) ∈ ν)
    (hνμ : ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ ν → (i, j) ∈ μ)
    (hrows :
      ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ → (i, j) ∈ ν →
        S.T i j = (trx.tableauAt target).T i j)
    (hnot :
      ∀ {r : ℕ}, r ≤ target →
        (trx.movingAt r).val ≤
          (trx.tableauAt r).T r (trY.bumpColAt r)) :
    trx.topCol < trY.topCol := by
  induction trx generalizing ν S y target
  case done B =>
      have htarget0 : target = 0 := by omega
      subst target
      simpa [movingAt, tableauAt] using
        topCol_lt_of_moving_le_of_rows_equiv_of_not_valid_at_right
          (ReverseRowInsertionTrace.done B) trY hmov hμν hνμ hrows (by
            intro r hr
            have hr0 : r = 0 := by omega
            subst r
            simpa [movingAt, tableauAt] using hnot le_rfl)
  case bump T₀ row₀ moving₀ hrow B tail ih =>
      by_cases htarget_eq : target = row₀
      · subst target
        have hmov0 : moving₀ ≤ y := by
          simpa [movingAt] using hmov
        have hrows0 :
            ∀ {i j : ℕ}, i ≤ row₀ → (i, j) ∈ μ → (i, j) ∈ ν →
              S.T i j = T₀.T i j := by
          intro i j hi hcellμ hcellν
          simpa [tableauAt] using hrows hi hcellμ hcellν
        have hnot0 :
            ∀ {r : ℕ}, r ≤ row₀ →
              ((ReverseRowInsertionTrace.bump hrow B tail).movingAt r).val ≤
                ((ReverseRowInsertionTrace.bump hrow B tail).tableauAt r).T r
                  (trY.bumpColAt r) := by
          intro r hr
          exact hnot hr
        simpa [movingAt, tableauAt] using
          topCol_lt_of_moving_le_of_rows_equiv_of_not_valid_at_right
            (ReverseRowInsertionTrace.bump hrow B tail) trY hmov0 hμν hνμ hrows0 hnot0
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        have hmov_tail : tail.movingAt target ≤ y := by
          simpa [movingAt, htarget_eq] using hmov
        have hrows_tail :
            ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ → (i, j) ∈ ν →
              S.T i j = (tail.tableauAt target).T i j := by
          intro i j hi hcellμ hcellν
          simpa [tableauAt, htarget_eq] using hrows hi hcellμ hcellν
        have hnot_tail :
            ∀ {r : ℕ}, r ≤ target →
              (tail.movingAt r).val ≤ (tail.tableauAt r).T r (trY.bumpColAt r) := by
          intro r hr
          have hr_ne : r ≠ row₀ := by omega
          simpa [movingAt, tableauAt, hr_ne] using hnot hr
        simpa [topCol] using
          ih trY htarget_tail hmov_tail hμν hνμ hrows_tail hnot_tail

theorem topCol_lt_of_movingAt_le_of_rows_equiv_of_bumpColAt_lt {N : ℕ}
    {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row target : ℕ} {moving y : Fin N}
    (trx : ReverseRowInsertionTrace N T row moving)
    (trY : ReverseRowInsertionTrace N S target y)
    (htarget : target ≤ row)
    (hmov : trx.movingAt target ≤ y)
    (hμν : ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ → (i, j) ∈ ν)
    (hνμ : ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ ν → (i, j) ∈ μ)
    (hrows :
      ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ → (i, j) ∈ ν →
        S.T i j = (trx.tableauAt target).T i j)
    (hcols :
      ∀ {r : ℕ}, r ≤ target → trx.bumpColAt r < trY.bumpColAt r) :
    trx.topCol < trY.topCol := by
  apply topCol_lt_of_movingAt_le_of_rows_equiv_of_not_valid_at_right
    trx trY htarget hmov hμν hνμ hrows
  apply not_valid_at_right_of_bumpColAt_lt trx trY htarget
  · intro r hr
    exact hνμ hr (trY.bumpColAt_mem hr)
  · exact hcols

def StrictlyLeftUpTo {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N}
    {row target : ℕ} {moving y : Fin N}
    (left : ReverseRowInsertionTrace N T row moving)
    (right : ReverseRowInsertionTrace N S target y) (limit : ℕ) : Prop :=
  ∀ {r : ℕ}, r ≤ limit → left.bumpColAt r < right.bumpColAt r

theorem topCol_lt_of_movingAt_le_of_rows_equiv_of_strictlyLeftUpTo {N : ℕ}
    {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row target : ℕ} {moving y : Fin N}
    (trx : ReverseRowInsertionTrace N T row moving)
    (trY : ReverseRowInsertionTrace N S target y)
    (htarget : target ≤ row)
    (hmov : trx.movingAt target ≤ y)
    (hμν : ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ → (i, j) ∈ ν)
    (hνμ : ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ ν → (i, j) ∈ μ)
    (hrows :
      ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ → (i, j) ∈ ν →
        S.T i j = (trx.tableauAt target).T i j)
    (hleft : StrictlyLeftUpTo trx trY target) :
    trx.topCol < trY.topCol := by
  exact topCol_lt_of_movingAt_le_of_rows_equiv_of_bumpColAt_lt
    trx trY htarget hmov hμν hνμ hrows hleft

theorem topCol_lt_of_strictlyLeftUpTo {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N}
    {row target limit : ℕ} {moving y : Fin N}
    (left : ReverseRowInsertionTrace N T row moving)
    (right : ReverseRowInsertionTrace N S target y)
    (hleft : StrictlyLeftUpTo left right limit) :
    left.topCol < right.topCol := by
  have hzero : left.bumpColAt 0 < right.bumpColAt 0 := hleft (Nat.zero_le limit)
  simpa [left.bumpColAt_zero_eq_topCol, right.bumpColAt_zero_eq_topCol] using hzero

theorem result_value_le_of_movingAt_le_of_rows_eq {N : ℕ} {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row target : ℕ} {moving y : Fin N}
    (trx : ReverseRowInsertionTrace N T row moving)
    (trY : ReverseRowInsertionTrace N S target y)
    (htarget : target ≤ row)
    (hmov : trx.movingAt target ≤ y)
    (hrows :
      ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ →
        S.T i j = (trx.tableauAt target).T i j) :
    trx.result.2 ≤ trY.result.2 := by
  induction trx generalizing S y target
  case done B =>
      have htarget0 : target = 0 := by omega
      subst target
      simpa [movingAt, tableauAt] using
        result_value_le_of_moving_le_of_rows_eq
          (ReverseRowInsertionTrace.done B) trY hmov hrows
  case bump T₀ row₀ moving₀ hrow B tail ih =>
      by_cases htarget_eq : target = row₀
      · subst target
        have hmov0 : moving₀ ≤ y := by
          simpa [movingAt] using hmov
        have hrows0 :
            ∀ {i j : ℕ}, i ≤ row₀ → (i, j) ∈ μ → S.T i j = T₀.T i j := by
          intro i j hi hcell
          simpa [tableauAt] using hrows hi hcell
        simpa [movingAt, tableauAt] using
          result_value_le_of_moving_le_of_rows_eq
            (ReverseRowInsertionTrace.bump hrow B tail) trY hmov0 hrows0
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        have hmov_tail : tail.movingAt target ≤ y := by
          simpa [movingAt, htarget_eq] using hmov
        have hrows_tail :
            ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ →
              S.T i j = (tail.tableauAt target).T i j := by
          intro i j hi hcell
          simpa [tableauAt, htarget_eq] using hrows hi hcell
        simpa [ReverseRowInsertionTrace.result] using
          ih trY htarget_tail hmov_tail hrows_tail

theorem topCol_le_of_movingAt_le_of_rows_eq {N : ℕ} {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row target : ℕ} {moving y : Fin N}
    (trx : ReverseRowInsertionTrace N T row moving)
    (trY : ReverseRowInsertionTrace N S target y)
    (htarget : target ≤ row)
    (hmov : trx.movingAt target ≤ y)
    (hrows :
      ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ →
        S.T i j = (trx.tableauAt target).T i j) :
    trx.topCol ≤ trY.topCol := by
  induction trx generalizing S y target
  case done B =>
      have htarget0 : target = 0 := by omega
      subst target
      simpa [movingAt, tableauAt] using
        topCol_le_of_moving_le_of_rows_eq
          (ReverseRowInsertionTrace.done B) trY hmov hrows
  case bump T₀ row₀ moving₀ hrow B tail ih =>
      by_cases htarget_eq : target = row₀
      · subst target
        have hmov0 : moving₀ ≤ y := by
          simpa [movingAt] using hmov
        have hrows0 :
            ∀ {i j : ℕ}, i ≤ row₀ → (i, j) ∈ μ → S.T i j = T₀.T i j := by
          intro i j hi hcell
          simpa [tableauAt] using hrows hi hcell
        simpa [movingAt, tableauAt] using
          topCol_le_of_moving_le_of_rows_eq
            (ReverseRowInsertionTrace.bump hrow B tail) trY hmov0 hrows0
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        have hmov_tail : tail.movingAt target ≤ y := by
          simpa [movingAt, htarget_eq] using hmov
        have hrows_tail :
            ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ →
              S.T i j = (tail.tableauAt target).T i j := by
          intro i j hi hcell
          simpa [tableauAt, htarget_eq] using hrows hi hcell
        simpa [topCol] using ih trY htarget_tail hmov_tail hrows_tail

theorem result_value_le_of_top_row_entries_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) {a : ℕ}
    (htop : ∀ {j : ℕ}, (0, j) ∈ μ → T.T 0 j ≤ a) :
    tr.result.2.val ≤ a := by
  induction tr with
  | done B =>
      change B.bumped.val ≤ a
      rw [← B.bumped_eq]
      exact htop B.location.cell_mem
  | bump hrow B tail ih =>
      have htop' : ∀ {j : ℕ}, (0, j) ∈ μ → B.tableau.T 0 j ≤ a := by
        intro j hcell
        rw [B.unchanged_of_ne]
        · exact htop hcell
        · intro hp
          have hrow0 : 0 = _ := congrArg Prod.fst hp
          omega
      exact ih htop'

theorem topCol_mem {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) :
    (0, tr.topCol) ∈ μ := by
  induction tr with
  | done B =>
      simpa [topCol] using B.location.cell_mem
  | bump hrow B tail ih =>
      simpa [topCol] using ih

theorem result_value_eq_initial_top_entry {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving) :
    tr.result.2.val = T.T 0 tr.topCol := by
  induction tr with
  | done B =>
      simpa [ReverseRowInsertionTrace.result, topCol] using B.bumped_eq.symm
  | bump hrow B tail ih =>
      have htop_unchanged := B.unchanged_of_ne (i := 0) (j := tail.topCol) (by
          intro hp
          have hrow0 := congrArg Prod.fst hp
          omega)
      simpa [ReverseRowInsertionTrace.result, topCol] using ih.trans htop_unchanged

theorem top_row_entry_le_result_value_of_col_le_topCol {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    {j : ℕ} (hcol : j ≤ tr.topCol) :
    T.T 0 j ≤ tr.result.2.val := by
  rw [tr.result_value_eq_initial_top_entry]
  rcases lt_or_eq_of_le hcol with hlt | heq
  · exact T.T.row_weak hlt tr.topCol_mem
  · simp [heq]

theorem topCol_ge_cap_of_respectsLowerCap {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    {tr : ReverseRowInsertionTrace N T row moving} {cap : ℕ}
    (hcap : tr.RespectsLowerCap cap) :
    cap ≤ tr.topCol := by
  induction tr generalizing cap with
  | done B =>
      simpa [RespectsLowerCap, topCol] using hcap
  | bump hrow B tail ih =>
      exact le_trans hcap.1 (ih hcap.2)

theorem result_tableau_eq_of_row_gt_start {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    {i j : ℕ} (hi : row < i) :
    tr.result.1.T i j = T.T i j := by
  induction tr with
  | done B =>
      simpa [ReverseRowInsertionTrace.result] using
        B.unchanged_of_ne (i := i) (j := j) (by
          intro hp
          have hirow : i = 0 := congrArg Prod.fst hp
          omega)
  | bump hrow B tail ih =>
      have htail : tail.result.1.T i j = B.tableau.T i j := ih (by omega)
      have hB := B.unchanged_of_ne (i := i) (j := j) (by
          intro hp
          have hirow := congrArg Prod.fst hp
          omega)
      simpa [ReverseRowInsertionTrace.result] using htail.trans hB

theorem result_tableau_entry_eq_of_col_lt_bumpColAt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    {i j : ℕ} (hi : i ≤ row) (hj : j < tr.bumpColAt i) :
    tr.result.1.T i j = T.T i j := by
  induction tr generalizing i with
  | done B =>
      have hi0 : i = 0 := by omega
      subst i
      have hj0 : j < B.location.col := by
        simpa [bumpColAt] using hj
      simpa [ReverseRowInsertionTrace.result, bumpColAt] using
        B.unchanged_of_ne (i := 0) (j := j) (by
          intro hp
          have hcol : j = B.location.col := congrArg Prod.snd hp
          omega)
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases hirow : i = row₀
      · subst i
        have htail :
            tail.result.1.T row₀ j = B.tableau.T row₀ j :=
          tail.result_tableau_eq_of_row_gt_start (by omega)
        have hB : B.tableau.T row₀ j = T₀.T row₀ j := by
          rw [B.unchanged_of_ne]
          intro hp
          have hcol : j = B.location.col := congrArg Prod.snd hp
          have hj' : j < B.location.col := by
            simpa [bumpColAt] using hj
          omega
        simpa [ReverseRowInsertionTrace.result] using htail.trans hB
      · have hi_tail : i ≤ row₀ - 1 := by omega
        have hj_tail : j < tail.bumpColAt i := by
          simpa [bumpColAt, hirow] using hj
        have htail : tail.result.1.T i j = B.tableau.T i j :=
          ih hi_tail hj_tail
        have hB : B.tableau.T i j = T₀.T i j := by
          rw [B.unchanged_of_ne]
          intro hp
          have hrow_eq : i = row₀ := congrArg Prod.fst hp
          exact hirow hrow_eq
        simpa [ReverseRowInsertionTrace.result] using htail.trans hB

theorem result_tableau_entry_eq_movingAt_of_bumpColAt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    {i : ℕ} (hi : i ≤ row) :
    tr.result.1.T i (tr.bumpColAt i) = (tr.movingAt i).val := by
  induction tr generalizing i with
  | done B =>
      have hi0 : i = 0 := by omega
      subst i
      simpa [ReverseRowInsertionTrace.result, bumpColAt, movingAt] using B.replaced_entry
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases hirow : i = row₀
      · subst i
        have htail :
            tail.result.1.T row₀ B.location.col = B.tableau.T row₀ B.location.col :=
          tail.result_tableau_eq_of_row_gt_start (by omega)
        simpa [ReverseRowInsertionTrace.result, bumpColAt, movingAt] using
          htail.trans B.replaced_entry
      · have hi_tail : i ≤ row₀ - 1 := by omega
        have htail :
            tail.result.1.T i (tail.bumpColAt i) = (tail.movingAt i).val :=
          ih hi_tail
        simpa [ReverseRowInsertionTrace.result, bumpColAt, movingAt, hirow] using htail

theorem movingAt_le_result_tableau_entry_of_bumpColAt_lt {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    {i j : ℕ} (hi : i ≤ row) (hcol : tr.bumpColAt i < j)
    (hcell : (i, j) ∈ μ) :
    (tr.movingAt i).val ≤ tr.result.1.T i j := by
  induction tr generalizing i with
  | done B =>
      rename_i Tdone movingdone
      have hi0 : i = 0 := by omega
      subst i
      have hlt' : B.location.col < j := by
        simpa [bumpColAt] using hcol
      have hright := B.location.right_ge hlt' hcell
      have hunchanged : B.tableau.T 0 j = Tdone.T 0 j := by
        rw [B.unchanged_of_ne]
        intro hp
        have hj : j = B.location.col := congrArg Prod.snd hp
        omega
      have hle : movingdone.val ≤ B.tableau.T 0 j := by
        simpa [hunchanged] using hright
      simpa [ReverseRowInsertionTrace.result, movingAt] using hle
  | bump hrow B tail ih =>
      rename_i T₀ row₀ moving₀
      by_cases hirow : i = row₀
      · subst i
        have hlt' : B.location.col < j := by
          simpa [bumpColAt] using hcol
        have hright : moving₀.val ≤ T₀.T row₀ j :=
          B.location.right_ge hlt' hcell
        have hB : B.tableau.T row₀ j = T₀.T row₀ j := by
          rw [B.unchanged_of_ne]
          intro hp
          have hj : j = B.location.col := congrArg Prod.snd hp
          omega
        have htail :
            tail.result.1.T row₀ j = B.tableau.T row₀ j :=
          tail.result_tableau_eq_of_row_gt_start (by omega)
        simpa [ReverseRowInsertionTrace.result, movingAt, bumpColAt, htail, hB] using hright
      · have hi_tail : i ≤ row₀ - 1 := by omega
        have hlt_tail : tail.bumpColAt i < j := by
          simpa [bumpColAt, hirow] using hcol
        have hcell_tail : (i, j) ∈ μ := hcell
        simpa [ReverseRowInsertionTrace.result, movingAt, bumpColAt, hirow] using
          ih hi_tail hlt_tail hcell_tail

theorem movingAt_le_result_tableau_entry_of_bumpColAt_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    {i j : ℕ} (hi : i ≤ row) (hcol : tr.bumpColAt i ≤ j)
    (hcell : (i, j) ∈ μ) :
    (tr.movingAt i).val ≤ tr.result.1.T i j := by
  rcases lt_or_eq_of_le hcol with hlt | heq
  · exact tr.movingAt_le_result_tableau_entry_of_bumpColAt_lt hi hlt hcell
  · subst j
    exact le_of_eq (tr.result_tableau_entry_eq_movingAt_of_bumpColAt hi).symm

theorem result_tableau_top_entry_eq_of_col_lt_topCol {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {moving : Fin N}
    (tr : ReverseRowInsertionTrace N T row moving)
    {j : ℕ} (hj : j < tr.topCol) :
    tr.result.1.T 0 j = T.T 0 j := by
  induction tr with
  | done B =>
      have hj' : j < B.location.col := by
        simpa [topCol] using hj
      simpa [ReverseRowInsertionTrace.result, topCol] using
        B.unchanged_of_ne (i := 0) (j := j) (by
          intro hp
          have hcol : j = B.location.col := congrArg Prod.snd hp
          omega)
  | bump hrow B tail ih =>
      have htail : tail.result.1.T 0 j = B.tableau.T 0 j := by
        exact ih (by simpa [topCol] using hj)
      have hB :=
        B.unchanged_of_ne (i := 0) (j := j) (by
          intro hp
          have hrow0 : 0 = _ := congrArg Prod.fst hp
          omega)
      simpa [ReverseRowInsertionTrace.result] using htail.trans hB

theorem topCol_lt_of_moving_le_of_rows_equiv_result {N : ℕ}
    {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row : ℕ} {x y : Fin N}
    (left : ReverseRowInsertionTrace N S row x)
    (right : ReverseRowInsertionTrace N T row y)
    (hxy : x ≤ y)
    (hνμ : ∀ {i j : ℕ}, i ≤ row → (i, j) ∈ ν → (i, j) ∈ μ)
    (hμν : ∀ {i j : ℕ}, i ≤ row → (i, j) ∈ μ → (i, j) ∈ ν)
    (hrows :
      ∀ {i j : ℕ}, i ≤ row → (i, j) ∈ ν → (i, j) ∈ μ →
        S.T i j = right.result.1.T i j) :
    left.topCol < right.topCol := by
  induction right generalizing ν S x with
  | done Br =>
      cases left with
      | done Bl =>
          have hcellν : (0, Br.location.col) ∈ ν :=
            hμν le_rfl Br.location.cell_mem
          have hnot : x.val ≤ S.T 0 Br.location.col := by
            calc
              x.val ≤ _ := Fin.le_def.mp hxy
              _ = (ReverseRowInsertionTrace.done Br).result.1.T 0 Br.location.col := by
                simpa [ReverseRowInsertionTrace.result] using Br.replaced_entry.symm
              _ = S.T 0 Br.location.col := by
                exact (hrows le_rfl hcellν Br.location.cell_mem).symm
          simpa [topCol] using
            Bl.location.col_lt_of_not_valid_at_col hcellν hnot
      | bump hrow _ _ =>
          exact False.elim (hrow rfl)
  | bump hrow Br tailR ih =>
      cases left with
      | done Bl =>
          exact False.elim (hrow rfl)
      | bump hrowL Bl tailL =>
          rename_i T₀ row₀ y₀
          have hcellν : (row₀, Br.location.col) ∈ ν :=
            hμν le_rfl Br.location.cell_mem
          have hnot : x.val ≤ S.T row₀ Br.location.col := by
            calc
              x.val ≤ y₀.val := Fin.le_def.mp hxy
              _ = (ReverseRowInsertionTrace.bump hrow Br tailR).result.1.T
                    row₀ Br.location.col := by
                simpa [ReverseRowInsertionTrace.result, bumpColAt, movingAt]
                using
                  ((ReverseRowInsertionTrace.bump hrow Br
                  tailR).result_tableau_entry_eq_movingAt_of_bumpColAt
                    (i := row₀) le_rfl).symm
              _ = S.T row₀ Br.location.col := by
                exact (hrows le_rfl hcellν Br.location.cell_mem).symm
          have hcol_lt : Bl.location.col < Br.location.col :=
            Bl.location.col_lt_of_not_valid_at_col hcellν hnot
          have hbumped : Bl.bumped ≤ Br.bumped := by
            rw [Fin.le_def, ← Bl.bumped_eq, ← Br.bumped_eq]
            have hcellμ_left : (row₀, Bl.location.col) ∈ μ :=
              hνμ le_rfl Bl.location.cell_mem
            have hleft_entry :
                S.T row₀ Bl.location.col =
                  (ReverseRowInsertionTrace.bump hrow Br tailR).result.1.T
                    row₀ Bl.location.col :=
              hrows le_rfl Bl.location.cell_mem hcellμ_left
            have hright_unchanged :
                (ReverseRowInsertionTrace.bump hrow Br tailR).result.1.T
                    row₀ Bl.location.col =
                  T₀.T row₀ Bl.location.col :=
              (ReverseRowInsertionTrace.bump hrow Br
              tailR).result_tableau_entry_eq_of_col_lt_bumpColAt
                (i := row₀) le_rfl (by simpa [bumpColAt] using hcol_lt)
            calc
              S.T row₀ Bl.location.col =
                  (ReverseRowInsertionTrace.bump hrow Br tailR).result.1.T
                    row₀ Bl.location.col := hleft_entry
              _ = T₀.T row₀ Bl.location.col := hright_unchanged
              _ ≤ T₀.T row₀ Br.location.col :=
                T₀.T.row_weak hcol_lt Br.location.cell_mem
          have hνμ_tail :
              ∀ {i j : ℕ}, i ≤ row₀ - 1 → (i, j) ∈ ν → (i, j) ∈ μ := by
            intro i j hi hcell
            exact hνμ (by omega) hcell
          have hμν_tail :
              ∀ {i j : ℕ}, i ≤ row₀ - 1 → (i, j) ∈ μ → (i, j) ∈ ν := by
            intro i j hi hcell
            exact hμν (by omega) hcell
          have hrows_tail :
              ∀ {i j : ℕ}, i ≤ row₀ - 1 → (i, j) ∈ ν → (i, j) ∈ μ →
                Bl.tableau.T i j = tailR.result.1.T i j := by
            intro i j hi hcellν hcellμ
            have hBl : Bl.tableau.T i j = S.T i j := by
              rw [Bl.unchanged_of_ne]
              intro hp
              have hrow_eq : i = row₀ := congrArg Prod.fst hp
              omega
            have hrow_entry :
                S.T i j = (ReverseRowInsertionTrace.bump hrow Br tailR).result.1.T i j :=
              hrows (by omega) hcellν hcellμ
            simpa [ReverseRowInsertionTrace.result] using hBl.trans hrow_entry
          simpa [topCol] using
            ih tailL hbumped hνμ_tail hμν_tail hrows_tail

theorem topCol_lt_of_movingAt_le_of_rows_equiv_result {N : ℕ}
    {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N}
    {row target : ℕ} {x y : Fin N}
    (left : ReverseRowInsertionTrace N S row x)
    (right : ReverseRowInsertionTrace N T target y)
    (htarget : target ≤ row)
    (hmov : left.movingAt target ≤ y)
    (hνμ : ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ ν → (i, j) ∈ μ)
    (hμν : ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ μ → (i, j) ∈ ν)
    (hrows :
      ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ ν → (i, j) ∈ μ →
        (left.tableauAt target).T i j = right.result.1.T i j) :
    left.topCol < right.topCol := by
  induction left generalizing target μ T y with
  | done B =>
      have htarget0 : target = 0 := by omega
      subst target
      simpa [movingAt, tableauAt] using
        topCol_lt_of_moving_le_of_rows_equiv_result
          (ReverseRowInsertionTrace.done B) right hmov hνμ hμν hrows
  | bump hrow B tail ih =>
      rename_i S₀ row₀ x₀
      by_cases htarget_eq : target = row₀
      · subst target
        have hmov0 : x₀ ≤ y := by
          simpa [movingAt] using hmov
        have hrows0 :
            ∀ {i j : ℕ}, i ≤ row₀ → (i, j) ∈ ν → (i, j) ∈ μ →
              S₀.T i j = right.result.1.T i j := by
          intro i j hi hcellν hcellμ
          simpa [tableauAt] using hrows hi hcellν hcellμ
        simpa [movingAt, tableauAt] using
          topCol_lt_of_moving_le_of_rows_equiv_result
            (ReverseRowInsertionTrace.bump hrow B tail) right hmov0 hνμ hμν hrows0
      · have htarget_tail : target ≤ row₀ - 1 := by omega
        have hmov_tail : tail.movingAt target ≤ y := by
          simpa [movingAt, htarget_eq] using hmov
        have hrows_tail :
            ∀ {i j : ℕ}, i ≤ target → (i, j) ∈ ν → (i, j) ∈ μ →
              (tail.tableauAt target).T i j = right.result.1.T i j := by
          intro i j hi hcellν hcellμ
          simpa [tableauAt, htarget_eq] using hrows hi hcellν hcellμ
        simpa [topCol] using
          ih right htarget_tail hmov_tail hνμ hμν hrows_tail

end ReverseRowInsertionTrace

/-- Given a reverse-bump location in every nonzero row, one can construct the full
reverse row-insertion trace by recursion on the row index.

This is the purely structural part of reverse insertion. The real mathematical work is
to prove the location hypothesis from a deleted removable corner and semistandardness. -/
theorem exists_reverseRowInsertionTrace {N : ℕ} {μ : YoungDiagram}
    (hstep :
      ∀ (T : BoundedSSYT μ N) (row : ℕ) (moving : Fin N),
        Nonempty (ReverseRowBumpLocation T row moving))
    (T : BoundedSSYT μ N) (row : ℕ) (moving : Fin N) :
    Nonempty (ReverseRowInsertionTrace N T row moving) := by
  induction row generalizing T moving with
  | zero =>
      rcases hstep T 0 moving with ⟨L⟩
      exact ⟨ReverseRowInsertionTrace.done (reverseRowBumpStep T 0 moving L)⟩
  | succ row ih =>
      have hrow : row + 1 ≠ 0 := by omega
      rcases hstep T (row + 1) moving with ⟨L⟩
      let B := reverseRowBumpStep T (row + 1) moving L
      have htail : Nonempty (ReverseRowInsertionTrace N B.tableau ((row + 1) - 1) B.bumped) := by
        simpa using ih B.tableau B.bumped
      exact htail.elim fun tail => ⟨ReverseRowInsertionTrace.bump hrow B tail⟩

/-- Reverse insertion trace from the path invariant at a known lower-bound column. -/
theorem exists_reverseRowInsertionTrace_fromCap {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row cap : ℕ) (moving : Fin N)
    (hcap_mem : (row, cap) ∈ μ)
    (hcap_lt : T.T row cap < moving.val)
    (hbelow :
      ∀ {i j : ℕ}, row < i → cap ≤ j → (i, j) ∈ μ →
        moving.val < T.T i j) :
    Nonempty (ReverseRowInsertionTrace N T row moving) := by
  induction row generalizing T moving cap with
  | zero =>
      rcases exists_reverseRowBumpLocation_fromCap T 0 cap moving
          hcap_mem hcap_lt hbelow with ⟨L⟩
      exact ⟨ReverseRowInsertionTrace.done (reverseRowBumpStep T 0 moving L)⟩
  | succ row ih =>
      rcases exists_reverseRowBumpLocation_fromCap T (row + 1) cap moving
          hcap_mem hcap_lt hbelow with ⟨L⟩
      let B := reverseRowBumpStep T (row + 1) moving L
      have hrow_ne : row + 1 ≠ 0 := by omega
      have hcap_mem' : (row, B.location.col) ∈ μ := by
        exact μ.up_left_mem (by omega) le_rfl B.location.cell_mem
      have hcap_lt' : B.tableau.T row B.location.col < B.bumped.val := by
        rw [B.unchanged_of_ne]
        · rw [← B.bumped_eq]
          exact T.T.col_strict (by omega) B.location.cell_mem
        · intro hp
          have hroweq : row = row + 1 := congrArg Prod.fst hp
          omega
      have hbelow' :
          ∀ {i j : ℕ}, row < i → B.location.col ≤ j → (i, j) ∈ μ →
            B.bumped.val < B.tableau.T i j := by
        intro i j hi hj hmem
        rcases Nat.eq_or_lt_of_le hi with hi_eq | hi_gt
        · subst i
          rcases Nat.eq_or_lt_of_le hj with hj_eq | hj_gt
          · subst j
            rw [B.replaced_entry]
            exact B.bumped_lt_moving
          · rw [B.unchanged_of_ne]
            · exact lt_of_lt_of_le B.bumped_lt_moving
                (B.location.right_ge hj_gt hmem)
            · intro hp
              have hjcontra : j = B.location.col := congrArg Prod.snd hp
              omega
        · have hcell_below : (row + 1, j) ∈ μ :=
            μ.up_left_mem (by omega) le_rfl hmem
          have hrowplus_lt : row + 1 < i := by omega
          have hbumped_lt_rowplus : B.bumped.val < B.tableau.T (row + 1) j := by
            rcases Nat.eq_or_lt_of_le hj with hj_eq | hj_gt
            · subst j
              rw [B.replaced_entry]
              exact B.bumped_lt_moving
            · rw [B.unchanged_of_ne]
              · exact lt_of_lt_of_le B.bumped_lt_moving
                  (B.location.right_ge hj_gt hcell_below)
              · intro hp
                have hjcontra : j = B.location.col := congrArg Prod.snd hp
                omega
          exact lt_trans hbumped_lt_rowplus
            (B.tableau.T.col_strict hrowplus_lt hmem)
      have htail := ih B.tableau B.location.col B.bumped hcap_mem' hcap_lt' hbelow'
      exact htail.elim fun tail =>
        ⟨ReverseRowInsertionTrace.bump hrow_ne B (by simpa using tail)⟩

theorem exists_reverseRowInsertionTrace_fromCap_with_respects {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row cap : ℕ) (moving : Fin N)
    (hcap_mem : (row, cap) ∈ μ)
    (hcap_lt : T.T row cap < moving.val)
    (hbelow :
      ∀ {i j : ℕ}, row < i → cap ≤ j → (i, j) ∈ μ →
        moving.val < T.T i j) :
    ∃ tr : ReverseRowInsertionTrace N T row moving,
      tr.RespectsLowerCap cap := by
  induction row generalizing T moving cap with
  | zero =>
      rcases exists_reverseRowBumpLocation_fromCap T 0 cap moving
          hcap_mem hcap_lt hbelow with ⟨L⟩
      let B := reverseRowBumpStep T 0 moving L
      refine ⟨ReverseRowInsertionTrace.done B, ?_⟩
      simpa [ReverseRowInsertionTrace.RespectsLowerCap, B] using
        L.cap_le_col_of_cap_lt hcap_mem hcap_lt
  | succ row ih =>
      rcases exists_reverseRowBumpLocation_fromCap T (row + 1) cap moving
          hcap_mem hcap_lt hbelow with ⟨L⟩
      let B := reverseRowBumpStep T (row + 1) moving L
      have hrow_ne : row + 1 ≠ 0 := by omega
      have hcap_mem' : (row, B.location.col) ∈ μ := by
        exact μ.up_left_mem (by omega) le_rfl B.location.cell_mem
      have hcap_lt' : B.tableau.T row B.location.col < B.bumped.val := by
        rw [B.unchanged_of_ne]
        · rw [← B.bumped_eq]
          exact T.T.col_strict (by omega) B.location.cell_mem
        · intro hp
          have hroweq : row = row + 1 := congrArg Prod.fst hp
          omega
      have hbelow' :
          ∀ {i j : ℕ}, row < i → B.location.col ≤ j → (i, j) ∈ μ →
            B.bumped.val < B.tableau.T i j := by
        intro i j hi hj hmem
        rcases Nat.eq_or_lt_of_le hi with hi_eq | hi_gt
        · subst i
          rcases Nat.eq_or_lt_of_le hj with hj_eq | hj_gt
          · subst j
            rw [B.replaced_entry]
            exact B.bumped_lt_moving
          · rw [B.unchanged_of_ne]
            · exact lt_of_lt_of_le B.bumped_lt_moving
                (B.location.right_ge hj_gt hmem)
            · intro hp
              have hjcontra : j = B.location.col := congrArg Prod.snd hp
              omega
        · have hcell_below : (row + 1, j) ∈ μ :=
            μ.up_left_mem (by omega) le_rfl hmem
          have hrowplus_lt : row + 1 < i := by omega
          have hbumped_lt_rowplus : B.bumped.val < B.tableau.T (row + 1) j := by
            rcases Nat.eq_or_lt_of_le hj with hj_eq | hj_gt
            · subst j
              rw [B.replaced_entry]
              exact B.bumped_lt_moving
            · rw [B.unchanged_of_ne]
              · exact lt_of_lt_of_le B.bumped_lt_moving
                  (B.location.right_ge hj_gt hcell_below)
              · intro hp
                have hjcontra : j = B.location.col := congrArg Prod.snd hp
                omega
          exact lt_trans hbumped_lt_rowplus
            (B.tableau.T.col_strict hrowplus_lt hmem)
      rcases ih B.tableau B.location.col B.bumped hcap_mem' hcap_lt' hbelow' with
        ⟨tail, htail⟩
      refine ⟨ReverseRowInsertionTrace.bump hrow_ne B (by simpa using tail), ?_⟩
      refine ⟨?_, by simpa using htail⟩
      simpa [B] using L.cap_le_col_of_cap_lt hcap_mem hcap_lt

/-- The genuine existence theorem needed after deleting a removable corner.

This is the next nontrivial mathematical target: starting from the deleted corner value,
prove that each upward step has a rightmost-smaller location satisfying the `below_gt`
condition. -/
theorem exists_reverseRowInsertionTrace_afterDelete {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (hrow : c.1 ≠ 0) :
    let D := deleteCorner T c hc
    Nonempty (ReverseRowInsertionTrace N D.tableau (c.1 - 1) D.value) := by
  classical
  let D := deleteCorner T c hc
  have hpred_lt : c.1 - 1 < c.1 := by omega
  have hpred_cell_old : (c.1 - 1, c.2) ∈ μ :=
    μ.up_left_mem (Nat.le_of_lt hpred_lt) le_rfl D.cell_mem_old
  have hpred_ne : ((c.1 - 1, c.2) : ℕ × ℕ) ≠ c := by
    intro hp
    have hfst : c.1 - 1 = c.1 := congrArg Prod.fst hp
    omega
  have hcap_mem : (c.1 - 1, c.2) ∈ D.shape := by
    exact (D.shape_mem_iff (c.1 - 1, c.2)).1 hpred_cell_old |>.resolve_right hpred_ne
  have hcap_lt : D.tableau.T (c.1 - 1) c.2 < D.value.val := by
    change (if (c.1 - 1, c.2) ∈ D.shape then T.T (c.1 - 1) c.2 else 0) <
      T.T c.1 c.2
    simp only [hcap_mem, ↓reduceIte]
    exact T.T.col_strict hpred_lt D.cell_mem_old
  have hbelow :
      ∀ {i j : ℕ}, c.1 - 1 < i → c.2 ≤ j → (i, j) ∈ D.shape →
        D.value.val < D.tableau.T i j := by
    intro i j hi hj hmem
    exfalso
    have hc_le_i : c.1 ≤ i := by omega
    have hrowLen_le : D.shape.rowLen i ≤ D.shape.rowLen c.1 :=
      D.shape.rowLen_anti c.1 i hc_le_i
    have hrowLen_c : D.shape.rowLen c.1 = c.2 :=
      D.new_shape_rowLen_at_removedCell
    have hj_lt : j < D.shape.rowLen i := by
      rwa [YoungDiagram.mem_iff_lt_rowLen] at hmem
    omega
  exact exists_reverseRowInsertionTrace_fromCap D.tableau (c.1 - 1) c.2 D.value
    hcap_mem hcap_lt hbelow

theorem exists_reverseRowInsertionTrace_afterDelete_with_respects {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (hrow : c.1 ≠ 0) :
    let D := deleteCorner T c hc
    ∃ tr : ReverseRowInsertionTrace N D.tableau (c.1 - 1) D.value,
      tr.RespectsLowerCap c.2 := by
  classical
  let D := deleteCorner T c hc
  have hpred_lt : c.1 - 1 < c.1 := by omega
  have hpred_cell_old : (c.1 - 1, c.2) ∈ μ :=
    μ.up_left_mem (Nat.le_of_lt hpred_lt) le_rfl D.cell_mem_old
  have hpred_ne : ((c.1 - 1, c.2) : ℕ × ℕ) ≠ c := by
    intro hp
    have hfst : c.1 - 1 = c.1 := congrArg Prod.fst hp
    omega
  have hcap_mem : (c.1 - 1, c.2) ∈ D.shape := by
    exact (D.shape_mem_iff (c.1 - 1, c.2)).1 hpred_cell_old |>.resolve_right hpred_ne
  have hcap_lt : D.tableau.T (c.1 - 1) c.2 < D.value.val := by
    change (if (c.1 - 1, c.2) ∈ D.shape then T.T (c.1 - 1) c.2 else 0) <
      T.T c.1 c.2
    simp only [hcap_mem, ↓reduceIte]
    exact T.T.col_strict hpred_lt D.cell_mem_old
  have hbelow :
      ∀ {i j : ℕ}, c.1 - 1 < i → c.2 ≤ j → (i, j) ∈ D.shape →
        D.value.val < D.tableau.T i j := by
    intro i j hi hj hmem
    exfalso
    have hc_le_i : c.1 ≤ i := by omega
    have hrowLen_le : D.shape.rowLen i ≤ D.shape.rowLen c.1 :=
      D.shape.rowLen_anti c.1 i hc_le_i
    have hrowLen_c : D.shape.rowLen c.1 = c.2 :=
      D.new_shape_rowLen_at_removedCell
    have hj_lt : j < D.shape.rowLen i := by
      rwa [YoungDiagram.mem_iff_lt_rowLen] at hmem
    omega
  exact exists_reverseRowInsertionTrace_fromCap_with_respects
    D.tableau (c.1 - 1) c.2 D.value hcap_mem hcap_lt hbelow

/-- True reverse row insertion at a removable outside corner.

It first deletes the outside corner, then performs upward reverse bumping starting in
the row above that corner. -/
noncomputable def reverseRowInsert {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    ReverseRowInsertResult N μ c hc := by
  classical
  by_cases htop : c.1 = 0
  · exact deleteCorner T c hc
  · let D := deleteCorner T c hc
    let startRow := c.1 - 1
    have htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
    let tr := Classical.choose htr
    let out := ReverseRowInsertionTrace.result tr
    exact
      { shape := D.shape
        tableau := out.1
        value := out.2
        cell_mem_old := D.cell_mem_old
        cell_not_mem_shape := D.cell_not_mem_shape
        shape_mem_iff := D.shape_mem_iff
        shape_addable := D.shape_addable
        card_eq := D.card_eq }

theorem reverseRowInsert_shape_eq_deleteCorner {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    (reverseRowInsert T c hc).shape = (deleteCorner T c hc).shape := by
  unfold reverseRowInsert
  by_cases htop : c.1 = 0
  · simp [htop]
  · simp [htop]

theorem reverseRowInsert_shape_eq_of_cell_eq {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hcd : c = d) :
    (reverseRowInsert T c hc).shape = (reverseRowInsert T d hd).shape := by
  cases hcd
  have hproof : hc = hd := Subsingleton.elim _ _
  cases hproof
  rfl

theorem reverseRowInsert_tableau_heq_of_cell_eq {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hcd : c = d) :
    HEq (reverseRowInsert T c hc).tableau (reverseRowInsert T d hd).tableau := by
  cases hcd
  have hproof : hc = hd := Subsingleton.elim _ _
  cases hproof
  exact HEq.rfl

theorem reverseRowInsert_value_eq_of_cell_eq {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hcd : c = d) :
    (reverseRowInsert T c hc).value = (reverseRowInsert T d hd).value := by
  cases hcd
  have hproof : hc = hd := Subsingleton.elim _ _
  cases hproof
  rfl

/-- Reverse row insertion produces another bounded semistandard Young tableau. -/
theorem reverseRowInsert_preserves_semistandard {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    ∃ μ' : YoungDiagram, Nonempty (BoundedSSYT μ' N) := by
  exact ⟨(reverseRowInsert T c hc).shape, ⟨(reverseRowInsert T c hc).tableau⟩⟩

/-- The output shape of reverse row insertion is contained in the input shape. -/
theorem reverseRowInsert_shape_subset {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    (reverseRowInsert T c hc).shape ≤ μ := by
  exact (reverseRowInsert T c hc).shape_subset_old

theorem reverseRowInsert_shape_mem_iff_of_row_lt {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    {i j : ℕ} (hi : i < c.1) :
    (i, j) ∈ (reverseRowInsert T c hc).shape ↔ (i, j) ∈ μ := by
  rw [reverseRowInsert_shape_eq_deleteCorner T c hc]
  exact deleteCorner_shape_mem_iff_of_row_lt T c hc hi

theorem deleteCorner_after_reverseRowInsert_shape_mem_iff_of_row_lt {N : ℕ}
    {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c)
    (hd : IsRemovableCorner (reverseRowInsert T c hc).shape d)
    {i j : ℕ} (hi : i < d.1) :
    (i, j) ∈ (deleteCorner (reverseRowInsert T c hc).tableau d hd).shape ↔
      (i, j) ∈ (reverseRowInsert T c hc).shape := by
  exact deleteCorner_shape_mem_iff_of_row_lt
    (reverseRowInsert T c hc).tableau d hd hi

theorem deleteCorner_after_reverseRowInsert_tableau_entry_of_row_lt {N : ℕ}
    {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c)
    (hd : IsRemovableCorner (reverseRowInsert T c hc).shape d)
    {i j : ℕ} (hi : i < d.1)
    (hcell : (i, j) ∈ (reverseRowInsert T c hc).shape) :
    (deleteCorner (reverseRowInsert T c hc).tableau d hd).tableau.T i j =
      (reverseRowInsert T c hc).tableau.T i j := by
  exact deleteCorner_tableau_entry_of_row_lt
    (reverseRowInsert T c hc).tableau d hd hi hcell

/-- Reverse row insertion removes its chosen cell from the output shape. -/
theorem reverseRowInsert_removedCell_not_mem {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    c ∉ (reverseRowInsert T c hc).shape := by
  exact (reverseRowInsert T c hc).cell_not_mem_shape

theorem reverseRowInsert_tableau_entry_of_removed_row_le {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    {i j : ℕ} (hi : c.1 ≤ i) (hcell : (i, j) ∈ (reverseRowInsert T c hc).shape) :
    (reverseRowInsert T c hc).tableau.T i j = T.T i j := by
  classical
  unfold reverseRowInsert at hcell ⊢
  by_cases htop0 : c.1 = 0
  · rw [dif_pos htop0] at hcell ⊢
    exact deleteCorner_tableau_entry T c hc hcell
  · let D := deleteCorner T c hc
    let startRow := c.1 - 1
    have htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop0
    let tr := Classical.choose htr
    rw [dif_neg htop0] at hcell ⊢
    have hcellD : (i, j) ∈ D.shape := by
      simpa [D] using hcell
    have htrace :
        (ReverseRowInsertionTrace.result tr).1.T i j = D.tableau.T i j :=
      tr.result_tableau_eq_of_row_gt_start (by omega)
    have hdel : D.tableau.T i j = T.T i j :=
      deleteCorner_tableau_entry T c hc hcellD
    simpa [D, startRow, htr, tr] using htrace.trans hdel

/-- Reverse row insertion removes exactly one box. -/
theorem reverseRowInsert_removes_one_box {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    μ.card = (reverseRowInsert T c hc).shape.card + 1 := by
  exact (reverseRowInsert T c hc).card_eq_of_shape_mem_iff

/-- The value ejected by reverse row insertion is at most the entry deleted from the
outside corner.  If the deleted corner is in the top row this is equality; otherwise it
follows from the reverse-bumping trace value decreasing at each upward step. -/
theorem reverseRowInsert_value_le_deletedValue {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    (reverseRowInsert T c hc).value.val ≤ T.T c.1 c.2 := by
  classical
  by_cases htop : c.1 = 0
  · simp [reverseRowInsert, htop, deleteCorner]
  · let D := deleteCorner T c hc
    let startRow := c.1 - 1
    have htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
    let tr := Classical.choose htr
    have hle : (ReverseRowInsertionTrace.result tr).2.val ≤ D.value.val :=
      (ReverseRowInsertionTrace.result_value_le_moving tr)
    simpa [reverseRowInsert, htop, D, startRow, htr, tr, deleteCorner] using hle

theorem reverseRowInsert_value_eq_trace_result_of_not_top {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (htop : c.1 ≠ 0) :
    let D := deleteCorner T c hc
    let startRow := c.1 - 1
    let htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
    (reverseRowInsert T c hc).value =
      (ReverseRowInsertionTrace.result (Classical.choose htr)).2 := by
  classical
  unfold reverseRowInsert
  rw [dif_neg htop]

theorem reverseRowInsert_tableau_heq_trace_result_of_not_top {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (htop : c.1 ≠ 0) :
    let D := deleteCorner T c hc
    let startRow := c.1 - 1
    let htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
    HEq (reverseRowInsert T c hc).tableau
      (ReverseRowInsertionTrace.result (Classical.choose htr)).1 := by
  classical
  unfold reverseRowInsert
  rw [dif_neg htop]

theorem reverseRowInsert_value_eq_of_reverseTrace_of_not_top {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (htop : c.1 ≠ 0)
    (tr : let D := deleteCorner T c hc
      ReverseRowInsertionTrace N D.tableau (c.1 - 1) D.value) :
    (reverseRowInsert T c hc).value = tr.result.2 := by
  classical
  let D := deleteCorner T c hc
  let startRow := c.1 - 1
  let htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
      tr.RespectsLowerCap c.2 := by
    simpa [D, startRow] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
  let chosen : ReverseRowInsertionTrace N D.tableau startRow D.value :=
    Classical.choose htr
  have hchosen :
      (reverseRowInsert T c hc).value = chosen.result.2 := by
    simpa [D, startRow, htr, chosen] using
      reverseRowInsert_value_eq_trace_result_of_not_top T c hc htop
  have huniq : chosen.result.2 = tr.result.2 := by
    simpa [D, startRow] using
      ReverseRowInsertionTrace.result_value_eq_of_same chosen tr
  exact hchosen.trans huniq

theorem reverseRowInsert_tableau_heq_of_reverseTrace_of_not_top {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (htop : c.1 ≠ 0)
    (tr : let D := deleteCorner T c hc
      ReverseRowInsertionTrace N D.tableau (c.1 - 1) D.value) :
    HEq (reverseRowInsert T c hc).tableau tr.result.1 := by
  classical
  let D := deleteCorner T c hc
  let startRow := c.1 - 1
  let htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
      tr.RespectsLowerCap c.2 := by
    simpa [D, startRow] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
  let chosen : ReverseRowInsertionTrace N D.tableau startRow D.value :=
    Classical.choose htr
  have hchosen :
      HEq (reverseRowInsert T c hc).tableau chosen.result.1 := by
    simpa [D, startRow, htr, chosen] using
      reverseRowInsert_tableau_heq_trace_result_of_not_top T c hc htop
  have huniq : HEq chosen.result.1 tr.result.1 := by
    simpa [D, startRow] using
      ReverseRowInsertionTrace.result_tableau_heq_of_same chosen tr
  exact hchosen.trans huniq

theorem reverseRowInsert_tableau_entry_eq_trace_result_of_not_top {N : ℕ}
    {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (htop : c.1 ≠ 0) (i j : ℕ) :
    let D := deleteCorner T c hc
    let startRow := c.1 - 1
    let htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
    let tr := Classical.choose htr
    (reverseRowInsert T c hc).tableau.T i j = tr.result.1.T i j := by
  classical
  intro D startRow htr tr
  unfold reverseRowInsert
  rw [dif_neg htop]

theorem reverseRowInsert_chosen_trace_respectsLowerCap_of_not_top {N : ℕ}
    {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (htop : c.1 ≠ 0) :
    let D := deleteCorner T c hc
    let startRow := c.1 - 1
    let htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
    (Classical.choose htr).RespectsLowerCap c.2 := by
  classical
  intro D startRow htr
  exact Classical.choose_spec htr

theorem reverseRowInsert_chosen_trace_topCol_ge_removed_col_of_not_top {N : ℕ}
    {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (htop : c.1 ≠ 0) :
    let D := deleteCorner T c hc
    let startRow := c.1 - 1
    let htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
        exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
    c.2 ≤ (Classical.choose htr).topCol := by
  classical
  intro D startRow htr
  exact ReverseRowInsertionTrace.topCol_ge_cap_of_respectsLowerCap
    (Classical.choose_spec htr)

theorem reverseRowInsert_tableau_entry_eq_deleteCorner_of_col_lt_chosen_bumpColAt
    {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (htop : c.1 ≠ 0) :
    let D := deleteCorner T c hc
    let startRow := c.1 - 1
    let htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
        exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
    let tr := Classical.choose htr
    ∀ {i j : ℕ}, i ≤ startRow → j < tr.bumpColAt i →
      (reverseRowInsert T c hc).tableau.T i j = D.tableau.T i j := by
  classical
  intro D startRow htr tr i j hi hj
  unfold reverseRowInsert
  rw [dif_neg htop]
  simpa [D, startRow, htr, tr] using
    tr.result_tableau_entry_eq_of_col_lt_bumpColAt hi hj

/-- A bridge for comparing two reverse row insertions.

Once the deleted value at `d` is known to be bounded by the value ejected from `c`,
the ejected value from `d` is bounded by the same value. -/
theorem reverseRowInsert_value_le_of_deletedValue_le_value {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hdel : T.T d.1 d.2 ≤ (reverseRowInsert T c hc).value.val) :
    (reverseRowInsert T d hd).value ≤ (reverseRowInsert T c hc).value := by
  rw [Fin.le_def]
  exact le_trans (reverseRowInsert_value_le_deletedValue T d hd) hdel

/-- Top-row special case of the double reverse-insertion comparison.

If both removable corners are in the same top row and `d` is weakly left of `c`, then
the reverse insertion from `d` ejects a value weakly below the one ejected from `c`.
This is the easy boundary case where reverse insertion at `c` just deletes the top-row
entry. -/
theorem reverseRowInsert_value_le_of_same_top_row_left {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hcrow : c.1 = 0) (hdrow : d.1 = c.1) (hleft : d.2 ≤ c.2) :
    (reverseRowInsert T d hd).value ≤ (reverseRowInsert T c hc).value := by
  apply reverseRowInsert_value_le_of_deletedValue_le_value T hc hd
  have hdeleted_le : T.T d.1 d.2 ≤ T.T c.1 c.2 := by
    rcases lt_or_eq_of_le hleft with hlt | heq
    · rw [hdrow]
      exact T.T.row_weak hlt hc.1
    · have hdc : d = c := by
        ext <;> omega
      simp [hdc]
  simpa [reverseRowInsert, hcrow, deleteCorner] using hdeleted_le

theorem reverseRowInsert_value_le_after_left_corner_of_current_top {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c)
    (hd : IsRemovableCorner (reverseRowInsert T c hc).shape d)
    (hcrow : c.1 = 0) (hdrow : d.1 = c.1) (hleft : d.2 ≤ c.2) :
    (reverseRowInsert (reverseRowInsert T c hc).tableau d hd).value ≤
      (reverseRowInsert T c hc).value := by
  rw [Fin.le_def]
  have hdel :
      (reverseRowInsert (reverseRowInsert T c hc).tableau d hd).value.val ≤
        (reverseRowInsert T c hc).tableau.T d.1 d.2 :=
    reverseRowInsert_value_le_deletedValue (reverseRowInsert T c hc).tableau d hd
  have hentry :
      (reverseRowInsert T c hc).tableau.T d.1 d.2 ≤
        (reverseRowInsert T c hc).value.val := by
    have hshape : (reverseRowInsert T c hc).shape = (deleteCorner T c hc).shape :=
      reverseRowInsert_shape_eq_deleteCorner T c hc
    have hD : d ∈ (deleteCorner T c hc).shape := by
      simpa [hshape] using hd.1
    have hentry_eq :
        (reverseRowInsert T c hc).tableau.T d.1 d.2 = T.T d.1 d.2 := by
      unfold reverseRowInsert
      rw [dif_pos hcrow]
      exact deleteCorner_tableau_entry T c hc hD
    rw [hentry_eq]
    have hvalue_eq : (reverseRowInsert T c hc).value.val = T.T c.1 c.2 := by
      simp [reverseRowInsert, hcrow, deleteCorner]
    rcases lt_or_eq_of_le hleft with hlt | heq
    · rw [hdrow]
      rw [hvalue_eq]
      exact T.T.row_weak hlt hc.1
    · have hdc : d = c := by
        ext <;> omega
      have hnot : c ∉ (reverseRowInsert T c hc).shape :=
        reverseRowInsert_removedCell_not_mem T c hc
      exact False.elim (hnot (by simpa [hdc] using hd.1))
  exact le_trans hdel hentry

theorem reverseRowInsert_value_le_after_left_corner_of_current_top' {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c)
    (hd : IsRemovableCorner (reverseRowInsert T c hc).shape d)
    (hcrow : c.1 = 0) (hleft : d.2 ≤ c.2) :
    (reverseRowInsert (reverseRowInsert T c hc).tableau d hd).value ≤
      (reverseRowInsert T c hc).value := by
  classical
  by_cases hdtop : d.1 = 0
  · exact reverseRowInsert_value_le_after_left_corner_of_current_top
      T hc hd hcrow (by omega) hleft
  · let R := reverseRowInsert T c hc
    let D := deleteCorner R.tableau d hd
    let startRow := d.1 - 1
    have htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
    tr.RespectsLowerCap d.2 := by
      simpa [D, startRow] using
        exists_reverseRowInsertionTrace_afterDelete_with_respects R.tableau d hd hdtop
    let tr : ReverseRowInsertionTrace N D.tableau startRow D.value :=
      Classical.choose htr
    have htr_respects : tr.RespectsLowerCap d.2 := by
      simpa [tr] using Classical.choose_spec htr
    have hval :
        (reverseRowInsert R.tableau d hd).value =
          (ReverseRowInsertionTrace.result tr).2 := by
      simpa [R, D, startRow, htr, tr] using
        reverseRowInsert_value_eq_trace_result_of_not_top R.tableau d hd hdtop
    rw [hval, Fin.le_def]
    have htop_bound :
        ∀ {j : ℕ}, (0, j) ∈ D.shape →
          D.tableau.T 0 j ≤ R.value.val := by
      intro j hj
      have hD_top : D.tableau.T 0 j = R.tableau.T 0 j := by
        exact deleteCorner_tableau_entry_of_row_lt R.tableau d hd (by omega) (D.shape_subset_old hj)
      rw [hD_top]
      have hRshape : R.shape = (deleteCorner T c hc).shape := by
        simpa [R] using reverseRowInsert_shape_eq_deleteCorner T c hc
      have hjR : (0, j) ∈ R.shape := D.shape_subset_old hj
      have hjDold : (0, j) ∈ (deleteCorner T c hc).shape := by
        simpa [hRshape] using hjR
      have hj_lt : j < c.2 := by
        have hrowLen : (deleteCorner T c hc).shape.rowLen c.1 = c.2 :=
          (deleteCorner T c hc).new_shape_rowLen_at_removedCell
        rw [YoungDiagram.mem_iff_lt_rowLen] at hjDold
        rw [← hcrow] at hjDold
        simpa [hrowLen] using hjDold
      have hRentry : R.tableau.T 0 j = T.T 0 j := by
        have hcellR : (0, j) ∈ R.shape := hjR
        simpa [R, hcrow] using
          (show (reverseRowInsert T c hc).tableau.T 0 j = T.T 0 j from by
            unfold reverseRowInsert
            rw [dif_pos hcrow]
            exact deleteCorner_tableau_entry T c hc hjDold)
      rw [hRentry]
      have hvalR : R.value.val = T.T c.1 c.2 := by
        simp [R, reverseRowInsert, hcrow, deleteCorner]
      rw [hvalR, hcrow]
      have hc_cell : (0, c.2) ∈ μ := by
        simpa [show (0, c.2) = c by ext <;> omega] using hc.1
      exact T.T.row_weak hj_lt hc_cell
    exact tr.result_value_le_of_top_row_entries_le htop_bound

/-- Core non-top/non-top path geometry for two reverse row-insertion paths.

The proof separates the top-row second-corner case, handled by the lower-cap
invariant, from the non-top path comparison formalized here. -/
theorem reverseRowInsert_second_topCol_le_first_topCol_nonTop_core {N : ℕ}
    {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c)
    (hc_not_top : c.1 ≠ 0)
    (hd : IsRemovableCorner (reverseRowInsert T c hc).shape d)
    (hd_not_top : d.1 ≠ 0)
    (hleft : d.2 < c.2) :
    let D₁ := deleteCorner T c hc
    let start₁ := c.1 - 1
    let htr₁ : ∃ tr : ReverseRowInsertionTrace N D₁.tableau start₁ D₁.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D₁, start₁] using
        exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc hc_not_top
    let tr₁ := Classical.choose htr₁
    let R₁ := reverseRowInsert T c hc
    let D₂ := deleteCorner R₁.tableau d hd
    let start₂ := d.1 - 1
    let htr₂ : ∃ tr : ReverseRowInsertionTrace N D₂.tableau start₂ D₂.value,
        tr.RespectsLowerCap d.2 := by
      simpa [D₂, start₂] using
        exists_reverseRowInsertionTrace_afterDelete_with_respects R₁.tableau d hd hd_not_top
    let tr₂ := Classical.choose htr₂
    tr₂.topCol < tr₁.topCol := by
  classical
  intro D₁ start₁ htr₁ tr₁ R₁ D₂ start₂ htr₂ tr₂
  have hshape_R₁_D₁ : R₁.shape = D₁.shape := by
    simpa [R₁, D₁] using reverseRowInsert_shape_eq_deleteCorner T c hc
  have hd_D₁ : IsRemovableCorner D₁.shape d := by
    change IsRemovableCorner R₁.shape d at hd
    simpa [hshape_R₁_D₁] using hd
  have hc_add_D₁ : IsAddableCorner D₁.shape c := by
    simpa [D₁] using (deleteCorner T c hc).shape_addable
  have hrow_cd : c.1 ≤ d.1 :=
    IsAddableCorner.row_le_of_removable_col_lt hc_add_D₁ hd_D₁ hleft
  have hstart : start₁ ≤ start₂ := by
    have hcpos : 0 < c.1 := Nat.pos_of_ne_zero hc_not_top
    have hdpos : 0 < d.1 := Nat.pos_of_ne_zero hd_not_top
    simp [start₁, start₂]
    omega
  have hcap₁ : tr₁.RespectsLowerCap c.2 := by
    simpa [tr₁] using Classical.choose_spec htr₁
  have hcap₂ : tr₂.RespectsLowerCap d.2 := by
    simpa [tr₂] using Classical.choose_spec htr₂
  have hmove : tr₂.movingAt start₁ ≤ D₁.value := by
    rw [Fin.le_def]
    by_cases hdcrow : d.1 = c.1
    · have hstart_eq : start₂ = start₁ := by
        simp [start₁, start₂, hdcrow]
      have hmov_start : tr₂.movingAt start₁ = D₂.value := by
        simpa [hstart_eq, tr₂] using tr₂.movingAt_self
      rw [hmov_start]
      have hD₂val : D₂.value.val = R₁.tableau.T d.1 d.2 := by
        simp [D₂, deleteCorner]
      rw [hD₂val]
      have hR₁entry : R₁.tableau.T d.1 d.2 = T.T d.1 d.2 := by
        change (reverseRowInsert T c hc).tableau.T d.1 d.2 = T.T d.1 d.2
        exact reverseRowInsert_tableau_entry_of_removed_row_le T c hc
          (by omega) (by simpa [R₁] using hd.1)
      rw [hR₁entry]
      have hD₁val : D₁.value.val = T.T c.1 c.2 := by
        simp [D₁, deleteCorner]
      rw [hD₁val]
      have hdrow : d.1 = c.1 := hdcrow
      rw [hdrow]
      exact T.T.row_weak hleft hc.1
    · have hdrow_gt : c.1 < d.1 := lt_of_le_of_ne hrow_cd (Ne.symm hdcrow)
      have htarget_succ : start₁ + 1 = c.1 := by
        have hcpos : 0 < c.1 := Nat.pos_of_ne_zero hc_not_top
        simp [start₁]
        omega
      have hc_le_start₂ : c.1 ≤ start₂ := by
        simp [start₂]
        omega
      have hpred :
          (tr₂.movingAt start₁).val =
            (tr₂.tableauAt c.1).T c.1 (tr₂.bumpColAt c.1) := by
        have h :=
          tr₂.movingAt_pred_val_eq_tableauAt_succ_bumpColAt
            (target := start₁) (by simpa [htarget_succ] using hc_le_start₂)
        simpa [htarget_succ] using h
      rw [hpred]
      have hbump_mem : (c.1, tr₂.bumpColAt c.1) ∈ D₂.shape :=
        tr₂.bumpColAt_mem hc_le_start₂
      have hbump_R₁ : (c.1, tr₂.bumpColAt c.1) ∈ R₁.shape :=
        D₂.shape_subset_old hbump_mem
      have hbump_D₁ : (c.1, tr₂.bumpColAt c.1) ∈ D₁.shape := by
        simpa [hshape_R₁_D₁] using hbump_R₁
      have hbump_lt : tr₂.bumpColAt c.1 < c.2 := by
        have hrowLen : D₁.shape.rowLen c.1 = c.2 := by
          simpa [D₁] using (deleteCorner T c hc).new_shape_rowLen_at_removedCell
        rwa [YoungDiagram.mem_iff_lt_rowLen, hrowLen] at hbump_D₁
      have htab_D₂ :
          D₂.tableau.T c.1 (tr₂.bumpColAt c.1) =
            R₁.tableau.T c.1 (tr₂.bumpColAt c.1) := by
        exact deleteCorner_tableau_entry_of_row_lt R₁.tableau d hd
          (by omega) hbump_R₁
      have htab_at :
          (tr₂.tableauAt c.1).T c.1 (tr₂.bumpColAt c.1) =
            D₂.tableau.T c.1 (tr₂.bumpColAt c.1) := by
        exact tr₂.tableauAt_entry_eq_of_row_le_target hc_le_start₂ le_rfl
      rw [htab_at, htab_D₂]
      have hR₁entry :
          R₁.tableau.T c.1 (tr₂.bumpColAt c.1) =
            T.T c.1 (tr₂.bumpColAt c.1) := by
        change (reverseRowInsert T c hc).tableau.T c.1 (tr₂.bumpColAt c.1) =
          T.T c.1 (tr₂.bumpColAt c.1)
        exact reverseRowInsert_tableau_entry_of_removed_row_le T c hc
          le_rfl (by simpa [R₁] using hbump_R₁)
      rw [hR₁entry]
      have hD₁val : D₁.value.val = T.T c.1 c.2 := by
        simp [D₁, deleteCorner]
      rw [hD₁val]
      exact T.T.row_weak hbump_lt hc.1
  have hR₁_eq_D₁_left :
      ∀ {i j : ℕ}, i ≤ start₁ → j < tr₁.bumpColAt i →
        R₁.tableau.T i j = D₁.tableau.T i j := by
    intro i j hi hj
    change (reverseRowInsert T c hc).tableau.T i j = D₁.tableau.T i j
    simpa [D₁, start₁, htr₁, tr₁, R₁] using
      reverseRowInsert_tableau_entry_eq_deleteCorner_of_col_lt_chosen_bumpColAt
        T c hc hc_not_top (i := i) (j := j) hi hj
  have hD₂_eq_R₁_up_to_start₁ :
      ∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ R₁.shape →
        D₂.tableau.T i j = R₁.tableau.T i j := by
    intro i j hi hcell
    have hi_d : i < d.1 := by
      have hcpos : 0 < c.1 := Nat.pos_of_ne_zero hc_not_top
      omega
    simpa [D₂] using
      deleteCorner_tableau_entry_of_row_lt R₁.tableau d hd hi_d hcell
  have hD₂_shape_to_D₁_up_to_start₁ :
      ∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₂.shape → (i, j) ∈ D₁.shape := by
    intro i j hi hcell
    have hR₁cell : (i, j) ∈ R₁.shape := D₂.shape_subset_old hcell
    simpa [hshape_R₁_D₁] using hR₁cell
  have hD₁_shape_to_D₂_up_to_start₁ :
      ∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₁.shape → (i, j) ∈ D₂.shape := by
    intro i j hi hcell
    have hR₁cell : (i, j) ∈ R₁.shape := by
      simpa [hshape_R₁_D₁] using hcell
    have hi_d : i < d.1 := by
      have hcpos : 0 < c.1 := Nat.pos_of_ne_zero hc_not_top
      omega
    simpa [D₂] using
      (deleteCorner_shape_mem_iff_of_row_lt R₁.tableau d hd hi_d).2 hR₁cell
  exact
    ReverseRowInsertionTrace.topCol_lt_of_movingAt_le_of_rows_equiv_result
      tr₂ tr₁ hstart hmove
      (by
        intro i j hi hcell
        exact hD₂_shape_to_D₁_up_to_start₁ hi hcell)
      (by
        intro i j hi hcell
        exact hD₁_shape_to_D₂_up_to_start₁ hi hcell)
      (by
        intro i j hi hcellD₂ hcellD₁
        calc
          (tr₂.tableauAt start₁).T i j = D₂.tableau.T i j := by
            exact tr₂.tableauAt_entry_eq_of_row_le_target hstart hi
          _ = R₁.tableau.T i j := by
            exact hD₂_eq_R₁_up_to_start₁ hi (D₂.shape_subset_old hcellD₂)
          _ = tr₁.result.1.T i j := by
            change (reverseRowInsert T c hc).tableau.T i j = tr₁.result.1.T i j
            unfold reverseRowInsert
            rw [dif_neg hc_not_top])

/-- The missing path geometry for the non-top double reverse insertion comparison.

After reverse-inserting at a non-top corner `c`, a second reverse insertion from a
corner `d` weakly to the left should eject from a top-row column weakly to the left
of the first path's top-row ejection column.  This is the precise column comparison
needed to finish the non-top branch of `reverseKrsList_sorted`. -/
theorem reverseRowInsert_second_topCol_le_first_topCol_of_left_corner {N : ℕ}
    {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c)
    (hc_not_top : c.1 ≠ 0)
    (hd : IsRemovableCorner (reverseRowInsert T c hc).shape d)
    (hleft : d.2 < c.2) :
    let D₁ := deleteCorner T c hc
    let start₁ := c.1 - 1
    let htr₁ : ∃ tr : ReverseRowInsertionTrace N D₁.tableau start₁ D₁.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D₁, start₁] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc hc_not_top
    let tr₁ := Classical.choose htr₁
    if hd_top : d.1 = 0 then
      d.2 ≤ tr₁.topCol
    else
      let R₁ := reverseRowInsert T c hc
      let D₂ := deleteCorner R₁.tableau d hd
      let start₂ := d.1 - 1
      let htr₂ : ∃ tr : ReverseRowInsertionTrace N D₂.tableau start₂ D₂.value,
          tr.RespectsLowerCap d.2 := by
        simpa [D₂, start₂] using
          exists_reverseRowInsertionTrace_afterDelete_with_respects R₁.tableau d hd hd_top
      let tr₂ := Classical.choose htr₂
      tr₂.topCol ≤ tr₁.topCol := by
  classical
  intro D₁ start₁ htr₁ tr₁
  by_cases hd_top : d.1 = 0
  · have hc_le_top : c.2 ≤ tr₁.topCol := by
      exact ReverseRowInsertionTrace.topCol_ge_cap_of_respectsLowerCap
        (Classical.choose_spec htr₁)
    simpa [hd_top] using le_of_lt (lt_of_lt_of_le hleft hc_le_top)
  · simp only [hd_top, ↓reduceDIte]
    exact le_of_lt (by
      simpa using
        reverseRowInsert_second_topCol_le_first_topCol_nonTop_core
          T hc hc_not_top hd hd_top hleft)

/-- Strong value form of the non-top double reverse-insertion comparison.

If the first reverse insertion starts at a non-top corner `c`, the second starts at a
non-top corner `d` of the resulting shape, and the second top-row ejection column is
strictly left of the first one, then the second ejected value is weakly bounded by the
first ejected value.  The strictness is exactly what avoids the top-row cell replaced by
the first reverse insertion. -/
theorem reverseRowInsert_value_le_after_left_corner_of_current_nonTop_of_topCol_lt
    {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c)
    (hc_not_top : c.1 ≠ 0)
    (hd : IsRemovableCorner (reverseRowInsert T c hc).shape d)
    (hd_not_top : d.1 ≠ 0)
    (htop_lt :
      let D₁ := deleteCorner T c hc
      let start₁ := c.1 - 1
      let htr₁ : ∃ tr : ReverseRowInsertionTrace N D₁.tableau start₁ D₁.value,
          tr.RespectsLowerCap c.2 := by
        simpa [D₁, start₁] using
          exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc hc_not_top
      let tr₁ := Classical.choose htr₁
      let R₁ := reverseRowInsert T c hc
      let D₂ := deleteCorner R₁.tableau d hd
      let start₂ := d.1 - 1
      let htr₂ : ∃ tr : ReverseRowInsertionTrace N D₂.tableau start₂ D₂.value,
          tr.RespectsLowerCap d.2 := by
        simpa [D₂, start₂] using
          exists_reverseRowInsertionTrace_afterDelete_with_respects R₁.tableau d hd hd_not_top
      let tr₂ := Classical.choose htr₂
      tr₂.topCol < tr₁.topCol) :
    (reverseRowInsert (reverseRowInsert T c hc).tableau d hd).value ≤
      (reverseRowInsert T c hc).value := by
  classical
  let D₁ := deleteCorner T c hc
  let start₁ := c.1 - 1
  let htr₁ : ∃ tr : ReverseRowInsertionTrace N D₁.tableau start₁ D₁.value,
      tr.RespectsLowerCap c.2 := by
    simpa [D₁, start₁] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc hc_not_top
  let tr₁ : ReverseRowInsertionTrace N D₁.tableau start₁ D₁.value :=
    Classical.choose htr₁
  let R₁ := reverseRowInsert T c hc
  let D₂ := deleteCorner R₁.tableau d hd
  let start₂ := d.1 - 1
  let htr₂ : ∃ tr : ReverseRowInsertionTrace N D₂.tableau start₂ D₂.value,
      tr.RespectsLowerCap d.2 := by
    simpa [D₂, start₂] using
      exists_reverseRowInsertionTrace_afterDelete_with_respects R₁.tableau d hd hd_not_top
  let tr₂ : ReverseRowInsertionTrace N D₂.tableau start₂ D₂.value :=
    Classical.choose htr₂
  have hlt : tr₂.topCol < tr₁.topCol := by
    simpa [D₁, start₁, htr₁, tr₁, R₁, D₂, start₂, htr₂, tr₂] using htop_lt
  have hval₁ : R₁.value = tr₁.result.2 := by
    simpa [D₁, start₁, htr₁, tr₁, R₁] using
      reverseRowInsert_value_eq_trace_result_of_not_top T c hc hc_not_top
  have hval₂ : (reverseRowInsert R₁.tableau d hd).value = tr₂.result.2 := by
    simpa [R₁, D₂, start₂, htr₂, tr₂] using
      reverseRowInsert_value_eq_trace_result_of_not_top R₁.tableau d hd hd_not_top
  rw [hval₂, hval₁, Fin.le_def]
  have htop₂ :
      D₂.tableau.T 0 tr₂.topCol = R₁.tableau.T 0 tr₂.topCol := by
    exact deleteCorner_tableau_entry_of_row_lt R₁.tableau d hd
      (by omega) (D₂.shape_subset_old tr₂.topCol_mem)
  have hR₁_tableau :
      R₁.tableau.T 0 tr₂.topCol = D₁.tableau.T 0 tr₂.topCol := by
    have hentry :
        tr₁.result.1.T 0 tr₂.topCol = D₁.tableau.T 0 tr₂.topCol :=
      tr₁.result_tableau_top_entry_eq_of_col_lt_topCol hlt
    change (reverseRowInsert T c hc).tableau.T 0 tr₂.topCol =
      D₁.tableau.T 0 tr₂.topCol
    unfold reverseRowInsert
    rw [dif_neg hc_not_top]
    simpa [D₁, start₁, htr₁, tr₁] using hentry
  calc
    tr₂.result.2.val = D₂.tableau.T 0 tr₂.topCol := by
      exact tr₂.result_value_eq_initial_top_entry
    _ = R₁.tableau.T 0 tr₂.topCol := htop₂
    _ = D₁.tableau.T 0 tr₂.topCol := hR₁_tableau
    _ ≤ tr₁.result.2.val :=
      tr₁.top_row_entry_le_result_value_of_col_le_topCol (le_of_lt hlt)

/-- On the southeast boundary of a Young diagram, a removable corner weakly to the left
of another removable corner is weakly lower. -/
theorem IsRemovableCorner.row_le_of_col_le {μ : YoungDiagram} {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hcol : d.2 ≤ c.2) :
    c.1 ≤ d.1 := by
  by_contra hnot
  have hd_lt_c : d.1 < c.1 := Nat.lt_of_not_ge hnot
  have hcell : (c.1, d.2) ∈ μ := by
    exact μ.up_left_mem le_rfl hcol hc.1
  rcases hd with ⟨hdmem, ν, hdnot, hν⟩
  have hcell_in_ν_or :
      (c.1, d.2) ∈ ν ∨ (c.1, d.2) = d := (hν (c.1, d.2)).1 hcell
  rcases hcell_in_ν_or with hcellν | hcell_eq
  · have hd_in_ν : d ∈ ν := by
      exact ν.up_left_mem (Nat.le_of_lt hd_lt_c) le_rfl hcellν
    exact hdnot hd_in_ν
  · have hcell_eq' : (c.1, d.2) = (d.1, d.2) := by
      simpa using hcell_eq
    have hrow : c.1 = d.1 := by
      injection hcell_eq' with hfst hsnd
    omega

/-- Distinct removable corners ordered by column have the expected strict row order. -/
theorem IsRemovableCorner.row_lt_of_col_lt {μ : YoungDiagram} {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hd : IsRemovableCorner μ d)
    (hcol : d.2 < c.2) :
    c.1 < d.1 := by
  have hle : c.1 ≤ d.1 := IsRemovableCorner.row_le_of_col_le hc hd (le_of_lt hcol)
  exact lt_of_le_of_ne hle (by
    intro hrow
    have hcell : (d.1, c.2) ∈ μ := by
      simpa [← hrow] using hc.1
    rcases hd with ⟨hdmem, ν, hdnot, hν⟩
    have hcell_in_ν_or : (d.1, c.2) ∈ ν ∨ (d.1, c.2) = d :=
      (hν (d.1, c.2)).1 hcell
    rcases hcell_in_ν_or with hcellν | hcell_eq
    · have hd_in_ν : d ∈ ν := by
        exact ν.up_left_mem le_rfl (Nat.le_of_lt hcol) hcellν
      exact hdnot hd_in_ν
    · have hcell_eq' : (d.1, c.2) = (d.1, d.2) := by
        simpa using hcell_eq
      have hcol_eq : c.2 = d.2 := by
        injection hcell_eq' with hfst hsnd
      omega)

theorem IsRemovableCorner.ge_eq {μ : YoungDiagram} {c d : ℕ × ℕ}
    (hc : IsRemovableCorner μ c) (hdmem : d ∈ μ) (hcd : c ≤ d) :
    d = c := by
  rcases hc with ⟨hcmem, ν, hcnot, hν⟩
  rcases (hν d).1 hdmem with hdν | hdc
  · have hcν : c ∈ ν := ν.up_left_mem hcd.1 hcd.2 hdν
    exact False.elim (hcnot hcν)
  · exact hdc

/-- Row insertion produces another bounded semistandard Young tableau. -/
theorem rowInsert_preserves_semistandard {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    ∃ μ' : YoungDiagram, Nonempty (BoundedSSYT μ' N) := by
  exact ⟨(rowInsert T x).shape, ⟨(rowInsert T x).tableau⟩⟩

/-- Row insertion adds exactly one box. -/
theorem rowInsert_adds_one_box {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    (rowInsert T x).shape.card = μ.card + 1 := by
  exact (rowInsert T x).card_eq_of_shape_mem_iff

/-- Trace-level row-bumping comparison with an explicit second starting tableau.

The second tableau `S` may differ from the first insertion result above `row`; row insertion
from `row` never looks there. This is the transport form needed in the bump/bump case. -/
theorem rowInsertionTrace_newCell_right_of_le_aux {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row cap : ℕ} {x y : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (trx : RowInsertionTrace N T row x)
    {S : BoundedSSYT trx.result.shape N}
    (hxy : x ≤ y)
    (hS : ∀ {i j : ℕ}, row ≤ i → S.T i j = trx.result.tableau.T i j)
    (trY : RowInsertionTrace N S row y) :
    trx.result.newCell.2 < trY.result.newCell.2 := by
  cases trx with
  | done A =>
      cases trY with
      | done Ay =>
          let Ay' : RowAppendLocation A.result.tableau row y :=
            { col := Ay.location.col
              col_eq_rowLen := Ay.location.col_eq_rowLen
              row_entries_le := by
                intro j hj
                have hSeq : S.T row j = A.result.tableau.T row j := by
                  simpa [RowInsertionTrace.result] using hS (i := row) (j := j) le_rfl
                calc
                  A.result.tableau.T row j = S.T row j := hSeq.symm
                  _ ≤ y.val := Ay.location.row_entries_le hj }
          change A.result.newCell.2 < Ay.result.newCell.2
          have hlt := RowAppendStepResult.rowAppendStep_newCell_col_lt_next_append_of_le A Ay'
          simpa [Ay', Ay.result_newCell_col, Ay.location.col_eq_rowLen] using hlt
      | bump By tailY =>
          let Ly' : RowBumpLocation A.result.tableau row y :=
            { col := By.col
              cell_mem := By.cell_mem
              entry_gt := by
                have hSeq : S.T row By.col = A.result.tableau.T row By.col := by
                  simpa [RowInsertionTrace.result] using
                    hS (i := row) (j := By.col) le_rfl
                rw [← hSeq]
                exact By.entry_gt
              left_le := by
                intro j hj hcell
                have hSeq : S.T row j = A.result.tableau.T row j := by
                  simpa [RowInsertionTrace.result] using hS (i := row) (j := j) le_rfl
                calc
                  A.result.tableau.T row j = S.T row j := hSeq.symm
                  _ ≤ y.val := By.left_le hj hcell }
          exact False.elim
            (RowAppendStepResult.not_rowBumpLocation_after_appendStep_of_le hxy A ⟨Ly'⟩)
  | bump B tail =>
      have hinv' := RowInsertionPathInvariant.next_after_bump_step hinv B
      cases trY with
      | done Ay =>
          have hrowLen : tail.result.shape.rowLen row = μ.rowLen row :=
            tail.result_rowLen_eq_of_row_lt (by omega)
          let AyB : RowAppendLocation B.tableau row y :=
            { col := Ay.location.col
              col_eq_rowLen := by
                calc
                  Ay.location.col = tail.result.shape.rowLen row := Ay.location.col_eq_rowLen
                  _ = μ.rowLen row := hrowLen
              row_entries_le := by
                intro j hj
                have hcell : (row, j) ∈ μ := by
                  rw [YoungDiagram.mem_iff_lt_rowLen]
                  exact hj
                have hjS : j < tail.result.shape.rowLen row := by
                  rwa [hrowLen]
                calc
                  B.tableau.T row j = tail.result.tableau.T row j :=
                    (tail.result_tableau_eq_of_row_lt (by omega) hcell).symm
                  _ = S.T row j := (by
                    simpa [RowInsertionTrace.result] using
                      (hS (i := row) (j := j) le_rfl).symm)
                  _ ≤ y.val := Ay.location.row_entries_le hjS }
          have htail_le : tail.result.newCell.2 ≤ B.col :=
            RowInsertionPathInvariant.trace_newCell_col_le_cap hinv' tail
          have hBlt : B.col < AyB.col :=
            rowBumpStep_col_lt_next_append B AyB
          change tail.result.newCell.2 < Ay.result.newCell.2
          have hAy : Ay.result.newCell.2 = Ay.location.col := by
            rw [Ay.result_newCell_col, Ay.location.col_eq_rowLen]
          rw [hAy]
          exact lt_of_le_of_lt htail_le hBlt
      | bump By tailY =>
          have hrowLen : tail.result.shape.rowLen row = μ.rowLen row :=
            tail.result_rowLen_eq_of_row_lt (by omega)
          have hBy_col_lt : By.col < μ.rowLen row := by
            have hlt := By.location.col_lt_rowLen
            simpa [RowInsertionTrace.result, hrowLen] using hlt
          have hBy_cell : (row, By.col) ∈ μ := by
            rw [YoungDiagram.mem_iff_lt_rowLen]
            exact hBy_col_lt
          let LyB : RowBumpLocation B.tableau row y :=
            { col := By.col
              cell_mem := hBy_cell
              entry_gt := by
                have htail :
                    tail.result.tableau.T row By.col = B.tableau.T row By.col :=
                  tail.result_tableau_eq_of_row_lt (by omega) hBy_cell
                have hSeq : S.T row By.col = tail.result.tableau.T row By.col := by
                  simpa [RowInsertionTrace.result] using
                    hS (i := row) (j := By.col) le_rfl
                calc
                  y.val < S.T row By.col := By.entry_gt
                  _ = tail.result.tableau.T row By.col := hSeq
                  _ = B.tableau.T row By.col := htail
              left_le := by
                intro j hj hcell
                have hcell_tail : (row, j) ∈ tail.result.shape :=
                  tail.result.old_subset (row, j) hcell
                calc
                  B.tableau.T row j = tail.result.tableau.T row j :=
                    (tail.result_tableau_eq_of_row_lt (by omega) hcell).symm
                  _ = S.T row j := (by
                    simpa [RowInsertionTrace.result] using
                      (hS (i := row) (j := j) le_rfl).symm)
                  _ ≤ y.val := By.left_le hj hcell_tail }
          have hBlt : B.col < By.col :=
            rowBumpStep_col_lt_next_bump_of_le hxy B LyB
          have hbumped_le : B.bumped ≤ By.bumped := by
            change B.bumped.val ≤ By.bumped.val
            calc
              B.bumped.val = T.T row B.col := B.bumped_eq.symm
              _ ≤ T.T row By.col := T.T.row_weak hBlt hBy_cell
              _ = B.tableau.T row By.col := by
                rw [RowBumpStepResult.unchanged_of_ne B (by
                  intro hp
                  have hcol : By.col = B.col := congrArg Prod.snd hp
                  omega)]
              _ = tail.result.tableau.T row By.col :=
                (tail.result_tableau_eq_of_row_lt (by omega) hBy_cell).symm
              _ = S.T row By.col := (by
                simpa [RowInsertionTrace.result] using
                  (hS (i := row) (j := By.col) le_rfl).symm)
              _ = By.bumped.val := By.bumped_eq
          have hS' :
              ∀ {i j : ℕ}, row + 1 ≤ i →
                By.tableau.T i j = tail.result.tableau.T i j := by
            intro i j hi
            calc
              By.tableau.T i j = S.T i j :=
                RowBumpStepResult.unchanged_of_row_ne By (by omega)
              _ = tail.result.tableau.T i j := by
                simpa [RowInsertionTrace.result] using hS (i := i) (j := j) (by omega)
          exact rowInsertionTrace_newCell_right_of_le_aux hinv' tail hbumped_le hS' tailY
termination_by sizeOf trx

/-- Trace-level row-bumping comparison.

This is the real row-bumping lemma for the chosen traces: if the second inserted
letter is weakly larger, its final new cell lies strictly to the right of the first
new cell. The proof should compare the two bumping paths row by row. -/
theorem rowInsertionTrace_newCell_right_of_le {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {x y : Fin N} (hxy : x ≤ y) :
    (rowInsertionTrace T x).result.newCell.2 <
      (rowInsertionTrace (rowInsertionTrace T x).result.tableau y).result.newCell.2 := by
  exact rowInsertionTrace_newCell_right_of_le_aux
    (RowInsertionPathInvariant.initial T x)
    (rowInsertionTrace T x)
    hxy
    (fun {_ _} _ => rfl)
    (rowInsertionTrace (rowInsertionTrace T x).result.tableau y)

/-- Row bumping comparison for two weakly increasing inserted letters. -/
theorem rowBumping_newBox_right_of_le {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {x y : Fin N} (hxy : x ≤ y) :
    (rowInsert T x).newCell.2 <
      (rowInsert (rowInsert T x).tableau y).newCell.2 := by
  exact rowInsertionTrace_newCell_right_of_le T hxy

/-- Strict successive-insertion comparison with an explicit second starting tableau.
If the later inserted letter is strictly smaller, its new cell is weakly to the left. -/
theorem rowInsertionTrace_newCell_col_le_after_gt_aux {N : ℕ} {μ : YoungDiagram} :
    ∀ {T : BoundedSSYT μ N} {row : ℕ} {x y : Fin N}
      (trx : RowInsertionTrace N T row x)
      {S : BoundedSSYT trx.result.shape N}
      (_hS : ∀ {i j : ℕ}, row ≤ i → S.T i j = trx.result.tableau.T i j)
      (trY : RowInsertionTrace N S row y),
      y < x → trY.result.newCell.2 ≤ trx.result.newCell.2 := by
  intro T row x y trx
  induction trx generalizing y with
  | done A =>
      rename_i T₀ row₀ x₀
      intro S hS trY hyx
      cases trY with
      | done AY =>
          have hentry :
              S.T row₀ A.result.newCell.2 = x₀.val := by
            calc
              S.T row₀ A.result.newCell.2 =
                  A.result.tableau.T row₀ A.result.newCell.2 := hS le_rfl
              _ = x₀.val := by simpa [A.newCell_eq] using A.inserted_entry
          have hlt : y.val < S.T row₀ A.result.newCell.2 := by
            simpa [hentry] using hyx
          have hcell : (row₀, A.result.newCell.2) ∈ A.result.shape := by
            simpa only [← A.result_newCell_row] using A.result.newCell_mem
          have hcol_lt : A.result.newCell.2 < A.result.shape.rowLen row₀ := by
            rwa [YoungDiagram.mem_iff_lt_rowLen] at hcell
          have hle : S.T row₀ A.result.newCell.2 ≤ y.val :=
            AY.location.row_entries_le hcol_lt
          exact False.elim (not_lt_of_ge hle hlt)
      | bump BY tailY =>
          have hentry :
              S.T row₀ A.result.newCell.2 = x₀.val := by
            calc
              S.T row₀ A.result.newCell.2 =
                  A.result.tableau.T row₀ A.result.newCell.2 := hS le_rfl
              _ = x₀.val := by simpa [A.newCell_eq] using A.inserted_entry
          have hcell : (row₀, A.result.newCell.2) ∈ A.result.shape := by
            simpa only [← A.result_newCell_row] using A.result.newCell_mem
          have hBY_le : BY.col ≤ A.result.newCell.2 :=
            BY.col_le_of_entry_gt hcell (by simpa [hentry] using hyx)
          exact le_trans
            (RowInsertionPathInvariant.trace_newCell_col_le_cap
              BY.pathInvariant_after_step tailY)
            hBY_le
  | bump B tail ih =>
      rename_i T₀ row₀ x₀
      intro S hS trY hyx
      cases trY with
      | done AY =>
          have hentry :
              S.T row₀ B.col = x₀.val := by
            calc
              S.T row₀ B.col = tail.result.tableau.T row₀ B.col := hS le_rfl
              _ = B.tableau.T row₀ B.col :=
                tail.result_tableau_eq_of_row_lt (by omega) B.cell_mem
              _ = x₀.val := B.replaced_entry
          have hcol_lt : B.col < tail.result.shape.rowLen row₀ := by
            have hcellS : (row₀, B.col) ∈ tail.result.shape :=
              tail.result.old_subset (row₀, B.col) B.cell_mem
            rwa [YoungDiagram.mem_iff_lt_rowLen] at hcellS
          have hle : S.T row₀ B.col ≤ y.val :=
            AY.location.row_entries_le hcol_lt
          omega
      | bump BY tailY =>
          have hcellS : (row₀, B.col) ∈ tail.result.shape :=
            tail.result.old_subset (row₀, B.col) B.cell_mem
          have hentry :
              S.T row₀ B.col = x₀.val := by
            calc
              S.T row₀ B.col = tail.result.tableau.T row₀ B.col := hS le_rfl
              _ = B.tableau.T row₀ B.col :=
                tail.result_tableau_eq_of_row_lt (by omega) B.cell_mem
              _ = x₀.val := B.replaced_entry
          have hBY_le : BY.col ≤ B.col :=
            BY.col_le_of_entry_gt hcellS (by simpa [hentry] using hyx)
          have hBY_bumped_lt : BY.bumped < B.bumped := by
            change BY.bumped.val < B.bumped.val
            have hle : BY.bumped.val ≤ S.T row₀ B.col :=
              BY.bumped_le_entry_of_entry_gt hcellS (by simpa [hentry] using hyx)
            exact lt_of_le_of_lt (by simpa [hentry] using hle) B.bumped_gt
          have hS' :
              ∀ {i j : ℕ}, row₀ + 1 ≤ i →
                BY.tableau.T i j = tail.result.tableau.T i j := by
            intro i j hi
            calc
              BY.tableau.T i j = S.T i j :=
                RowBumpStepResult.unchanged_of_row_ne BY (by omega)
              _ = tail.result.tableau.T i j := hS (by omega)
          exact ih hS' tailY hBY_bumped_lt
/-- Strict successive-insertion comparison: inserting a smaller letter next creates a
new cell weakly to the left of the preceding new cell. -/
theorem rowInsertionTrace_newCell_col_le_after_gt {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {x y : Fin N} (hyx : y < x) :
    (rowInsertionTrace (rowInsertionTrace T x).result.tableau y).result.newCell.2 ≤
      (rowInsertionTrace T x).result.newCell.2 := by
  exact rowInsertionTrace_newCell_col_le_after_gt_aux
    (rowInsertionTrace T x) (fun {_ _} _ => rfl)
    (rowInsertionTrace (rowInsertionTrace T x).result.tableau y) hyx

/-- Strict successive-insertion row comparison: inserting a smaller letter next creates
a new cell in a strictly lower row. -/
theorem rowBumping_newBox_row_lt_after_gt {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {x y : Fin N} (hyx : y < x) :
    (rowInsert T x).newCell.1 <
      (rowInsert (rowInsert T x).tableau y).newCell.1 := by
  let R₁ := rowInsert T x
  let R₂ := rowInsert R₁.tableau y
  have hcol : R₂.newCell.2 ≤ R₁.newCell.2 := by
    exact rowInsertionTrace_newCell_col_le_after_gt T hyx
  have hmem : R₁.newCell ∈ R₂.shape :=
    R₂.old_subset R₁.newCell R₁.newCell_mem
  by_contra hnot
  have hrow : R₂.newCell.1 ≤ R₁.newCell.1 := Nat.le_of_not_gt hnot
  have heq : R₁.newCell = R₂.newCell :=
    R₂.newCell_removable.ge_eq hmem ⟨hrow, hcol⟩
  exact R₂.newCell_not_mem_old (by simpa [heq] using R₁.newCell_mem)

/-- Direct trace comparison for two weakly increasing letters inserted into tableaux that
agree from the current row downward.  This is the same-row version of the row-bumping
comparison: the later/larger insertion cannot finish strictly to the left. -/
theorem rowInsertionTrace_newCell_col_le_of_le_aux {N : ℕ} {μ : YoungDiagram}
    {T S : BoundedSSYT μ N} {row cap : ℕ} {x y : Fin N}
    (hinv : RowInsertionPathInvariant T row cap x)
    (trx : RowInsertionTrace N T row x)
    (hxy : x ≤ y)
    (hS : ∀ {i j : ℕ}, row ≤ i → S.T i j = T.T i j)
    (trY : RowInsertionTrace N S row y) :
    trx.result.newCell.2 ≤ trY.result.newCell.2 := by
  cases trx with
  | done A =>
      cases trY with
      | done Ay =>
          change A.result.newCell.2 ≤ Ay.result.newCell.2
          rw [A.result_newCell_col, Ay.result_newCell_col]
      | bump By _ =>
          let Ly : RowBumpLocation T row y :=
            { col := By.col
              cell_mem := By.cell_mem
              entry_gt := by
                have hSeq : S.T row By.col = T.T row By.col := hS le_rfl
                simpa [hSeq] using By.entry_gt
              left_le := by
                intro j hj hcell
                have hSeq : S.T row j = T.T row j := hS le_rfl
                calc
                  T.T row j = S.T row j := hSeq.symm
                  _ ≤ y.val := By.left_le hj hcell }
          exact False.elim (not_rowBumpLocation_of_append_of_le hxy A.location ⟨Ly⟩)
  | bump B tail =>
      have hinv' : RowInsertionPathInvariant B.tableau (row + 1) B.col B.bumped :=
        RowInsertionPathInvariant.next_after_bump_step hinv B
      cases trY with
      | done Ay =>
          let AyB : RowAppendLocation B.tableau row y :=
            { col := Ay.location.col
              col_eq_rowLen := Ay.location.col_eq_rowLen
              row_entries_le := by
                intro j hj
                by_cases hjcol : j = B.col
                · subst hjcol
                  rw [B.replaced_entry]
                  exact hxy
                · have hSeq : S.T row j = T.T row j := hS le_rfl
                  calc
                    B.tableau.T row j = T.T row j := by
                      rw [RowBumpStepResult.unchanged_of_col_ne B hjcol]
                    _ = S.T row j := hSeq.symm
                    _ ≤ y.val := Ay.location.row_entries_le hj }
          have htail_le : tail.result.newCell.2 ≤ B.col :=
            RowInsertionPathInvariant.trace_newCell_col_le_cap hinv' tail
          have hBlt : B.col < AyB.col :=
            rowBumpStep_col_lt_next_append B AyB
          change tail.result.newCell.2 ≤ Ay.result.newCell.2
          have hAy : Ay.result.newCell.2 = Ay.location.col := by
            rw [Ay.result_newCell_col, Ay.location.col_eq_rowLen]
          rw [hAy]
          exact le_trans htail_le (le_of_lt hBlt)
      | bump By tailY =>
          let LyT : RowBumpLocation T row y :=
            { col := By.col
              cell_mem := By.cell_mem
              entry_gt := by
                have hSeq : S.T row By.col = T.T row By.col := hS le_rfl
                simpa [hSeq] using By.entry_gt
              left_le := by
                intro j hj hcell
                have hSeq : S.T row j = T.T row j := hS le_rfl
                calc
                  T.T row j = S.T row j := hSeq.symm
                  _ ≤ y.val := By.left_le hj hcell }
          have hB_le_By : B.col ≤ By.col :=
            rowBumpLocation_col_le_of_le hxy B.location LyT
          have hbumped_le : B.bumped ≤ By.bumped := by
            change B.bumped.val ≤ By.bumped.val
            rcases lt_or_eq_of_le hB_le_By with hlt | heq
            · calc
                B.bumped.val = T.T row B.col := B.bumped_eq.symm
                _ ≤ T.T row By.col := T.T.row_weak hlt By.cell_mem
                _ = S.T row By.col := (hS le_rfl).symm
                _ = By.bumped.val := By.bumped_eq
            · exact le_of_eq (by
                calc
                  B.bumped.val = T.T row B.col := B.bumped_eq.symm
                  _ = T.T row By.col := by rw [heq]
                  _ = S.T row By.col := (hS le_rfl).symm
                  _ = By.bumped.val := By.bumped_eq)
          have hS' :
              ∀ {i j : ℕ}, row + 1 ≤ i →
                By.tableau.T i j = B.tableau.T i j := by
            intro i j hi
            calc
              By.tableau.T i j = S.T i j :=
                RowBumpStepResult.unchanged_of_row_ne By (by omega)
              _ = T.T i j := hS (by omega)
              _ = B.tableau.T i j :=
                (RowBumpStepResult.unchanged_of_row_ne B (by omega)).symm
          exact rowInsertionTrace_newCell_col_le_of_le_aux hinv' tail hbumped_le hS' tailY
termination_by sizeOf trx

/-- Direct row-bumping comparison for weakly increasing inserted letters. -/
theorem rowInsertionTrace_newCell_col_le_of_le {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {x y : Fin N} (hxy : x ≤ y) :
    (rowInsertionTrace T x).result.newCell.2 ≤
      (rowInsertionTrace T y).result.newCell.2 := by
  exact rowInsertionTrace_newCell_col_le_of_le_aux
    (RowInsertionPathInvariant.initial T x)
    (rowInsertionTrace T x)
    hxy
    (fun {_ _} _ => rfl)
    (rowInsertionTrace T y)

/-- Direct row-bumping comparison for the packaged row insertion result. -/
theorem rowBumping_newBox_col_le_of_le {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) {x y : Fin N} (hxy : x ≤ y) :
    (rowInsert T x).newCell.2 ≤ (rowInsert T y).newCell.2 := by
  exact rowInsertionTrace_newCell_col_le_of_le T hxy

/-- Row insertion from `row` only depends on the part of the tableau at or below `row`.
This transport form permits the ambient shapes to differ above `row`. -/
theorem RowInsertionTrace.result_newCell_eq_of_rows_equiv {N : ℕ} :
    ∀ {μ ν : YoungDiagram} {T : BoundedSSYT μ N} {S : BoundedSSYT ν N}
      {row : ℕ} {x : Fin N}
      (trT : RowInsertionTrace N T row x) (trS : RowInsertionTrace N S row x),
      (∀ {i j : ℕ}, row ≤ i → ((i, j) ∈ μ ↔ (i, j) ∈ ν)) →
      (∀ {i j : ℕ}, row ≤ i → T.T i j = S.T i j) →
      trT.result.newCell = trS.result.newCell := by
  intro μ ν T S row x trT trS hshape hentry
  cases trT with
  | done A =>
      cases trS with
      | done AS =>
          have hrowLen : μ.rowLen row = ν.rowLen row := by
            apply eq_of_forall_lt_iff
            intro j
            rw [← YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.mem_iff_lt_rowLen]
            exact hshape le_rfl
          change A.result.newCell = AS.result.newCell
          rw [A.newCell_eq, AS.newCell_eq, hrowLen]
      | bump BS _ =>
          have hcellT : (row, BS.col) ∈ μ := (hshape le_rfl).2 BS.cell_mem
          have hle : T.T row BS.col ≤ x.val :=
            A.location.row_entries_le (by
              rwa [YoungDiagram.mem_iff_lt_rowLen] at hcellT)
          have heq : T.T row BS.col = S.T row BS.col := hentry le_rfl
          exact False.elim (not_lt_of_ge (by simpa [← heq] using hle) BS.entry_gt)
  | bump B tail =>
      cases trS with
      | done AS =>
          have hcellS : (row, B.col) ∈ ν := (hshape le_rfl).1 B.cell_mem
          have hle : S.T row B.col ≤ x.val :=
            AS.location.row_entries_le (by
              rwa [YoungDiagram.mem_iff_lt_rowLen] at hcellS)
          have heq : T.T row B.col = S.T row B.col := hentry le_rfl
          exact False.elim (not_lt_of_ge (by simpa [← heq] using hle) B.entry_gt)
      | bump BS tailS =>
          let BST : RowBumpLocation T row x :=
            { col := BS.col
              cell_mem := (hshape le_rfl).2 BS.cell_mem
              entry_gt := by
                simpa [hentry le_rfl] using BS.entry_gt
              left_le := by
                intro j hj hcell
                have hcellS : (row, j) ∈ ν := (hshape le_rfl).1 hcell
                simpa [hentry le_rfl] using BS.left_le hj hcellS }
          let BTS : RowBumpLocation S row x :=
            { col := B.col
              cell_mem := (hshape le_rfl).1 B.cell_mem
              entry_gt := by
                simpa [← hentry le_rfl] using B.entry_gt
              left_le := by
                intro j hj hcell
                have hcellT : (row, j) ∈ μ := (hshape le_rfl).2 hcell
                simpa [← hentry le_rfl] using B.left_le hj hcellT }
          have hcol : B.col = BS.col := by
            exact le_antisymm
              (rowBumpLocation_col_le_of_le le_rfl B.location BST)
              (rowBumpLocation_col_le_of_le le_rfl BS.location BTS)
          have hbumped : B.bumped = BS.bumped := by
            apply Fin.ext
            calc
              B.bumped.val = T.T row B.col := B.bumped_eq.symm
              _ = S.T row B.col := hentry le_rfl
              _ = S.T row BS.col := by rw [hcol]
              _ = BS.bumped.val := BS.bumped_eq
          let tailS' : RowInsertionTrace N BS.tableau (row + 1) B.bumped :=
            RowInsertionTrace.castValue hbumped tailS
          have hshape' :
              ∀ {i j : ℕ}, row + 1 ≤ i → ((i, j) ∈ μ ↔ (i, j) ∈ ν) := by
            intro i j hi
            exact hshape (by omega)
          have hentry' :
              ∀ {i j : ℕ}, row + 1 ≤ i → B.tableau.T i j = BS.tableau.T i j := by
            intro i j hi
            calc
              B.tableau.T i j = T.T i j :=
                RowBumpStepResult.unchanged_of_row_ne B (by omega)
              _ = S.T i j := hentry (by omega)
              _ = BS.tableau.T i j :=
                (RowBumpStepResult.unchanged_of_row_ne BS (by omega)).symm
          calc
            tail.result.newCell = tailS'.result.newCell :=
              RowInsertionTrace.result_newCell_eq_of_rows_equiv tail tailS' hshape' hentry'
            _ = tailS.result.newCell := by
              exact congrArg RowInsertResult.newCell
                (RowInsertionTrace.castValue_result_eq hbumped tailS)
termination_by μ ν T S row x trT _trS _hshape _hentry => sizeOf trT

set_option maxRecDepth 4000 in
/-- If a smaller insertion creates a first-column cell while a larger insertion does not,
then inserting the smaller value after the larger one still creates a first-column cell.
The third trace is allowed to start in a tableau equivalent below the current row, which
is what makes the induction stable after commuting the two current-row bump steps. -/
theorem rowInsertionTrace_newCell_col_zero_after_prior_of_le_aux {N : ℕ} :
    ∀ {μ κ ν : YoungDiagram} {T : BoundedSSYT μ N} {W : BoundedSSYT κ N}
      {Z : BoundedSSYT ν N}
      {row : ℕ} {x y : Fin N}
      (trx : RowInsertionTrace N T row x)
      (trY : RowInsertionTrace N W row y)
      (trXY : RowInsertionTrace N Z row x),
      x ≤ y →
      trx.result.newCell.2 = 0 →
      trY.result.newCell.2 ≠ 0 →
      (∀ {i j : ℕ}, row ≤ i → ((i, j) ∈ μ ↔ (i, j) ∈ κ)) →
      (∀ {i j : ℕ}, row ≤ i → T.T i j = W.T i j) →
      (∀ {i j : ℕ}, row ≤ i →
        ((i, j) ∈ trY.result.shape ↔ (i, j) ∈ ν)) →
      (∀ {i j : ℕ}, row ≤ i →
      trY.result.tableau.T i j = Z.T i j) →
      trXY.result.newCell.2 = 0 := by
  intro μ κ ν T W Z row x y trx trY trXY hxy hx hY hshapeTW hentryTW hshape hentry
  cases trx with
  | done A =>
      cases trY with
      | done AY =>
          exact False.elim (hY (by
            simp only [RowInsertionTrace.result] at hx hY ⊢
            rw [AY.result_newCell_col]
            rw [A.result_newCell_col] at hx
            have hrowLen : μ.rowLen row = κ.rowLen row := by
              apply eq_of_forall_lt_iff
              intro j
              rw [← YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.mem_iff_lt_rowLen]
              exact hshapeTW le_rfl
            simpa [← hrowLen] using hx))
      | bump BY _ =>
          have BYT : RowBumpLocation T row y :=
            { col := BY.col
              cell_mem := (hshapeTW le_rfl).2 BY.cell_mem
              entry_gt := by simpa [hentryTW le_rfl] using BY.entry_gt
              left_le := by
                intro j hj hcell
                have hcellW : (row, j) ∈ κ := (hshapeTW le_rfl).1 hcell
                simpa [hentryTW le_rfl] using BY.left_le hj hcellW }
          exact False.elim
            (not_rowBumpLocation_of_append_of_le hxy A.location ⟨BYT⟩)
  | bump B tail =>
      have htail_zero : tail.result.newCell.2 = 0 := hx
      cases trY with
      | done AY =>
          simp only [RowInsertionTrace.result] at hY hshape hentry
          let hB_in_Z : RowBumpLocation Z row x :=
            { col := B.col
              cell_mem := (hshape le_rfl).1
                (AY.result.old_subset (row, B.col) ((hshapeTW le_rfl).1 B.cell_mem))
              entry_gt := by
                rw [← hentry le_rfl,
                  AY.unchanged_on_old_shape ((hshapeTW le_rfl).1 B.cell_mem)]
                rw [← hentryTW le_rfl]
                exact B.entry_gt
              left_le := by
                intro j hj hcell
                have hcell_old : (row, j) ∈ μ := by
                  rw [YoungDiagram.mem_iff_lt_rowLen]
                  have hBcell := B.cell_mem
                  rw [YoungDiagram.mem_iff_lt_rowLen] at hBcell
                  omega
                rw [← hentry le_rfl,
                  AY.unchanged_on_old_shape ((hshapeTW le_rfl).1 hcell_old)]
                rw [← hentryTW le_rfl]
                exact B.left_le hj hcell_old }
          cases trXY with
          | done AXY =>
              exact False.elim
                ((not_lt_of_ge
                  (AXY.location.row_entries_le hB_in_Z.col_lt_rowLen))
                  hB_in_Z.entry_gt)
          | bump BXY tailXY =>
              have hcol : BXY.col = B.col := by
                exact le_antisymm
                  (by simpa using
                    (rowBumpLocation_col_le_of_le le_rfl BXY.location hB_in_Z))
                  (by simpa using
                    (rowBumpLocation_col_le_of_le le_rfl hB_in_Z BXY.location))
              have hbumped : BXY.bumped = B.bumped := by
                apply Fin.ext
                calc
                  BXY.bumped.val = Z.T row BXY.col := BXY.bumped_eq.symm
                  _ = Z.T row B.col := by rw [hcol]
                  _ = AY.result.tableau.T row B.col := (hentry le_rfl).symm
                  _ = W.T row B.col :=
                    AY.unchanged_on_old_shape ((hshapeTW le_rfl).1 B.cell_mem)
                  _ = T.T row B.col := (hentryTW le_rfl).symm
                  _ = B.bumped.val := B.bumped_eq
              let tailXY' : RowInsertionTrace N BXY.tableau (row + 1) B.bumped :=
                RowInsertionTrace.castValue hbumped.symm tailXY
              have hshape' :
                  ∀ {i j : ℕ}, row + 1 ≤ i →
                    ((i, j) ∈ μ ↔ (i, j) ∈ ν) := by
                intro i j hi
                constructor
                · intro hcell
                  exact (hshape (by omega)).1
                    (AY.result.old_subset (i, j) ((hshapeTW (by omega)).1 hcell))
                · intro hcell
                  have hcellAY : (i, j) ∈ AY.result.shape := (hshape (by omega)).2 hcell
                  rcases (AY.result.shape_mem_iff (i, j)).1 hcellAY with hold | hnew
                  · exact (hshapeTW (by omega)).2 hold
                  · have hroweq : i = row := by
                      simpa [AY.newCell_eq] using congrArg Prod.fst hnew
                    omega
              have hentry' :
                  ∀ {i j : ℕ}, row + 1 ≤ i →
                    B.tableau.T i j = BXY.tableau.T i j := by
                intro i j hi
                calc
                  B.tableau.T i j = T.T i j :=
                    RowBumpStepResult.unchanged_of_row_ne B (by omega)
                  _ = W.T i j := hentryTW (by omega)
                  _ = AY.result.tableau.T i j :=
                    (RowAppendStepResult.unchanged_of_row_ne AY (by omega)).symm
                  _ = Z.T i j := hentry (by omega)
                  _ = BXY.tableau.T i j :=
                    (RowBumpStepResult.unchanged_of_row_ne BXY (by omega)).symm
              have heq :=
                RowInsertionTrace.result_newCell_eq_of_rows_equiv tail tailXY' hshape' hentry'
              have htailXY' : tailXY'.result.newCell.2 = 0 := by
                simpa [heq] using htail_zero
              rw [RowInsertionTrace.castValue_result_eq hbumped.symm tailXY] at htailXY'
              exact htailXY'
      | bump BY tailY =>
          simp only [RowInsertionTrace.result] at hY hshape hentry
          let BYT : RowBumpLocation T row y :=
            { col := BY.col
              cell_mem := (hshapeTW le_rfl).2 BY.cell_mem
              entry_gt := by simpa [hentryTW le_rfl] using BY.entry_gt
              left_le := by
                intro j hj hcell
                have hcellW : (row, j) ∈ κ := (hshapeTW le_rfl).1 hcell
                simpa [hentryTW le_rfl] using BY.left_le hj hcellW }
          have hB_le_BY : B.col ≤ BY.col :=
            by simpa [BYT] using rowBumpLocation_col_le_of_le hxy B.location BYT
          rcases lt_or_eq_of_le hB_le_BY with hcol_lt | hcol_eq
          · let hB_in_Z : RowBumpLocation Z row x :=
              { col := B.col
                cell_mem := by
                  exact (hshape le_rfl).1
                    (tailY.result.old_subset (row, B.col)
                      ((hshapeTW le_rfl).1 B.cell_mem))
                entry_gt := by
                  rw [← hentry le_rfl]
                  rw [tailY.result_tableau_eq_of_row_lt (by omega)
                    ((hshapeTW le_rfl).1 B.cell_mem)]
                  rw [RowBumpStepResult.unchanged_of_col_ne BY (by omega)]
                  rw [← hentryTW le_rfl]
                  exact B.entry_gt
                left_le := by
                  intro j hj hcell
                  rw [← hentry le_rfl]
                  have hcell_old : (row, j) ∈ μ := by
                    rw [YoungDiagram.mem_iff_lt_rowLen]
                    have hBcell := B.cell_mem
                    rw [YoungDiagram.mem_iff_lt_rowLen] at hBcell
                    omega
                  rw [tailY.result_tableau_eq_of_row_lt (by omega)
                    ((hshapeTW le_rfl).1 hcell_old)]
                  rw [RowBumpStepResult.unchanged_of_col_ne BY (by omega)]
                  rw [← hentryTW le_rfl]
                  exact B.left_le hj hcell_old }
            cases trXY with
            | done AXY =>
                exact False.elim
                  ((not_lt_of_ge
                    (AXY.location.row_entries_le hB_in_Z.col_lt_rowLen))
                    hB_in_Z.entry_gt)
            | bump BXY tailXY =>
                have hcolXY : BXY.col = B.col := by
                  exact le_antisymm
                    (by simpa using
                      (rowBumpLocation_col_le_of_le le_rfl BXY.location hB_in_Z))
                    (by simpa using
                      (rowBumpLocation_col_le_of_le le_rfl hB_in_Z BXY.location))
                have hbumpedXY : BXY.bumped = B.bumped := by
                  apply Fin.ext
                  calc
                    BXY.bumped.val = Z.T row BXY.col := BXY.bumped_eq.symm
                    _ = Z.T row B.col := by rw [hcolXY]
                    _ = tailY.result.tableau.T row B.col := (hentry le_rfl).symm
                    _ = BY.tableau.T row B.col :=
                      tailY.result_tableau_eq_of_row_lt (by omega)
                        ((hshapeTW le_rfl).1 B.cell_mem)
                    _ = W.T row B.col :=
                      RowBumpStepResult.unchanged_of_col_ne BY (by omega)
                    _ = T.T row B.col := (hentryTW le_rfl).symm
                    _ = B.bumped.val := B.bumped_eq
                have hbumped_le : B.bumped ≤ BY.bumped := by
                  change B.bumped.val ≤ BY.bumped.val
                  calc
                    B.bumped.val = T.T row B.col := B.bumped_eq.symm
                    _ ≤ T.T row BY.col := T.T.row_weak hcol_lt BYT.cell_mem
                    _ = W.T row BY.col := hentryTW le_rfl
                    _ = BY.bumped.val := BY.bumped_eq
                let tailXY' : RowInsertionTrace N BXY.tableau (row + 1) B.bumped :=
                  RowInsertionTrace.castValue hbumpedXY.symm tailXY
                have hshape' :
                    ∀ {i j : ℕ}, row + 1 ≤ i →
                      ((i, j) ∈ μ ↔ (i, j) ∈ κ) := by
                  intro i j hi
                  exact hshapeTW (by omega)
                have hentry' :
                    ∀ {i j : ℕ}, row + 1 ≤ i →
                      B.tableau.T i j = BY.tableau.T i j := by
                  intro i j hi
                  calc
                    B.tableau.T i j = T.T i j :=
                      RowBumpStepResult.unchanged_of_row_ne B (by omega)
                    _ = W.T i j := hentryTW (by omega)
                    _ = BY.tableau.T i j :=
                      (RowBumpStepResult.unchanged_of_row_ne BY (by omega)).symm
                have hshapeY' :
                    ∀ {i j : ℕ}, row + 1 ≤ i →
                      ((i, j) ∈ tailY.result.shape ↔ (i, j) ∈ ν) := by
                  intro i j hi
                  exact hshape (by omega)
                have hentryY' :
                    ∀ {i j : ℕ}, row + 1 ≤ i →
                      tailY.result.tableau.T i j = BXY.tableau.T i j := by
                  intro i j hi
                  calc
                    tailY.result.tableau.T i j = Z.T i j := hentry (by omega)
                    _ = BXY.tableau.T i j :=
                      (RowBumpStepResult.unchanged_of_row_ne BXY (by omega)).symm
                have hrec : tailXY'.result.newCell.2 = 0 :=
                  rowInsertionTrace_newCell_col_zero_after_prior_of_le_aux
                    (trx := tail) (trY := tailY) (trXY := tailXY')
                    hbumped_le htail_zero hY hshape' hentry' hshapeY' hentryY'
                rw [RowInsertionTrace.castValue_result_eq hbumpedXY.symm tailXY] at hrec
                exact hrec
          · have hbumped : B.bumped = BY.bumped := by
              apply Fin.ext
              calc
                B.bumped.val = T.T row B.col := B.bumped_eq.symm
                _ = T.T row BY.col := by rw [hcol_eq]
                _ = W.T row BY.col := hentryTW le_rfl
                _ = BY.bumped.val := BY.bumped_eq
            let tailY' : RowInsertionTrace N BY.tableau (row + 1) B.bumped :=
              RowInsertionTrace.castValue hbumped tailY
            have hshape' :
                ∀ {i j : ℕ}, row + 1 ≤ i → ((i, j) ∈ μ ↔ (i, j) ∈ κ) := by
              intro i j hi
              exact hshapeTW (by omega)
            have hentry' :
                ∀ {i j : ℕ}, row + 1 ≤ i →
                  B.tableau.T i j = BY.tableau.T i j := by
              intro i j hi
              calc
                B.tableau.T i j = T.T i j :=
                  RowBumpStepResult.unchanged_of_row_ne B (by omega)
                _ = W.T i j := hentryTW (by omega)
                _ = BY.tableau.T i j :=
                  (RowBumpStepResult.unchanged_of_row_ne BY (by omega)).symm
            have heq :=
              RowInsertionTrace.result_newCell_eq_of_rows_equiv tail tailY' hshape' hentry'
            have htailY' : tailY'.result.newCell.2 = 0 := by
              simpa [heq] using htail_zero
            exact False.elim (hY (by
              rw [RowInsertionTrace.castValue_result_eq hbumped tailY] at htailY'
              exact htailY'))
termination_by _μ _κ _ν _T _W _Z _row _x _y trx _trY _trXY _hxy _hx _hY
    _hshapeTW _hentryTW _hshape _hentry => sizeOf trx

/-- Chosen-trace form of the first-column preservation lemma. -/
theorem rowInsertionTrace_newCell_col_zero_after_prior_of_le {N : ℕ}
    {μ : YoungDiagram} (T : BoundedSSYT μ N) {x y : Fin N}
    (hxy : x ≤ y)
    (hx : (rowInsertionTrace T x).result.newCell.2 = 0)
    (hY : (rowInsertionTrace T y).result.newCell.2 ≠ 0) :
    (rowInsertionTrace (rowInsertionTrace T y).result.tableau x).result.newCell.2 = 0 := by
  exact rowInsertionTrace_newCell_col_zero_after_prior_of_le_aux
    (rowInsertionTrace T x)
    (rowInsertionTrace T y)
    (rowInsertionTrace (rowInsertionTrace T y).result.tableau x)
    hxy hx hY
    (fun {_ _} _ => Iff.rfl)
    (fun {_ _} _ => rfl)
    (fun {_ _} _ => Iff.rfl)
    (fun {_ _} _ => rfl)

theorem RowAppendStepResult.reverseTrace_after_delete_with_continuation {N : ℕ}
    {μ : YoungDiagram} {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (A : RowAppendStepResult T row x)
    (cont : ReverseRowInsertionTrace N T (row - 1) x) :
    let D := deleteCorner A.result.tableau A.result.newCell A.result.newCell_removable
    ∃ tr : ReverseRowInsertionTrace N D.tableau (A.result.newCell.1 - 1) D.value,
      tr.result.2 = cont.result.2 ∧ HEq tr.result.1 cont.result.1 := by
  classical
  let D := deleteCorner A.result.tableau A.result.newCell A.result.newCell_removable
  rcases A.deleteCorner_inverse with ⟨hshape, htableau, hvalue⟩
  have hrow : A.result.newCell.1 - 1 = row - 1 := by
    rw [A.result_newCell_row]
  let tr0 : ReverseRowInsertionTrace N D.tableau (row - 1) x :=
    ReverseRowInsertionTrace.castOfHEq hshape.symm htableau.symm cont
  change ∃ tr : ReverseRowInsertionTrace N D.tableau (A.result.newCell.1 - 1) D.value,
      tr.result.2 = cont.result.2 ∧ HEq tr.result.1 cont.result.1
  rw [hvalue, hrow]
  refine ⟨tr0, ?_, ?_⟩
  · exact ReverseRowInsertionTrace.castOfHEq_result_value_eq
      hshape.symm htableau.symm cont
  · exact ReverseRowInsertionTrace.castOfHEq_result_tableau_heq
      hshape.symm htableau.symm cont

theorem RowInsertionTrace.reverseTrace_after_delete_with_continuation {N : ℕ}
    {μ : YoungDiagram} {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (tr : RowInsertionTrace N T row x)
    (hrow_start : row ≠ 0)
    (cont : ReverseRowInsertionTrace N T (row - 1) x) :
    let R := tr.result
    let D := deleteCorner R.tableau R.newCell R.newCell_removable
    ∃ rev : ReverseRowInsertionTrace N D.tableau (R.newCell.1 - 1) D.value,
      rev.result.2 = cont.result.2 ∧ HEq rev.result.1 cont.result.1 := by
  classical
  induction tr with
  | done A =>
      simpa [RowInsertionTrace.result] using
        A.reverseTrace_after_delete_with_continuation cont
  | bump B tail ih =>
      rename_i T₀ row₀ x₀
      let RB := reverseRowBumpStep B.tableau row₀ B.bumped B.reverseLocation
      have hRB_value : RB.bumped = x₀ :=
        reverseRowBumpStep_forward_bump_bumped B
      have hRB_tableau : HEq RB.tableau T₀ :=
        reverseRowBumpStep_forward_bump_tableau_heq B
      have hRB_shape : μ = μ := rfl
      let contVal : ReverseRowInsertionTrace N T₀ (row₀ - 1) RB.bumped :=
        ReverseRowInsertionTrace.castMoving hRB_value cont
      have hcontVal_val : contVal.result.2 = cont.result.2 := by
        exact ReverseRowInsertionTrace.castMoving_def_result_value_eq hRB_value cont
      have hcontVal_tab : HEq contVal.result.1 cont.result.1 := by
        exact ReverseRowInsertionTrace.castMoving_def_result_tableau_heq hRB_value cont
      let cont0 : ReverseRowInsertionTrace N RB.tableau (row₀ - 1) RB.bumped :=
        ReverseRowInsertionTrace.castOfHEq hRB_shape hRB_tableau.symm contVal
      have hcont0_val : cont0.result.2 = cont.result.2 := by
        calc
          cont0.result.2 = contVal.result.2 :=
            ReverseRowInsertionTrace.castOfHEq_result_value_eq hRB_shape hRB_tableau.symm
              contVal
          _ = cont.result.2 := hcontVal_val
      have hcont0_tab : HEq cont0.result.1 cont.result.1 := by
        have hcast :
            HEq cont0.result.1 contVal.result.1 :=
          ReverseRowInsertionTrace.castOfHEq_result_tableau_heq hRB_shape hRB_tableau.symm
            contVal
        exact hcast.trans hcontVal_tab
      have hrow_ne : row₀ ≠ 0 := hrow_start
      let contB : ReverseRowInsertionTrace N B.tableau row₀ B.bumped :=
        ReverseRowInsertionTrace.bump hrow_ne RB cont0
      have htail_start : row₀ + 1 ≠ 0 := by omega
      rcases ih htail_start contB with ⟨rev, hval, htab⟩
      refine ⟨rev, ?_, ?_⟩
      · exact hval.trans hcont0_val
      · exact htab.trans hcont0_tab

theorem RowBumpStepResult.reverseTrace_after_delete_of_top_bump {N : ℕ}
    {μ : YoungDiagram} {T : BoundedSSYT μ N} {x : Fin N}
    (B : RowBumpStepResult T 0 x)
    (tail : RowInsertionTrace N B.tableau 1 B.bumped) :
    let R := (RowInsertionTrace.bump B tail).result
    let D := deleteCorner R.tableau R.newCell R.newCell_removable
    ∃ rev : ReverseRowInsertionTrace N D.tableau (R.newCell.1 - 1) D.value,
      rev.result.2 = x ∧ HEq rev.result.1 T := by
  classical
  let RB := reverseRowBumpStep B.tableau 0 B.bumped B.reverseLocation
  have hRB_value : RB.bumped = x :=
    reverseRowBumpStep_forward_bump_bumped B
  have hRB_tableau : HEq RB.tableau T :=
    reverseRowBumpStep_forward_bump_tableau_heq B
  let contB : ReverseRowInsertionTrace N B.tableau (1 - 1) B.bumped := by
    simpa using (ReverseRowInsertionTrace.done RB)
  have htail_start : (1 : ℕ) ≠ 0 := by omega
  rcases tail.reverseTrace_after_delete_with_continuation htail_start contB with
    ⟨rev, hval, htab⟩
  refine ⟨rev, ?_, ?_⟩
  · calc
      rev.result.2 = contB.result.2 := hval
      _ = RB.bumped := by
        simp [contB, ReverseRowInsertionTrace.result]
      _ = x := hRB_value
  · have htabRB : HEq contB.result.1 RB.tableau := by
      simp [contB, ReverseRowInsertionTrace.result]
    exact htab.trans (htabRB.trans hRB_tableau)

/-- Trace-level inverse property for reverse row insertion after a forward insertion. -/
def ReverseRowInsertInverseTraceSpec {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) : Prop :=
  let R := (rowInsertionTrace T x).result
  (reverseRowInsert R.tableau R.newCell R.newCell_removable).shape = μ ∧
    HEq (reverseRowInsert R.tableau R.newCell R.newCell_removable).tableau T ∧
    (reverseRowInsert R.tableau R.newCell R.newCell_removable).value = x

/-- Trace-level inverse theorem for row insertion followed by reverse row insertion.

This packages the append terminal API and the forward-bump/reverse-bump local API into
the exact specification needed by the public `rowInsert` inverse statement. -/
theorem reverseRowInsert_inverse_traceSpec {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N) :
    ReverseRowInsertInverseTraceSpec T x := by
  classical
  change
    let R := (rowInsertionTrace T x).result
    (reverseRowInsert R.tableau R.newCell R.newCell_removable).shape = μ ∧
      HEq (reverseRowInsert R.tableau R.newCell R.newCell_removable).tableau T ∧
      (reverseRowInsert R.tableau R.newCell R.newCell_removable).value = x
  generalize htr : rowInsertionTrace T x = tr
  cases tr with
  | done A =>
      have htop : (RowInsertionTrace.done A).result.newCell.1 = 0 := by
        simpa [RowInsertionTrace.result] using A.result_newCell_row
      simp only [RowInsertionTrace.result] at htop ⊢
      unfold reverseRowInsert
      rw [dif_pos htop]
      exact A.deleteCorner_inverse
  | bump B tail =>
      let R := tail.result
      let D := deleteCorner R.tableau R.newCell R.newCell_removable
      have hnot_top : R.newCell.1 ≠ 0 := by
        have hge : 1 ≤ R.newCell.1 := by
          simpa [R] using tail.result_newCell_row_ge
        omega
      rcases B.reverseTrace_after_delete_of_top_bump tail with ⟨rev, hrev_value, hrev_tableau⟩
      have hshape_delete : D.shape = μ := by
        simpa [D, R] using (RowInsertResult.deleteCorner_shape_inverse R)
      have hshape :
          (reverseRowInsert R.tableau R.newCell R.newCell_removable).shape = μ := by
        exact (reverseRowInsert_shape_eq_deleteCorner R.tableau R.newCell
          R.newCell_removable).trans hshape_delete
      have htableau :
          HEq (reverseRowInsert R.tableau R.newCell R.newCell_removable).tableau T := by
        have hbridge :
            HEq (reverseRowInsert R.tableau R.newCell R.newCell_removable).tableau
              rev.result.1 := by
          simpa [D, R] using
            reverseRowInsert_tableau_heq_of_reverseTrace_of_not_top
              R.tableau R.newCell R.newCell_removable hnot_top rev
        exact hbridge.trans hrev_tableau
      have hvalue :
          (reverseRowInsert R.tableau R.newCell R.newCell_removable).value = x := by
        have hbridge :
            (reverseRowInsert R.tableau R.newCell R.newCell_removable).value =
              rev.result.2 := by
          simpa [D, R] using
            reverseRowInsert_value_eq_of_reverseTrace_of_not_top
              R.tableau R.newCell R.newCell_removable hnot_top rev
        exact hbridge.trans hrev_value
      simpa [RowInsertionTrace.result, R] using ⟨hshape, htableau, hvalue⟩

/-- The public inverse statement follows from its trace-level inverse specification. -/
theorem reverseRowInsert_inverse_of_traceSpec {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (x : Fin N)
    (hspec : ReverseRowInsertInverseTraceSpec T x) :
    (reverseRowInsert (rowInsert T x).tableau
        (rowInsert T x).newCell (rowInsert T x).newCell_removable).shape = μ ∧
      HEq
        (reverseRowInsert (rowInsert T x).tableau
          (rowInsert T x).newCell (rowInsert T x).newCell_removable).tableau
        T ∧
        (reverseRowInsert (rowInsert T x).tableau
        (rowInsert T x).newCell (rowInsert T x).newCell_removable).value = x := by
  exact hspec

/-- The empty bounded tableau, used as the initial KRS state. -/
noncomputable def emptyBoundedSSYT (N : ℕ) : BoundedSSYT (⊥ : YoungDiagram) N where
  T := default
  bound := by
    intro i j hcell
    simp at hcell

/-- State carried by forward KRS insertion: two same-shape bounded SSYTs. -/
structure KRSForwardState (m n : ℕ) where
  shape : YoungDiagram
  P : BoundedSSYT shape n
  Q : BoundedSSYT shape m

namespace KRSForwardState

noncomputable def empty (m n : ℕ) : KRSForwardState m n where
  shape := ⊥
  P := emptyBoundedSSYT n
  Q := emptyBoundedSSYT m

def toTableauPair {m n : ℕ} (S : KRSForwardState m n) : TableauPair m n where
  shape := S.shape
  P := S.P
  Q := S.Q

end KRSForwardState

namespace TableauPair

def toForwardState {m n : ℕ} (T : TableauPair m n) : KRSForwardState m n where
  shape := T.shape
  P := T.P
  Q := T.Q

@[simp]
theorem toForwardState_toTableauPair {m n : ℕ} (T : TableauPair m n) :
    T.toForwardState.toTableauPair = T := rfl

end TableauPair

/-- Local semistandardness conditions for appending a recording entry in the new KRS cell.

These hypotheses are intentionally explicit: for an arbitrary `Q`, entry `a`, and
row-insertion result `R`, appending `a` is not automatically semistandard. In the real KRS
induction these inequalities come from the sorted biword hypothesis and the row-bumping
comparison theorem. -/
structure RecordingAppendHyp {m n : ℕ} {μ : YoungDiagram}
    (Q : BoundedSSYT μ m) (a : Fin m) (R : RowInsertResult n μ) where
  left_le :
    ∀ {j : ℕ}, j < R.newCell.2 → (R.newCell.1, j) ∈ μ →
      Q.T R.newCell.1 j ≤ a.val
  above_lt :
    ∀ {i : ℕ}, i < R.newCell.1 → (i, R.newCell.2) ∈ μ →
      Q.T i R.newCell.2 < a.val

/-- Add the recording letter to `Q` in the new cell produced by inserting into `P`,
assuming the local row/column inequalities needed for semistandardness. -/
noncomputable def krsAppendRecording {m n : ℕ} {μ : YoungDiagram}
    (Q : BoundedSSYT μ m) (a : Fin m) (R : RowInsertResult n μ)
    (h : RecordingAppendHyp Q a R) :
    BoundedSSYT R.shape m :=
  RowAppendStepResult.appendTableau Q R.newCell a R.extendsByCell
    R.newCell_not_mem_old h.left_le h.above_lt

theorem krsAppendRecording_entry_newCell {m n : ℕ} {μ : YoungDiagram}
    (Q : BoundedSSYT μ m) (a : Fin m) (R : RowInsertResult n μ)
    (h : RecordingAppendHyp Q a R) :
    (krsAppendRecording Q a R h).T R.newCell.1 R.newCell.2 = a.val := by
  change
    RowAppendStepResult.appendEntry Q R.newCell a R.newCell.1 R.newCell.2 = a.val
  rw [RowAppendStepResult.appendEntry_newCell]

theorem krsAppendRecording_entry_old {m n : ℕ} {μ : YoungDiagram}
    (Q : BoundedSSYT μ m) (a : Fin m) (R : RowInsertResult n μ)
    (h : RecordingAppendHyp Q a R) {i j : ℕ} (hcell : (i, j) ∈ μ) :
    (krsAppendRecording Q a R h).T i j = Q.T i j := by
  change RowAppendStepResult.appendEntry Q R.newCell a i j = Q.T i j
  rw [RowAppendStepResult.appendEntry_ne]
  intro heq
  exact R.newCell_not_mem_old (by simpa [heq] using hcell)

theorem krsAppendRecording_deleteCorner_inverse {m n : ℕ} {μ : YoungDiagram}
    (Q : BoundedSSYT μ m) (a : Fin m) (R : RowInsertResult n μ)
    (h : RecordingAppendHyp Q a R) :
    let Q' := krsAppendRecording Q a R h
    let D := deleteCorner Q' R.newCell R.newCell_removable
    D.shape = μ ∧ HEq D.tableau Q ∧ D.value = a := by
  classical
  let Q' := krsAppendRecording Q a R h
  let D := deleteCorner Q' R.newCell R.newCell_removable
  have hshape : D.shape = μ := by
    simpa [D] using RowInsertResult.deleteCorner_shape_inverse R
  have htableau : HEq D.tableau Q := by
    apply BoundedSSYT.heq_of_entry_eq hshape
    intro i j
    by_cases hcellD : (i, j) ∈ D.shape
    · have hcellR : (i, j) ∈ R.shape := D.shape_subset_old hcellD
      have hcellμ : (i, j) ∈ μ := by
        rcases (R.shape_mem_iff (i, j)).1 hcellR with hμ | hnew
        · exact hμ
        · exact False.elim (D.cell_not_mem_shape (by simpa [hnew] using hcellD))
      calc
        D.tableau.T i j = Q'.T i j := deleteCorner_tableau_entry Q' R.newCell
          R.newCell_removable hcellD
        _ = Q.T i j := krsAppendRecording_entry_old Q a R h hcellμ
    · have hcellμ_not : (i, j) ∉ μ := by
        intro hcellμ
        have hcellD' : (i, j) ∈ D.shape := by
          simpa [hshape] using hcellμ
        exact hcellD hcellD'
      calc
        D.tableau.T i j = 0 := D.tableau.T.zeros hcellD
        _ = Q.T i j := (Q.T.zeros hcellμ_not).symm
  have hvalue : D.value = a := by
    apply Fin.ext
    have hval : D.value.val = Q'.T R.newCell.1 R.newCell.2 := by
      simp [D, deleteCorner]
    rw [hval]
    exact krsAppendRecording_entry_newCell Q a R h
  exact ⟨hshape, htableau, hvalue⟩

/-- One forward KRS step, once the local recording inequalities have been supplied.

The local hypotheses are not true for an arbitrary state and arbitrary next letter.
They are a sorted-prefix invariant of the KRS construction, so the proof is threaded
through the run relation below rather than manufactured here. -/
noncomputable def krsForwardStep {m n : ℕ}
    (S : KRSForwardState m n) (z : Fin m × Fin n)
    (hrec : let R := rowInsert S.P z.2; RecordingAppendHyp S.Q z.1 R) :
    KRSForwardState m n :=
  let R := rowInsert S.P z.2
  { shape := R.shape
    P := R.tableau
    Q := krsAppendRecording S.Q z.1 R hrec }

/-- Forward KRS states reachable by scanning a sorted biword prefix.

The `snoc` constructor records exactly the proof obligation needed to append the
recording tableau entry.  This avoids the false interface asserting that every
arbitrary `KRSForwardState` accepts every next recording letter. -/
inductive KRSForwardRun {m n : ℕ} :
    List (Fin m × Fin n) → KRSForwardState m n → Prop where
  | nil :
      KRSForwardRun [] (KRSForwardState.empty m n)
  | snoc {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
      (z : Fin m × Fin n)
      (hrun : KRSForwardRun w S)
      (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y))
      (hrec : let R := rowInsert S.P z.2; RecordingAppendHyp S.Q z.1 R)
      (hsame_next : ∀ y : Fin m × Fin n,
        ((w ++ [z]) ++ [y]).Pairwise (fun x y => toLex x ≤ toLex y) →
          let S' := krsForwardStep S z hrec
          let R := rowInsert S'.P y.2
          ∀ {c : ℕ × ℕ}, c ∈ S'.shape → S'.Q.T c.1 c.2 = y.1.val →
            c.2 < R.newCell.2) :
      KRSForwardRun (w ++ [z]) (krsForwardStep S z hrec)

namespace KRSForwardRun

/-- Source labels transported along a complete KRS run.  The label attached to a newly
inserted lower letter is its position in the processed prefix. -/
inductive OriginRun {m n : ℕ} :
    ∀ {w : List (Fin m × Fin n)} {S : KRSForwardState m n},
      KRSForwardRun w S → RowInsertionTrace.OriginLabels → Prop
  | nil :
      OriginRun (.nil : KRSForwardRun ([] : List (Fin m × Fin n))
        (KRSForwardState.empty m n)) (fun _ _ => none)
  | snoc {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
      {z : Fin m × Fin n}
      {hrun : KRSForwardRun w S}
      {hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y)}
      {hrec : let R := rowInsert S.P z.2; RecordingAppendHyp S.Q z.1 R}
      {hsame_next : ∀ y : Fin m × Fin n,
        ((w ++ [z]) ++ [y]).Pairwise (fun x y => toLex x ≤ toLex y) →
          let S' := krsForwardStep S z hrec
          let R := rowInsert S'.P y.2
          ∀ {c : ℕ × ℕ}, c ∈ S'.shape → S'.Q.T c.1 c.2 = y.1.val →
            c.2 < R.newCell.2}
      {labels : RowInsertionTrace.OriginLabels}
      (origin : OriginRun hrun labels)
      (hvalid : labels.Valid S.shape) :
      OriginRun (.snoc z hrun hsorted hrec hsame_next)
        (RowInsertionTrace.TaggedRowInsertionTrace.resultLabels
          (RowInsertionTrace.TaggedRowInsertionTrace.ofTrace labels w.length
            (rowInsertionTrace S.P z.2) hvalid))

theorem exists_originRun {m n : ℕ} {w : List (Fin m × Fin n)}
    {S : KRSForwardState m n} (hrun : KRSForwardRun w S) :
    ∃ labels, OriginRun hrun labels ∧ labels.Valid S.shape := by
  induction hrun with
  | nil =>
      refine ⟨fun _ _ => none, .nil, ?_⟩
      intro i j hcell
      simp [KRSForwardState.empty] at hcell
  | @snoc w S z hrun hsorted hrec hsame_next ih =>
      rcases ih with ⟨labels, origin, hvalid⟩
      let tr := rowInsertionTrace S.P z.2
      let tagged :=
        RowInsertionTrace.TaggedRowInsertionTrace.ofTrace labels w.length tr hvalid
      exact ⟨tagged.resultLabels,
        .snoc (hsorted := hsorted) (hrec := hrec) (hsame_next := hsame_next)
          origin hvalid,
        by
          change tagged.resultLabels.Valid (rowInsertionTrace S.P z.2).result.shape
          exact tagged.valid_resultLabels hvalid⟩

/-- Every processed lower letter has a current representative in the insertion tableau.
The representative may move downward when later letters bump it, but its source label
and value are preserved. -/
def OriginRepresentatives {m n : ℕ} (w : List (Fin m × Fin n))
    (S : KRSForwardState m n) (labels : RowInsertionTrace.OriginLabels) : Prop :=
  ∀ (k : ℕ) (hk : k < w.length),
    ∃ c ∈ S.shape,
      labels c.1 c.2 = some k ∧ S.P.T c.1 c.2 = (w.get ⟨k, hk⟩).2.val

theorem OriginRun.representatives {m n : ℕ} {w : List (Fin m × Fin n)}
    {S : KRSForwardState m n} {hrun : KRSForwardRun w S}
    {labels : RowInsertionTrace.OriginLabels}
    (origin : OriginRun hrun labels) :
    OriginRepresentatives w S labels := by
  induction origin with
  | nil =>
      intro k hk
      simp at hk
  | @snoc w S z hrun hsorted hrec hsame_next labels origin hvalid ih =>
      intro k hk
      let tr := rowInsertionTrace S.P z.2
      let tagged :=
        RowInsertionTrace.TaggedRowInsertionTrace.ofTrace labels w.length tr hvalid
      by_cases hk_last : k = w.length
      · subst k
        rcases tagged.exists_resultLabels_eq_tag_and_entry_eq with ⟨c, hcell, htag, hvalue⟩
        refine ⟨c, ?_, htag, ?_⟩
        · simpa [krsForwardStep, tr] using hcell
        · simpa using hvalue
      · have hk_old : k < w.length := by
          simpa [List.length_append] using
            (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (by simpa [List.length_append] using hk))
              hk_last)
        rcases ih k hk_old with ⟨c, hcell, htag, hvalue⟩
        rcases tagged.exists_resultLabels_eq_of_old_entry hcell htag hvalue with
          ⟨d, hdcell, hdtag, hdvalue⟩
        refine ⟨d, ?_, hdtag, ?_⟩
        · simpa [krsForwardStep, tr] using hdcell
        · simpa [List.get_eq_getElem, hk_old] using hdvalue

/-- Every recording-tableau entry in a reachable state comes from the processed prefix. -/
def QEntriesFromPrefix {m n : ℕ} {w : List (Fin m × Fin n)}
    (S : KRSForwardState m n) : Prop :=
  ∀ {c : ℕ × ℕ}, c ∈ S.shape →
    ∃ x ∈ w, S.Q.T c.1 c.2 = x.1.val

/-- For a sorted prefix followed by `z`, all old recording entries are weakly below
the new upper letter. -/
def OldQEntriesLeNext {m n : ℕ} (S : KRSForwardState m n) (z : Fin m × Fin n) :
    Prop :=
  ∀ {c : ℕ × ℕ}, c ∈ S.shape → S.Q.T c.1 c.2 ≤ z.1.val

/-- Among old cells with the same upper letter as `z`, the row-insertion comparison
places them strictly to the left of the new cell produced by inserting `z.2`. -/
def SameUpperCellsLeftOfNext {m n : ℕ}
    (S : KRSForwardState m n) (z : Fin m × Fin n) : Prop :=
  let R := rowInsert S.P z.2
  ∀ {c : ℕ × ℕ}, c ∈ S.shape → S.Q.T c.1 c.2 = z.1.val → c.2 < R.newCell.2

/-- A reachable state's shape has one box for each processed biword letter. -/
theorem shape_card {m n : ℕ} {w : List (Fin m × Fin n)}
    {S : KRSForwardState m n} (hrun : KRSForwardRun w S) :
    S.shape.card = w.length := by
  induction hrun with
  | nil =>
      simp [KRSForwardState.empty]
  | snoc z hrun hsorted hrec hsame_next ih =>
      simp only [krsForwardStep, List.length_append,
      List.length_cons, List.length_nil, zero_add]
      rw [rowInsert_adds_one_box, ih]

theorem sorted {m n : ℕ} {w : List (Fin m × Fin n)}
    {S : KRSForwardState m n} (hrun : KRSForwardRun w S) :
    w.Pairwise (fun x y => toLex x ≤ toLex y) := by
  induction hrun with
  | nil =>
      simp
  | snoc z hrun hsorted hrec hsame_next ih =>
      exact hsorted

/-- Source invariant for recording entries, proved by the same run induction that
constructs the recording tableau. -/
theorem qEntriesFromPrefix {m n : ℕ} {w : List (Fin m × Fin n)}
    {S : KRSForwardState m n} (hrun : KRSForwardRun w S) :
    QEntriesFromPrefix (w := w) S := by
  induction hrun with
  | nil =>
      intro c hcell
      simp [KRSForwardState.empty] at hcell
  | snoc z hrun hsorted hrec hsame_next ih =>
      rename_i w₀ S₀
      intro c hcell
      have hsplit :
          c ∈ S₀.shape ∨ c = (rowInsert S₀.P z.2).newCell := by
        simpa [krsForwardStep] using
          ((rowInsert S₀.P z.2).shape_mem_iff c).1 hcell
      rcases hsplit with hold | hnew
      · rcases ih hold with ⟨x, hxmem, hxeq⟩
        refine ⟨x, by simp [hxmem], ?_⟩
        have hne : c ≠ (rowInsert S₀.P z.2).newCell := by
          intro hc
          exact (rowInsert S₀.P z.2).newCell_not_mem_old (by simpa [hc] using hold)
        change
          RowAppendStepResult.appendEntry S₀.Q (rowInsert S₀.P z.2).newCell z.1
            c.1 c.2 = x.1.val
        rw [RowAppendStepResult.appendEntry_ne _ _ _ hne]
        exact hxeq
      · refine ⟨z, by simp, ?_⟩
        subst c
        change
          RowAppendStepResult.appendEntry S₀.Q (rowInsert S₀.P z.2).newCell z.1
            (rowInsert S₀.P z.2).newCell.1 (rowInsert S₀.P z.2).newCell.2 = z.1.val
        rw [RowAppendStepResult.appendEntry_newCell]

/-- The source invariant plus sortedness imply that all old recording entries are
weakly below the next upper letter. -/
theorem oldQEntriesLeNext_of_entriesFromPrefix {m n : ℕ}
    {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
    (hsource : QEntriesFromPrefix (w := w) S)
    (z : Fin m × Fin n)
    (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y)) :
    OldQEntriesLeNext S z := by
  intro c hcell
  rcases hsource hcell with ⟨x, hxmem, hxeq⟩
  have hxz : toLex x ≤ toLex z := by
    have hxmem' : x ∈ w ++ [z] := by
      exact List.mem_append_left [z] hxmem
    have hzmem' : z ∈ w ++ [z] := by
      exact List.mem_append_right w (by simp)
    have hbefore : ∀ y ∈ [z], toLex x ≤ toLex y := by
      have hpair := List.pairwise_append.mp hsorted
      exact hpair.2.2 x hxmem
    exact hbefore z (by simp)
  have hupper : x.1 ≤ z.1 := (Prod.Lex.toLex_le_toLex'.mp hxz).1
  rw [hxeq]
  exact hupper

/-- Equal-upper old cells lie strictly to the left of the next new cell.  This is the
place where the row-bumping comparison for equal upper letters belongs. -/
theorem sameUpperCellsLeftOfNext_of_run {m n : ℕ}
    {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
    (hrun : KRSForwardRun w S) (z : Fin m × Fin n)
    (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y)) :
    SameUpperCellsLeftOfNext S z := by
  induction hrun with
  | nil =>
      intro c hcell heq
      simp [KRSForwardState.empty] at hcell
  | snoc z₀ hrun hsorted₀ hrec₀ hsame_next ih =>
      exact hsame_next z hsorted

end KRSForwardRun

/-- Sorted-prefix KRS induction supplies the local recording inequalities.

The hypotheses say that the state was produced from the preceding sorted prefix and
that appending `z` preserves sortedness.  The proof combines the source-cell invariant
for the recording tableau with the same-upper row-bumping comparison. -/
theorem krsForwardStep_recordingHyp_of_run {m n : ℕ}
    {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
    (_hrun : KRSForwardRun w S) (z : Fin m × Fin n)
    (_hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y))
    (hold_le : KRSForwardRun.OldQEntriesLeNext S z)
    (hsame_left : KRSForwardRun.SameUpperCellsLeftOfNext S z) :
    let R := rowInsert S.P z.2
    RecordingAppendHyp S.Q z.1 R := by
  classical
  let R := rowInsert S.P z.2
  refine
    { left_le := ?_
      above_lt := ?_ }
  · intro j hj hcell
    exact hold_le hcell
  · intro i hi hcell
    have hle : S.Q.T i R.newCell.2 ≤ z.1.val := hold_le hcell
    exact lt_of_le_of_ne hle (by
      intro heq
      have hleft : R.newCell.2 < R.newCell.2 :=
        hsame_left (c := (i, R.newCell.2)) hcell heq
      exact Nat.lt_irrefl R.newCell.2 hleft)

/-- Stability of the same-upper/right-moving invariant after one certified KRS step.

This is the row-bumping comparison needed to construct certified forward runs.  The
proof splits an old cell of the new state into either an old cell of `S` or the
newly-created `z` cell.  In the new-cell case it uses
`rowBumping_newBox_right_of_le`; in the old-cell case the sortedness hypotheses and
the source invariant rule out a later upper letter unless the intervening `z` has the
same upper letter, reducing again to the certified invariant for `z` followed by the
row-bumping comparison from `z` to `y`. -/
theorem krsForwardStep_sameUpperCellsLeftOfNext {m n : ℕ}
    {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
    (hrun : KRSForwardRun w S) (z : Fin m × Fin n)
    (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y))
    (hrec : let R := rowInsert S.P z.2; RecordingAppendHyp S.Q z.1 R) :
    ∀ y : Fin m × Fin n,
      ((w ++ [z]) ++ [y]).Pairwise (fun x y => toLex x ≤ toLex y) →
        let S' := krsForwardStep S z hrec
        let R := rowInsert S'.P y.2
        ∀ {c : ℕ × ℕ}, c ∈ S'.shape → S'.Q.T c.1 c.2 = y.1.val →
          c.2 < R.newCell.2 := by
  intro y hsorted_next
  change
    ∀ {c : ℕ × ℕ}, c ∈ (krsForwardStep S z hrec).shape →
      (krsForwardStep S z hrec).Q.T c.1 c.2 = y.1.val →
        c.2 < (rowInsert (krsForwardStep S z hrec).P y.2).newCell.2
  intro c hc hcy
  let S' := krsForwardStep S z hrec
  let Rz := rowInsert S.P z.2
  let Ry := rowInsert S'.P y.2
  have hsource : KRSForwardRun.QEntriesFromPrefix (w := w) S :=
    KRSForwardRun.qEntriesFromPrefix hrun
  have hold_le : KRSForwardRun.OldQEntriesLeNext S z :=
    KRSForwardRun.oldQEntriesLeNext_of_entriesFromPrefix hsource z hsorted
  have hsame_z : KRSForwardRun.SameUpperCellsLeftOfNext S z :=
    KRSForwardRun.sameUpperCellsLeftOfNext_of_run hrun z hsorted
  have hzy_lex : toLex z ≤ toLex y := by
    have hcross := (List.pairwise_append.mp hsorted_next).2.2
    exact hcross z (by simp) y (by simp)
  have hzy_upper : z.1 ≤ y.1 := (Prod.Lex.toLex_le_toLex'.mp hzy_lex).1
  have hsplit : c ∈ S.shape ∨ c = Rz.newCell := by
    simpa [S', krsForwardStep, Rz] using
      (Rz.shape_mem_iff c).1 hc
  rcases hsplit with hold | hnew
  · have hne : c ≠ Rz.newCell := by
      intro hcnew
      exact Rz.newCell_not_mem_old (by simpa [hcnew] using hold)
    have hcy_old : S.Q.T c.1 c.2 = y.1.val := by
      have hcy' : RowAppendStepResult.appendEntry S.Q Rz.newCell z.1 c.1 c.2 = y.1.val := by
        simpa [S', krsForwardStep, krsAppendRecording,
        RowAppendStepResult.appendTableau, Rz] using hcy
      rwa [RowAppendStepResult.appendEntry_ne _ _ _ hne] at hcy'
    have hy_le_z : y.1 ≤ z.1 := by
      rw [Fin.le_def]
      calc
        y.1.val = S.Q.T c.1 c.2 := hcy_old.symm
        _ ≤ z.1.val := hold_le hold
    have hupper_eq : z.1 = y.1 := le_antisymm hzy_upper hy_le_z
    have hz_lower_le_y : z.2 ≤ y.2 := by
      exact (Prod.Lex.toLex_le_toLex'.mp hzy_lex).2 hupper_eq
    have hc_left_z : c.2 < Rz.newCell.2 := by
      exact hsame_z hold (by simpa [hupper_eq] using hcy_old)
    have hz_left_y : Rz.newCell.2 < Ry.newCell.2 := by
      simpa [S', Rz, Ry, krsForwardStep] using
        rowBumping_newBox_right_of_le S.P hz_lower_le_y
    exact lt_trans hc_left_z hz_left_y
  · subst c
    have hzy_val : z.1.val = y.1.val := by
      have hcy' :
          RowAppendStepResult.appendEntry S.Q Rz.newCell z.1 Rz.newCell.1 Rz.newCell.2 =
            y.1.val := by
        simpa [S', krsForwardStep, krsAppendRecording,
        RowAppendStepResult.appendTableau, Rz] using hcy
      simpa [RowAppendStepResult.appendEntry_newCell] using hcy'
    have hupper_eq : z.1 = y.1 := Fin.ext hzy_val
    have hz_lower_le_y : z.2 ≤ y.2 := by
      exact (Prod.Lex.toLex_le_toLex'.mp hzy_lex).2 hupper_eq
    simpa [S', Rz, Ry, krsForwardStep] using
      rowBumping_newBox_right_of_le S.P hz_lower_le_y

/-- Every sorted biword has a forward KRS run.

This is intentionally phrased as existence rather than an unconditional fold.  The
recursive construction must consume the sorted-prefix proof at each append step. -/
theorem exists_krsForwardRun_of_pairwise {m n : ℕ}
    (w : List (Fin m × Fin n))
    (hsorted : w.Pairwise (fun x y => toLex x ≤ toLex y)) :
    ∃ S : KRSForwardState m n, KRSForwardRun w S := by
  induction w using List.reverseRecOn with
  | nil =>
      exact ⟨KRSForwardState.empty m n, KRSForwardRun.nil⟩
  | append_singleton w z ih =>
      have hprefix : w.Pairwise (fun x y => toLex x ≤ toLex y) := by
        exact (List.pairwise_append.mp hsorted).1
      rcases ih hprefix with ⟨S, hrun⟩
      have hsource : KRSForwardRun.QEntriesFromPrefix (w := w) S :=
        KRSForwardRun.qEntriesFromPrefix hrun
      have hold_le : KRSForwardRun.OldQEntriesLeNext S z :=
        KRSForwardRun.oldQEntriesLeNext_of_entriesFromPrefix hsource z hsorted
      have hsame_left : KRSForwardRun.SameUpperCellsLeftOfNext S z :=
        KRSForwardRun.sameUpperCellsLeftOfNext_of_run hrun z hsorted
      have hrec :
          let R := rowInsert S.P z.2
          RecordingAppendHyp S.Q z.1 R :=
        krsForwardStep_recordingHyp_of_run hrun z hsorted hold_le hsame_left
      have hsame_next :
          ∀ y : Fin m × Fin n,
            ((w ++ [z]) ++ [y]).Pairwise (fun x y => toLex x ≤ toLex y) →
              let S' := krsForwardStep S z hrec
              let R := rowInsert S'.P y.2
              ∀ {c : ℕ × ℕ}, c ∈ S'.shape → S'.Q.T c.1 c.2 = y.1.val →
                c.2 < R.newCell.2 :=
        krsForwardStep_sameUpperCellsLeftOfNext hrun z hsorted hrec
      exact ⟨krsForwardStep S z hrec,
        KRSForwardRun.snoc z hrun hsorted hrec hsame_next⟩

/-- Forward KRS state obtained by scanning a sorted biword from left to right. -/
noncomputable def krsForwardStateOfList {m n : ℕ}
    (w : List (Fin m × Fin n))
    (hsorted : w.Pairwise (fun x y => toLex x ≤ toLex y)) : KRSForwardState m n :=
  Classical.choose (exists_krsForwardRun_of_pairwise w hsorted)

/-- The state chosen by `krsForwardStateOfList` is certified by a forward run. -/
theorem krsForwardStateOfList_run {m n : ℕ}
    (w : List (Fin m × Fin n))
    (hsorted : w.Pairwise (fun x y => toLex x ≤ toLex y)) :
    KRSForwardRun w (krsForwardStateOfList w hsorted) :=
  Classical.choose_spec (exists_krsForwardRun_of_pairwise w hsorted)

/-- A single reverse KRS step removes one recording entry and reverses the corresponding
row insertion step in `P`. -/
structure KRSReverseStepResult {m n : ℕ} (T : TableauPair m n) where
  previous : TableauPair m n
  letter : Fin m × Fin n
  card_previous : previous.shape.card + 1 = T.shape.card

/-- The corner selected by one reverse KRS step.

It is a removable corner whose recording entry is maximal; among cells with the same
maximal recording entry, the selected cell is rightmost. The rightmost tie-break is the
one compatible with the row-bumping comparison for equal upper letters. -/
structure MaxRecordingCorner {m n : ℕ} (T : TableauPair m n) where
  cell : ℕ × ℕ
  cell_mem : cell ∈ T.shape
  removable : IsRemovableCorner T.shape cell
  max_entry :
    ∀ {d : ℕ × ℕ}, d ∈ T.shape → T.Q.T d.1 d.2 ≤ T.Q.T cell.1 cell.2
  rightmost_of_same_entry :
    ∀ {d : ℕ × ℕ}, d ∈ T.shape →
      T.Q.T d.1 d.2 = T.Q.T cell.1 cell.2 → d.2 ≤ cell.2

/-- Existence of the reverse KRS corner with the specified tie-breaking rule. -/
theorem exists_maxRecordingCorner {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0) :
    Nonempty (MaxRecordingCorner T) := by
  classical
  let weight : ℕ × ℕ → ℕ ×ₗ ℕ := fun c => toLex (T.Q.T c.1 c.2, c.2)
  have hcells : T.shape.cells.Nonempty := by
    change T.shape.cells.card ≠ 0 at h_nonempty
    exact Finset.card_ne_zero.mp h_nonempty
  rcases Finset.exists_max_image T.shape.cells weight hcells with ⟨c, hc_cells, hcmax⟩
  have hc : c ∈ T.shape := by
    simpa [YoungDiagram.mem_cells] using hc_cells
  have hmax_entry :
      ∀ {d : ℕ × ℕ}, d ∈ T.shape → T.Q.T d.1 d.2 ≤ T.Q.T c.1 c.2 := by
    intro d hd
    have hd_cells : d ∈ T.shape.cells := by
      simpa [YoungDiagram.mem_cells] using hd
    have hle := hcmax d hd_cells
    exact (Prod.Lex.toLex_le_toLex'.mp hle).1
  have hright :
      ∀ {d : ℕ × ℕ}, d ∈ T.shape →
        T.Q.T d.1 d.2 = T.Q.T c.1 c.2 → d.2 ≤ c.2 := by
    intro d hd hentry
    have hd_cells : d ∈ T.shape.cells := by
      simpa [YoungDiagram.mem_cells] using hd
    have hle := hcmax d hd_cells
    exact (Prod.Lex.toLex_le_toLex'.mp hle).2 hentry
  have hge_eq : ∀ {d : ℕ × ℕ}, d ∈ T.shape → c ≤ d → d = c := by
    intro d hd hcd
    apply Prod.ext
    · apply le_antisymm
      · by_contra hnot
        have hlt : c.1 < d.1 := by omega
        have hcol_mem : (d.1, c.2) ∈ T.shape :=
          T.shape.up_left_mem le_rfl hcd.2 hd
        have hq_lt : T.Q.T c.1 c.2 < T.Q.T d.1 c.2 :=
          T.Q.T.col_strict hlt hcol_mem
        have hq_le : T.Q.T d.1 c.2 ≤ T.Q.T c.1 c.2 :=
          hmax_entry hcol_mem
        exact (not_lt_of_ge hq_le) hq_lt
      · exact hcd.1
    · apply le_antisymm
      · have hentry_eq : T.Q.T d.1 d.2 = T.Q.T c.1 c.2 := by
          apply le_antisymm
          · exact hmax_entry hd
          · have hrow_le : T.Q.T c.1 c.2 ≤ T.Q.T d.1 d.2 := by
              by_cases hrow : c.1 = d.1
              · rcases lt_or_eq_of_le hcd.2 with hcol_lt | hcol_eq
                · rw [hrow]
                  exact T.Q.T.row_weak hcol_lt hd
                · have hdc : d = c := by
                    ext <;> omega
                  simp [hdc]
              · have hlt : c.1 < d.1 := lt_of_le_of_ne hcd.1 hrow
                have hcol_mem : (d.1, c.2) ∈ T.shape :=
                  T.shape.up_left_mem le_rfl hcd.2 hd
                have hq_lt : T.Q.T c.1 c.2 < T.Q.T d.1 c.2 :=
                  T.Q.T.col_strict hlt hcol_mem
                have hrow_le' : T.Q.T d.1 c.2 ≤ T.Q.T d.1 d.2 := by
                  rcases lt_or_eq_of_le hcd.2 with hcol_lt | hcol_eq
                  · exact T.Q.T.row_weak hcol_lt hd
                  · simp [hcol_eq]
                exact le_trans (le_of_lt hq_lt) hrow_le'
            exact hrow_le
        exact hright hd hentry_eq
      · exact hcd.2
  exact ⟨{
    cell := c
    cell_mem := hc
    removable := IsRemovableCorner.of_ge_eq hc hge_eq
    max_entry := hmax_entry
    rightmost_of_same_entry := hright }⟩

/-- The selected reverse KRS corner. This is the only choice point for the reverse
algorithm, and its specification fixes the max-entry/rightmost tie-breaking convention. -/
noncomputable def maxRecordingCorner {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0) :
    MaxRecordingCorner T :=
  Classical.choice (exists_maxRecordingCorner T h_nonempty)

theorem maxRecordingCorner_max_entry {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0)
    {d : ℕ × ℕ} (hd : d ∈ T.shape) :
    T.Q.T d.1 d.2 ≤
      T.Q.T (maxRecordingCorner T h_nonempty).cell.1
        (maxRecordingCorner T h_nonempty).cell.2 :=
  (maxRecordingCorner T h_nonempty).max_entry hd

theorem maxRecordingCorner_rightmost_of_same_entry {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0)
    {d : ℕ × ℕ} (hd : d ∈ T.shape)
    (heq :
      T.Q.T d.1 d.2 =
        T.Q.T (maxRecordingCorner T h_nonempty).cell.1
          (maxRecordingCorner T h_nonempty).cell.2) :
    d.2 ≤ (maxRecordingCorner T h_nonempty).cell.2 :=
  (maxRecordingCorner T h_nonempty).rightmost_of_same_entry hd heq

/-- Cast a bounded SSYT across an equality of shapes. -/
noncomputable def castBoundedSSYT {N : ℕ} {μ ν : YoungDiagram}
    (h : μ = ν) (T : BoundedSSYT μ N) : BoundedSSYT ν N := by
  subst h
  exact T

theorem castBoundedSSYT_entry {N : ℕ} {μ ν : YoungDiagram}
    (h : μ = ν) (T : BoundedSSYT μ N) (i j : ℕ) :
    (castBoundedSSYT h T).T i j = T.T i j := by
  subst h
  rfl

theorem castBoundedSSYT_heq {N : ℕ} {μ ν : YoungDiagram}
    (h : μ = ν) (T : BoundedSSYT μ N) :
    HEq (castBoundedSSYT h T) T := by
  subst h
  exact HEq.rfl

/-- One reverse KRS step. It chooses the maximal/rightmost recording corner, removes it
from `Q`, and performs true reverse row insertion on `P` at the same corner. -/
noncomputable def reverseKrsStep {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0) :
    KRSReverseStepResult T :=
  let C := maxRecordingCorner T h_nonempty
  let Pinv := reverseRowInsert T.P C.cell C.removable
  let Qdel := deleteCorner T.Q C.cell C.removable
  have hshape : Qdel.shape = Pinv.shape := by
    have hdel :
        Qdel.shape = (deleteCorner T.P C.cell C.removable).shape := rfl
    exact hdel.trans (reverseRowInsert_shape_eq_deleteCorner T.P C.cell C.removable).symm
  { previous :=
      { shape := Pinv.shape
        P := Pinv.tableau
        Q := castBoundedSSYT hshape Qdel.tableau }
    letter :=
      (⟨T.Q.T C.cell.1 C.cell.2, T.Q.bound C.cell_mem⟩, Pinv.value)
    card_previous := (reverseRowInsert_removes_one_box T.P C.cell C.removable).symm }

theorem reverseKrsStep_letter_upper_eq_corner {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0) :
    (reverseKrsStep T h_nonempty).letter.1.val =
      T.Q.T (maxRecordingCorner T h_nonempty).cell.1
        (maxRecordingCorner T h_nonempty).cell.2 := by
  unfold reverseKrsStep
  rfl

theorem reverseKrsStep_letter_lower_eq_reverseRowInsert {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0) :
    (reverseKrsStep T h_nonempty).letter.2 =
      (reverseRowInsert T.P
        (maxRecordingCorner T h_nonempty).cell
        (maxRecordingCorner T h_nonempty).removable).value := by
  unfold reverseKrsStep
  rfl

theorem reverseKrsStep_letter_upper_max {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0)
    {d : ℕ × ℕ} (hd : d ∈ T.shape) :
    T.Q.T d.1 d.2 ≤ (reverseKrsStep T h_nonempty).letter.1.val := by
  rw [reverseKrsStep_letter_upper_eq_corner]
  exact maxRecordingCorner_max_entry T h_nonempty hd

theorem reverseKrsStep_previous_Q_entry {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0)
    {i j : ℕ} (hcell : (i, j) ∈ (reverseKrsStep T h_nonempty).previous.shape) :
    (reverseKrsStep T h_nonempty).previous.Q.T i j = T.Q.T i j := by
  classical
  unfold reverseKrsStep
  simp only
  let C := maxRecordingCorner T h_nonempty
  let Pinv := reverseRowInsert T.P C.cell C.removable
  let Qdel := deleteCorner T.Q C.cell C.removable
  have hshape : Qdel.shape = Pinv.shape := by
    have hdel :
        Qdel.shape = (deleteCorner T.P C.cell C.removable).shape := rfl
    exact hdel.trans (reverseRowInsert_shape_eq_deleteCorner T.P C.cell C.removable).symm
  have hcellQ : (i, j) ∈ Qdel.shape := by
    simpa [hshape] using hcell
  calc
    (castBoundedSSYT hshape Qdel.tableau).T i j = Qdel.tableau.T i j :=
      castBoundedSSYT_entry hshape Qdel.tableau i j
    _ = T.Q.T i j := deleteCorner_tableau_entry T.Q C.cell C.removable hcellQ

theorem reverseKrsStep_previous_shape_subset {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0) :
    (reverseKrsStep T h_nonempty).previous.shape ≤ T.shape := by
  classical
  unfold reverseKrsStep
  simp only
  let C := maxRecordingCorner T h_nonempty
  exact reverseRowInsert_shape_subset T.P C.cell C.removable

theorem reverseKrsStep_previous_Q_le_letter {m n : ℕ}
    (T : TableauPair m n) (h_nonempty : T.shape.card ≠ 0)
    {c : ℕ × ℕ} (hcell : c ∈ (reverseKrsStep T h_nonempty).previous.shape) :
    (reverseKrsStep T h_nonempty).previous.Q.T c.1 c.2 ≤
      (reverseKrsStep T h_nonempty).letter.1.val := by
  have hold : c ∈ T.shape :=
    reverseKrsStep_previous_shape_subset T h_nonempty hcell
  rw [reverseKrsStep_previous_Q_entry T h_nonempty hcell]
  exact reverseKrsStep_letter_upper_max T h_nonempty hold

theorem reverseKrsStep_previous_P_entry_of_current_corner_row_le {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    {i j : ℕ}
    (hi : (maxRecordingCorner T h).cell.1 ≤ i)
    (hcell : (i, j) ∈ (reverseKrsStep T h).previous.shape) :
    (reverseKrsStep T h).previous.P.T i j = T.P.T i j := by
  classical
  unfold reverseKrsStep
  simp only
  let C := maxRecordingCorner T h
  let Pinv := reverseRowInsert T.P C.cell C.removable
  change Pinv.tableau.T i j = T.P.T i j
  exact reverseRowInsert_tableau_entry_of_removed_row_le T.P C.cell C.removable
    (by simpa [C] using hi) (by simpa [Pinv, C] using hcell)

theorem reverseKrsStep_next_same_upper_corner_col_le {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1) :
    (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.2 ≤
      (maxRecordingCorner T h).cell.2 := by
  let step := reverseKrsStep T h
  let C₂ := maxRecordingCorner step.previous hprev
  have hC₂_prev : C₂.cell ∈ step.previous.shape := C₂.cell_mem
  have hC₂_old : C₂.cell ∈ T.shape :=
    reverseKrsStep_previous_shape_subset T h hC₂_prev
  apply maxRecordingCorner_rightmost_of_same_entry T h hC₂_old
  have hQprev :
      step.previous.Q.T C₂.cell.1 C₂.cell.2 = T.Q.T C₂.cell.1 C₂.cell.2 := by
    simpa [step, C₂] using
      reverseKrsStep_previous_Q_entry T h hC₂_prev
  have hnext_upper :
      (reverseKrsStep step.previous hprev).letter.1.val =
        step.previous.Q.T C₂.cell.1 C₂.cell.2 := by
    simpa [step, C₂] using
      reverseKrsStep_letter_upper_eq_corner step.previous hprev
  have hcurr_upper :
      step.letter.1.val =
        T.Q.T (maxRecordingCorner T h).cell.1 (maxRecordingCorner T h).cell.2 := by
    simpa [step] using reverseKrsStep_letter_upper_eq_corner T h
  calc
    T.Q.T C₂.cell.1 C₂.cell.2 = step.previous.Q.T C₂.cell.1 C₂.cell.2 := hQprev.symm
    _ = (reverseKrsStep step.previous hprev).letter.1.val := hnext_upper.symm
    _ = step.letter.1.val := by rw [hsame]
    _ = T.Q.T (maxRecordingCorner T h).cell.1 (maxRecordingCorner T h).cell.2 :=
      hcurr_upper

theorem reverseKrsStep_next_same_upper_corner_col_lt {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1) :
    (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.2 <
      (maxRecordingCorner T h).cell.2 := by
  classical
  let step := reverseKrsStep T h
  let C := maxRecordingCorner T h
  let C₂ := maxRecordingCorner step.previous hprev
  have hle : C₂.cell.2 ≤ C.cell.2 := by
    simpa [step, C, C₂] using
      reverseKrsStep_next_same_upper_corner_col_le T h hprev hsame
  rcases lt_or_eq_of_le hle with hlt | hcol_eq
  · exact hlt
  · exfalso
    have hC₂_prev : C₂.cell ∈ step.previous.shape := C₂.cell_mem
    have hC₂_old : C₂.cell ∈ T.shape := by
      simpa [step, C₂] using reverseKrsStep_previous_shape_subset T h hC₂_prev
    have hC₂_ne_C : C₂.cell ≠ C.cell := by
      intro heq
      have hnot : C.cell ∉ step.previous.shape := by
        simpa [step, C] using
          reverseRowInsert_removedCell_not_mem T.P C.cell C.removable
      exact hnot (by simpa [heq] using hC₂_prev)
    have hentry :
        T.Q.T C₂.cell.1 C₂.cell.2 = T.Q.T C.cell.1 C.cell.2 := by
      have hQprev :
          step.previous.Q.T C₂.cell.1 C₂.cell.2 =
            T.Q.T C₂.cell.1 C₂.cell.2 := by
        simpa [step, C₂] using
          reverseKrsStep_previous_Q_entry T h hC₂_prev
      have hnext_upper :
          (reverseKrsStep step.previous hprev).letter.1.val =
            step.previous.Q.T C₂.cell.1 C₂.cell.2 := by
        simpa [step, C₂] using
          reverseKrsStep_letter_upper_eq_corner step.previous hprev
      have hcurr_upper :
          step.letter.1.val = T.Q.T C.cell.1 C.cell.2 := by
        simpa [step, C] using reverseKrsStep_letter_upper_eq_corner T h
      calc
        T.Q.T C₂.cell.1 C₂.cell.2 = step.previous.Q.T C₂.cell.1 C₂.cell.2 := hQprev.symm
        _ = (reverseKrsStep step.previous hprev).letter.1.val := hnext_upper.symm
        _ = step.letter.1.val := by rw [hsame]
        _ = T.Q.T C.cell.1 C.cell.2 := hcurr_upper
    have hrow_ne : C₂.cell.1 ≠ C.cell.1 := by
      intro hrow_eq
      exact hC₂_ne_C (Prod.ext hrow_eq hcol_eq)
    rcases lt_or_gt_of_ne hrow_ne with hrow_lt | hrow_gt
    · have hcell : (C.cell.1, C₂.cell.2) ∈ T.shape := by
        simpa [hcol_eq] using C.cell_mem
      have hlt_entry : T.Q.T C₂.cell.1 C₂.cell.2 <
          T.Q.T C.cell.1 C₂.cell.2 :=
        T.Q.T.col_strict hrow_lt hcell
      have hlt_entry' :
          T.Q.T C₂.cell.1 C.cell.2 < T.Q.T C.cell.1 C.cell.2 := by
        simpa [hcol_eq] using hlt_entry
      have hentry' :
          T.Q.T C₂.cell.1 C.cell.2 = T.Q.T C.cell.1 C.cell.2 := by
        simpa [hcol_eq] using hentry
      exact (not_lt_of_ge (le_of_eq hentry'.symm)) hlt_entry'
    · have hcell : (C₂.cell.1, C.cell.2) ∈ T.shape := by
        have hp : (C₂.cell.1, C.cell.2) = C₂.cell := by
          ext <;> simp [hcol_eq]
        simpa [hp] using hC₂_old
      have hlt_entry : T.Q.T C.cell.1 C.cell.2 <
          T.Q.T C₂.cell.1 C.cell.2 :=
        T.Q.T.col_strict hrow_gt hcell
      have hlt_entry' :
          T.Q.T C.cell.1 C.cell.2 < T.Q.T C₂.cell.1 C₂.cell.2 := by
        simpa [hcol_eq] using hlt_entry
      exact (not_lt_of_ge (le_of_eq hentry)) hlt_entry'

theorem reverseKrsStep_next_same_upper_corner_row_ge {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1) :
    (maxRecordingCorner T h).cell.1 ≤
      (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1 := by
  classical
  let step := reverseKrsStep T h
  let C := maxRecordingCorner T h
  let C₂ := maxRecordingCorner step.previous hprev
  have hC₂_prev : C₂.cell ∈ step.previous.shape := C₂.cell_mem
  have hC₂_old : C₂.cell ∈ T.shape := by
    simpa [step, C₂] using reverseKrsStep_previous_shape_subset T h hC₂_prev
  have hcol_lt : C₂.cell.2 < C.cell.2 := by
    simpa [step, C, C₂] using
      reverseKrsStep_next_same_upper_corner_col_lt T h hprev hsame
  have hentry :
      T.Q.T C₂.cell.1 C₂.cell.2 = T.Q.T C.cell.1 C.cell.2 := by
    have hQprev :
        step.previous.Q.T C₂.cell.1 C₂.cell.2 =
          T.Q.T C₂.cell.1 C₂.cell.2 := by
      simpa [step, C₂] using
        reverseKrsStep_previous_Q_entry T h hC₂_prev
    have hnext_upper :
        (reverseKrsStep step.previous hprev).letter.1.val =
          step.previous.Q.T C₂.cell.1 C₂.cell.2 := by
      simpa [step, C₂] using
        reverseKrsStep_letter_upper_eq_corner step.previous hprev
    have hcurr_upper :
        step.letter.1.val = T.Q.T C.cell.1 C.cell.2 := by
      simpa [step, C] using reverseKrsStep_letter_upper_eq_corner T h
    calc
      T.Q.T C₂.cell.1 C₂.cell.2 = step.previous.Q.T C₂.cell.1 C₂.cell.2 := hQprev.symm
      _ = (reverseKrsStep step.previous hprev).letter.1.val := hnext_upper.symm
      _ = step.letter.1.val := by rw [hsame]
      _ = T.Q.T C.cell.1 C.cell.2 := hcurr_upper
  apply le_of_not_gt
  intro hrow_lt
  have hcell_mid : (C.cell.1, C₂.cell.2) ∈ T.shape :=
    T.shape.up_left_mem le_rfl (Nat.le_of_lt hcol_lt) C.cell_mem
  have hstrict :
      T.Q.T C₂.cell.1 C₂.cell.2 < T.Q.T C.cell.1 C₂.cell.2 :=
    T.Q.T.col_strict hrow_lt hcell_mid
  have hweak :
      T.Q.T C.cell.1 C₂.cell.2 ≤ T.Q.T C.cell.1 C.cell.2 :=
    T.Q.T.row_weak hcol_lt C.cell_mem
  have hlt : T.Q.T C₂.cell.1 C₂.cell.2 < T.Q.T C.cell.1 C.cell.2 :=
    lt_of_lt_of_le hstrict hweak
  exact (not_lt_of_ge (le_of_eq hentry.symm)) hlt

theorem reverseKrsStep_next_same_upper_start_row_le {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1) :
    (maxRecordingCorner T h).cell.1 - 1 ≤
      (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1 - 1 := by
  have hrow :
      (maxRecordingCorner T h).cell.1 ≤
        (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1 :=
    reverseKrsStep_next_same_upper_corner_row_ge T h hprev hsame
  omega

theorem reverseKrsStep_next_same_upper_corner_nonTop_of_current_nonTop {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hcurrent_nonTop : (maxRecordingCorner T h).cell.1 ≠ 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1) :
    (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1 ≠ 0 := by
  have hrow :
      (maxRecordingCorner T h).cell.1 ≤
        (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1 :=
    reverseKrsStep_next_same_upper_corner_row_ge T h hprev hsame
  omega

theorem reverseKrsStep_letter_lower_le_deleted_P_entry {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0) :
    (reverseKrsStep T h).letter.2.val ≤
      T.P.T (maxRecordingCorner T h).cell.1 (maxRecordingCorner T h).cell.2 := by
  classical
  unfold reverseKrsStep
  simp only
  let C := maxRecordingCorner T h
  exact reverseRowInsert_value_le_deletedValue T.P C.cell C.removable

theorem reverseKrsStep_next_lower_le_of_deleted_P_le {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hdeleted :
      (reverseKrsStep T h).previous.P.T
          (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1
          (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.2 ≤
        (reverseKrsStep T h).letter.2.val) :
    (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.2 ≤
      (reverseKrsStep T h).letter.2 := by
  rw [Fin.le_def]
  exact le_trans
    (reverseKrsStep_letter_lower_le_deleted_P_entry
      (reverseKrsStep T h).previous hprev)
    hdeleted

theorem reverseKrsStep_next_lower_le_of_same_upper_current_top {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hcurrent_top : (maxRecordingCorner T h).cell.1 = 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1) :
    (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.2 ≤
      (reverseKrsStep T h).letter.2 := by
  classical
  let C := maxRecordingCorner T h
  let step := reverseKrsStep T h
  let C₂ := maxRecordingCorner step.previous hprev
  have hleft : C₂.cell.2 ≤ C.cell.2 := by
    simpa [step, C, C₂] using
      reverseKrsStep_next_same_upper_corner_col_le T h hprev hsame
  unfold reverseKrsStep
  simp only
  change
    (reverseRowInsert
        (reverseRowInsert T.P C.cell C.removable).tableau
        C₂.cell C₂.removable).value ≤
      (reverseRowInsert T.P C.cell C.removable).value
  exact reverseRowInsert_value_le_after_left_corner_of_current_top'
    T.P C.removable C₂.removable (by simpa [C] using hcurrent_top) hleft

theorem reverseKrsStep_second_topCol_lt_of_same_upper_traceColumnInvariant
    {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hcurrent_nonTop : (maxRecordingCorner T h).cell.1 ≠ 0)
    (hsecond_nonTop :
      (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1 ≠ 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1) :
    let C := maxRecordingCorner T h
    let step := reverseKrsStep T h
    let C₂ := maxRecordingCorner step.previous hprev
    let D₁ := deleteCorner T.P C.cell C.removable
    let start₁ := C.cell.1 - 1
    let htr₁ : ∃ tr : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value,
        tr.RespectsLowerCap C.cell.2 := by
      simpa [D₁, start₁, C] using
        exists_reverseRowInsertionTrace_afterDelete_with_respects
          T.P C.cell C.removable hcurrent_nonTop
    let tr₁ := Classical.choose htr₁
    let R₁ := reverseRowInsert T.P C.cell C.removable
    let D₂ := deleteCorner R₁.tableau C₂.cell C₂.removable
    let start₂ := C₂.cell.1 - 1
    let htr₂ : ∃ tr : ReverseRowInsertionTrace n D₂.tableau start₂ D₂.value,
        tr.RespectsLowerCap C₂.cell.2 := by
      simpa [D₂, start₂] using
        exists_reverseRowInsertionTrace_afterDelete_with_respects
          R₁.tableau C₂.cell C₂.removable hsecond_nonTop
    let tr₂ := Classical.choose htr₂
    tr₂.movingAt start₁ ≤ D₁.value →
    (∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₂.shape → (i, j) ∈ D₁.shape) →
    (∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₁.shape → (i, j) ∈ D₂.shape) →
    (∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₂.shape → (i, j) ∈ D₁.shape →
      D₁.tableau.T i j = (tr₂.tableauAt start₁).T i j) →
    ReverseRowInsertionTrace.StrictlyLeftUpTo tr₂ tr₁ start₁ →
    tr₂.topCol < tr₁.topCol := by
  classical
  intro C step C₂ D₁ start₁ htr₁ tr₁ R₁ D₂ start₂ htr₂ tr₂
    hmove hD₂D₁ hD₁D₂ hrows hleft
  have htarget : start₁ ≤ start₂ := by
    simpa [C, step, C₂, start₁, start₂] using
      reverseKrsStep_next_same_upper_start_row_le T h hprev hsame
  exact
    ReverseRowInsertionTrace.topCol_lt_of_movingAt_le_of_rows_equiv_of_strictlyLeftUpTo
      tr₂ tr₁ htarget hmove hD₂D₁ hD₁D₂ hrows hleft

theorem reverseKrsStep_next_lower_le_of_same_upper_current_nonTop_of_second_topCol_lt
    {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hcurrent_nonTop : (maxRecordingCorner T h).cell.1 ≠ 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1)
    (htop_lt :
      ∀ hsecond_nonTop :
          (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1 ≠ 0,
        let C := maxRecordingCorner T h
        let step := reverseKrsStep T h
        let C₂ := maxRecordingCorner step.previous hprev
        let D₁ := deleteCorner T.P C.cell C.removable
        let start₁ := C.cell.1 - 1
        let htr₁ : ∃ tr : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value,
            tr.RespectsLowerCap C.cell.2 := by
          simpa [D₁, start₁, C] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              T.P C.cell C.removable hcurrent_nonTop
        let tr₁ := Classical.choose htr₁
        let R₁ := reverseRowInsert T.P C.cell C.removable
        let D₂ := deleteCorner R₁.tableau C₂.cell C₂.removable
        let start₂ := C₂.cell.1 - 1
        let htr₂ : ∃ tr : ReverseRowInsertionTrace n D₂.tableau start₂ D₂.value,
            tr.RespectsLowerCap C₂.cell.2 := by
          simpa [D₂, start₂] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              R₁.tableau C₂.cell C₂.removable hsecond_nonTop
        let tr₂ := Classical.choose htr₂
        tr₂.topCol < tr₁.topCol) :
    (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.2 ≤
      (reverseKrsStep T h).letter.2 := by
  classical
  let C := maxRecordingCorner T h
  let step := reverseKrsStep T h
  let C₂ := maxRecordingCorner step.previous hprev
  let R₁ := reverseRowInsert T.P C.cell C.removable
  have hcorner_lt : C₂.cell.2 < C.cell.2 := by
    simpa [step, C, C₂] using
      reverseKrsStep_next_same_upper_corner_col_lt T h hprev hsame
  unfold reverseKrsStep
  simp only
  change (reverseRowInsert R₁.tableau C₂.cell C₂.removable).value ≤ R₁.value
  by_cases hsecond_top : C₂.cell.1 = 0
  · rw [Fin.le_def]
    let D₁ := deleteCorner T.P C.cell C.removable
    let start₁ := C.cell.1 - 1
    let htr₁ : ∃ tr : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value,
        tr.RespectsLowerCap C.cell.2 := by
      simpa [D₁, start₁, C] using
        exists_reverseRowInsertionTrace_afterDelete_with_respects
          T.P C.cell C.removable hcurrent_nonTop
    let tr₁ : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value :=
      Classical.choose htr₁
    have hval₁ : R₁.value = tr₁.result.2 := by
      simpa [R₁, D₁, start₁, htr₁, tr₁, C] using
        reverseRowInsert_value_eq_trace_result_of_not_top
          T.P C.cell C.removable hcurrent_nonTop
    have hC_le_top : C.cell.2 ≤ tr₁.topCol := by
      exact ReverseRowInsertionTrace.topCol_ge_cap_of_respectsLowerCap
        (Classical.choose_spec htr₁)
    have hC₂_lt_top : C₂.cell.2 < tr₁.topCol :=
      lt_of_lt_of_le hcorner_lt hC_le_top
    have htop_value :
        R₁.tableau.T 0 C₂.cell.2 ≤ R₁.value.val := by
      rw [hval₁]
      have hentry :
          R₁.tableau.T 0 C₂.cell.2 = D₁.tableau.T 0 C₂.cell.2 := by
        change (reverseRowInsert T.P C.cell C.removable).tableau.T 0 C₂.cell.2 =
          D₁.tableau.T 0 C₂.cell.2
        unfold reverseRowInsert
        rw [dif_neg hcurrent_nonTop]
        have htrace :
            tr₁.result.1.T 0 C₂.cell.2 = D₁.tableau.T 0 C₂.cell.2 :=
          tr₁.result_tableau_top_entry_eq_of_col_lt_topCol hC₂_lt_top
        simpa [D₁, start₁, htr₁, tr₁] using htrace
      rw [hentry]
      exact tr₁.top_row_entry_le_result_value_of_col_le_topCol
        (le_of_lt hC₂_lt_top)
    have htop_delete :
        (reverseRowInsert R₁.tableau C₂.cell C₂.removable).value.val =
          R₁.tableau.T 0 C₂.cell.2 := by
      simp [reverseRowInsert, hsecond_top, deleteCorner]
    rw [htop_delete]
    exact htop_value
  · exact
      reverseRowInsert_value_le_after_left_corner_of_current_nonTop_of_topCol_lt
        T.P C.removable (by simpa [C] using hcurrent_nonTop) C₂.removable
        hsecond_top (by
          simpa [C, step, C₂] using htop_lt hsecond_top)

theorem reverseKrsStep_next_lower_le_of_same_upper_current_nonTop_of_traceColumnInvariant
    {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hcurrent_nonTop : (maxRecordingCorner T h).cell.1 ≠ 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1)
    (htrace :
      ∀ hsecond_nonTop :
          (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1 ≠ 0,
        let C := maxRecordingCorner T h
        let step := reverseKrsStep T h
        let C₂ := maxRecordingCorner step.previous hprev
        let D₁ := deleteCorner T.P C.cell C.removable
        let start₁ := C.cell.1 - 1
        let htr₁ : ∃ tr : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value,
            tr.RespectsLowerCap C.cell.2 := by
          simpa [D₁, start₁, C] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              T.P C.cell C.removable hcurrent_nonTop
        let tr₁ := Classical.choose htr₁
        let R₁ := reverseRowInsert T.P C.cell C.removable
        let D₂ := deleteCorner R₁.tableau C₂.cell C₂.removable
        let start₂ := C₂.cell.1 - 1
        let htr₂ : ∃ tr : ReverseRowInsertionTrace n D₂.tableau start₂ D₂.value,
            tr.RespectsLowerCap C₂.cell.2 := by
          simpa [D₂, start₂] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              R₁.tableau C₂.cell C₂.removable hsecond_nonTop
        let tr₂ := Classical.choose htr₂
        tr₂.movingAt start₁ ≤ D₁.value ∧
        (∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₂.shape → (i, j) ∈ D₁.shape) ∧
        (∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₁.shape → (i, j) ∈ D₂.shape) ∧
        (∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₂.shape → (i, j) ∈ D₁.shape →
          D₁.tableau.T i j = (tr₂.tableauAt start₁).T i j) ∧
        ReverseRowInsertionTrace.StrictlyLeftUpTo tr₂ tr₁ start₁) :
    (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.2 ≤
      (reverseKrsStep T h).letter.2 := by
  classical
  exact
    reverseKrsStep_next_lower_le_of_same_upper_current_nonTop_of_second_topCol_lt
      T h hprev hcurrent_nonTop hsame (by
        intro hsecond_nonTop
        let C := maxRecordingCorner T h
        let step := reverseKrsStep T h
        let C₂ := maxRecordingCorner step.previous hprev
        let D₁ := deleteCorner T.P C.cell C.removable
        let start₁ := C.cell.1 - 1
        let htr₁ : ∃ tr : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value,
            tr.RespectsLowerCap C.cell.2 := by
          simpa [D₁, start₁, C] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              T.P C.cell C.removable hcurrent_nonTop
        let tr₁ := Classical.choose htr₁
        let R₁ := reverseRowInsert T.P C.cell C.removable
        let D₂ := deleteCorner R₁.tableau C₂.cell C₂.removable
        let start₂ := C₂.cell.1 - 1
        let htr₂ : ∃ tr : ReverseRowInsertionTrace n D₂.tableau start₂ D₂.value,
            tr.RespectsLowerCap C₂.cell.2 := by
          simpa [D₂, start₂] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              R₁.tableau C₂.cell C₂.removable hsecond_nonTop
        let tr₂ := Classical.choose htr₂
        have hdata :
            tr₂.movingAt start₁ ≤ D₁.value ∧
            (∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₂.shape → (i, j) ∈ D₁.shape) ∧
            (∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₁.shape → (i, j) ∈ D₂.shape) ∧
            (∀ {i j : ℕ}, i ≤ start₁ → (i, j) ∈ D₂.shape → (i, j) ∈ D₁.shape →
              D₁.tableau.T i j = (tr₂.tableauAt start₁).T i j) ∧
            ReverseRowInsertionTrace.StrictlyLeftUpTo tr₂ tr₁ start₁ := by
          simpa [C, step, C₂, D₁, start₁, htr₁, tr₁, R₁, D₂, start₂, htr₂, tr₂]
            using htrace hsecond_nonTop
        rcases hdata with ⟨hmove, hD₂D₁, hD₁D₂, hrows, hleft⟩
        exact
          reverseKrsStep_second_topCol_lt_of_same_upper_traceColumnInvariant
            T h hprev hcurrent_nonTop hsecond_nonTop hsame
            hmove hD₂D₁ hD₁D₂ hrows hleft)

theorem reverseKrsStep_next_lower_le_of_same_upper_current_nonTop_of_strictlyLeftUpTo
    {m n : ℕ}
    (T : TableauPair m n) (h : T.shape.card ≠ 0)
    (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0)
    (hcurrent_nonTop : (maxRecordingCorner T h).cell.1 ≠ 0)
    (hsame :
      (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
        (reverseKrsStep T h).letter.1)
    (hleft :
      ∀ hsecond_nonTop :
          (maxRecordingCorner (reverseKrsStep T h).previous hprev).cell.1 ≠ 0,
        let C := maxRecordingCorner T h
        let step := reverseKrsStep T h
        let C₂ := maxRecordingCorner step.previous hprev
        let D₁ := deleteCorner T.P C.cell C.removable
        let start₁ := C.cell.1 - 1
        let htr₁ : ∃ tr : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value,
            tr.RespectsLowerCap C.cell.2 := by
          simpa [D₁, start₁, C] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              T.P C.cell C.removable hcurrent_nonTop
        let tr₁ := Classical.choose htr₁
        let R₁ := reverseRowInsert T.P C.cell C.removable
        let D₂ := deleteCorner R₁.tableau C₂.cell C₂.removable
        let start₂ := C₂.cell.1 - 1
        let htr₂ : ∃ tr : ReverseRowInsertionTrace n D₂.tableau start₂ D₂.value,
            tr.RespectsLowerCap C₂.cell.2 := by
          simpa [D₂, start₂] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              R₁.tableau C₂.cell C₂.removable hsecond_nonTop
        let tr₂ := Classical.choose htr₂
        ReverseRowInsertionTrace.StrictlyLeftUpTo tr₂ tr₁ start₁) :
    (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.2 ≤
      (reverseKrsStep T h).letter.2 := by
  classical
  exact
    reverseKrsStep_next_lower_le_of_same_upper_current_nonTop_of_second_topCol_lt
      T h hprev hcurrent_nonTop hsame (by
        intro hsecond_nonTop
        let C := maxRecordingCorner T h
        let step := reverseKrsStep T h
        let C₂ := maxRecordingCorner step.previous hprev
        let D₁ := deleteCorner T.P C.cell C.removable
        let start₁ := C.cell.1 - 1
        let htr₁ : ∃ tr : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value,
            tr.RespectsLowerCap C.cell.2 := by
          simpa [D₁, start₁, C] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              T.P C.cell C.removable hcurrent_nonTop
        let tr₁ := Classical.choose htr₁
        let R₁ := reverseRowInsert T.P C.cell C.removable
        let D₂ := deleteCorner R₁.tableau C₂.cell C₂.removable
        let start₂ := C₂.cell.1 - 1
        let htr₂ : ∃ tr : ReverseRowInsertionTrace n D₂.tableau start₂ D₂.value,
            tr.RespectsLowerCap C₂.cell.2 := by
          simpa [D₂, start₂] using
            exists_reverseRowInsertionTrace_afterDelete_with_respects
              R₁.tableau C₂.cell C₂.removable hsecond_nonTop
        let tr₂ := Classical.choose htr₂
        have hleft' : ReverseRowInsertionTrace.StrictlyLeftUpTo tr₂ tr₁ start₁ := by
          intro r hr
          have h := (hleft hsecond_nonTop) hr
          simpa [C, step, C₂, D₁, start₁, htr₁, tr₁, R₁, D₂, start₂, htr₂, tr₂]
            using h
        have htop : tr₂.topCol < tr₁.topCol := by
          exact ReverseRowInsertionTrace.topCol_lt_of_strictlyLeftUpTo tr₂ tr₁ hleft'
        simpa [C, step, C₂, D₁, start₁, htr₁, tr₁, R₁, D₂, start₂, htr₂, tr₂]
          using htop)

/-- Reverse KRS list extraction with explicit fuel. The fuel will be `T.shape.card`; the
`card_previous` field in `reverseKrsStep` is the invariant used later to prove this extracts
all and only the cells. -/
noncomputable def reverseKrsListAux {m n : ℕ} :
    ℕ → TableauPair m n → List (Fin m × Fin n)
  | 0, _ => []
  | fuel + 1, T =>
      if h : T.shape.card = 0 then
        []
      else
        let step := reverseKrsStep T h
        reverseKrsListAux fuel step.previous ++ [step.letter]

/-- If all recording entries in the current tableau are bounded above by `a`, then every
upper letter extracted by reverse KRS with the given fuel is also bounded above by `a`. -/
theorem reverseKrsListAux_upper_le_of_Q_le {m n : ℕ}
    (fuel : ℕ) (T : TableauPair m n) (a : Fin m)
    (hQ : ∀ {c : ℕ × ℕ}, c ∈ T.shape → T.Q.T c.1 c.2 ≤ a.val) :
    ∀ x ∈ reverseKrsListAux fuel T, x.1 ≤ a := by
  induction fuel generalizing T with
  | zero =>
      intro x hx
      simp [reverseKrsListAux] at hx
  | succ fuel ih =>
      intro x hx
      unfold reverseKrsListAux at hx
      by_cases h : T.shape.card = 0
      · simp [h] at hx
      · simp only [h, ↓reduceDIte, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
        rcases hx with hxprev | hxlast
        · let step := reverseKrsStep T h
          have hQprev :
              ∀ {c : ℕ × ℕ}, c ∈ step.previous.shape →
                step.previous.Q.T c.1 c.2 ≤ a.val := by
            intro c hc
            calc
              step.previous.Q.T c.1 c.2
                  ≤ step.letter.1.val := by
                    simpa [step] using
                      reverseKrsStep_previous_Q_le_letter T h hc
              _ ≤ a.val := by
                    have hcorner :
                        (maxRecordingCorner T h).cell ∈ T.shape :=
                      (maxRecordingCorner T h).cell_mem
                    rw [show step.letter.1.val =
                        T.Q.T (maxRecordingCorner T h).cell.1
                          (maxRecordingCorner T h).cell.2 by
                        simpa [step] using reverseKrsStep_letter_upper_eq_corner T h]
                    exact hQ hcorner
          exact Fin.le_def.mpr (ih step.previous hQprev x hxprev)
        · have hx_eq : x = (reverseKrsStep T h).letter := by
            simpa using hxlast
          subst x
          rw [Fin.le_def]
          have hcorner :
              (maxRecordingCorner T h).cell ∈ T.shape :=
            (maxRecordingCorner T h).cell_mem
          rw [reverseKrsStep_letter_upper_eq_corner]
          exact hQ hcorner

theorem biwordLetter_toLex_le_of_upper_le_of_lower_le_eq {m n : ℕ}
    {x y : Fin m × Fin n}
    (hupper : x.1 ≤ y.1)
    (hlower : x.1 = y.1 → x.2 ≤ y.2) :
    toLex x ≤ toLex y := by
  exact Prod.Lex.toLex_le_toLex'.mpr ⟨hupper, hlower⟩

theorem pairwise_append_singleton_of_pairwise_of_forall {α : Type*}
    {r : α → α → Prop} {l : List α} {y : α}
    (hl : l.Pairwise r) (hy : ∀ x ∈ l, r x y) :
    (l ++ [y]).Pairwise r := by
  rw [List.pairwise_append]
  exact ⟨hl, by simp, by
    intro x hx z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    subst z
    exact hy x hx⟩

/-- The recursive sorting skeleton for reverse KRS.

All list-level and upper-letter work is handled here, parameterized by the
same-upper lower-letter comparison for the current reverse step. -/
theorem reverseKrsListAux_sorted_of_lower_bound {m n : ℕ}
    (hlower :
      ∀ (fuel : ℕ) (T : TableauPair m n) (h : T.shape.card ≠ 0)
        (x : Fin m × Fin n),
        x ∈ reverseKrsListAux fuel (reverseKrsStep T h).previous →
        x.1 = (reverseKrsStep T h).letter.1 →
        x.2 ≤ (reverseKrsStep T h).letter.2) :
    ∀ (fuel : ℕ) (T : TableauPair m n),
      (reverseKrsListAux fuel T).Pairwise (fun x y => toLex x ≤ toLex y) := by
  intro fuel
  induction fuel with
  | zero =>
      intro T
      simp [reverseKrsListAux]
  | succ fuel ih =>
      intro T
      unfold reverseKrsListAux
      by_cases h : T.shape.card = 0
      · simp [h]
      · simp only [h, ↓reduceDIte]
        let step := reverseKrsStep T h
        apply pairwise_append_singleton_of_pairwise_of_forall
        · exact ih step.previous
        · intro x hx
          have hupper : x.1 ≤ step.letter.1 := by
            apply reverseKrsListAux_upper_le_of_Q_le fuel step.previous step.letter.1
            · intro c hc
              simpa [step] using reverseKrsStep_previous_Q_le_letter T h hc
            · exact hx
          apply biwordLetter_toLex_le_of_upper_le_of_lower_le_eq hupper
          intro hsame
          exact hlower fuel T h x (by simpa [step] using hx) (by simpa [step] using hsame)

/-- A multi-step same-upper lower-letter comparison follows from the corresponding
one-step comparison between consecutive reverse KRS steps. -/
theorem reverseKrsListAux_lower_le_of_one_step {m n : ℕ}
    (hone :
      ∀ (T : TableauPair m n) (h : T.shape.card ≠ 0)
        (hprev : (reverseKrsStep T h).previous.shape.card ≠ 0),
        (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.1 =
          (reverseKrsStep T h).letter.1 →
        (reverseKrsStep (reverseKrsStep T h).previous hprev).letter.2 ≤
          (reverseKrsStep T h).letter.2) :
    ∀ (fuel : ℕ) (T : TableauPair m n) (h : T.shape.card ≠ 0)
      (x : Fin m × Fin n),
      x ∈ reverseKrsListAux fuel (reverseKrsStep T h).previous →
      x.1 = (reverseKrsStep T h).letter.1 →
      x.2 ≤ (reverseKrsStep T h).letter.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro T h x hx hsame
      simp [reverseKrsListAux] at hx
  | succ fuel ih =>
      intro T h x hx hsame
      let step := reverseKrsStep T h
      change x ∈ reverseKrsListAux (fuel + 1) step.previous at hx
      unfold reverseKrsListAux at hx
      by_cases hprev : step.previous.shape.card = 0
      · simp [hprev] at hx
      · simp only [hprev, ↓reduceDIte, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
        let step₂ := reverseKrsStep step.previous hprev
        rcases hx with hxprev | hxlast
        · have hupper_x_le_step₂ : x.1 ≤ step₂.letter.1 := by
            apply reverseKrsListAux_upper_le_of_Q_le fuel step₂.previous step₂.letter.1
            · intro c hc
              simpa [step₂] using
                reverseKrsStep_previous_Q_le_letter step.previous hprev hc
            · exact hxprev
          have hstep₂_upper_le_step : step₂.letter.1 ≤ step.letter.1 := by
            have hcorner :
                (maxRecordingCorner step.previous hprev).cell ∈ step.previous.shape :=
              (maxRecordingCorner step.previous hprev).cell_mem
            rw [Fin.le_def, show step₂.letter.1.val =
                step.previous.Q.T (maxRecordingCorner step.previous hprev).cell.1
                  (maxRecordingCorner step.previous hprev).cell.2 by
              simpa [step₂] using reverseKrsStep_letter_upper_eq_corner step.previous hprev]
            simpa [step] using reverseKrsStep_previous_Q_le_letter T h hcorner
          have hstep₂_same : step₂.letter.1 = step.letter.1 :=
            le_antisymm hstep₂_upper_le_step (by simpa [hsame] using hupper_x_le_step₂)
          have hx_same_step₂ : x.1 = step₂.letter.1 := by
            exact hsame.trans hstep₂_same.symm
          exact le_trans
            (ih step.previous hprev x (by simpa [step₂] using hxprev)
              (by simpa [step₂] using hx_same_step₂))
            (hone T h hprev (by simpa [step, step₂] using hstep₂_same))
        · have hx_eq : x = step₂.letter := by
            simpa [step₂] using hxlast
          subst x
          exact hone T h hprev (by simpa [step, step₂] using hsame)

/-- The raw biword recovered from a tableau pair by reverse KRS. -/
noncomputable def reverseKrsList {m n : ℕ}
    (T : TableauPair m n) : List (Fin m × Fin n) :=
  reverseKrsListAux T.shape.card T

/-- Reverse KRS returns a row-column lexicographically sorted biword. This is the ordering
part of the reverse KRS proof, separated from the executable list extraction. -/
theorem reverseKrsList_sorted {m n : ℕ}
    (T : TableauPair m n) :
    (reverseKrsList T).Pairwise (fun x y => toLex x ≤ toLex y) := by
  classical
  unfold reverseKrsList
  apply reverseKrsListAux_sorted_of_lower_bound
  apply reverseKrsListAux_lower_le_of_one_step
  intro T h hprev hsame
  by_cases htop : (maxRecordingCorner T h).cell.1 = 0
  · exact reverseKrsStep_next_lower_le_of_same_upper_current_top
      T h hprev htop hsame
  · exact
      reverseKrsStep_next_lower_le_of_same_upper_current_nonTop_of_second_topCol_lt
        T h hprev htop hsame (by
          intro hsecond_nonTop
          let C := maxRecordingCorner T h
          let step := reverseKrsStep T h
          let C₂ := maxRecordingCorner step.previous hprev
          let D₁ := deleteCorner T.P C.cell C.removable
          let start₁ := C.cell.1 - 1
          let htr₁ : ∃ tr : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value,
              tr.RespectsLowerCap C.cell.2 := by
            simpa [D₁, start₁, C] using
              exists_reverseRowInsertionTrace_afterDelete_with_respects
                T.P C.cell C.removable htop
          let tr₁ := Classical.choose htr₁
          let R₁ := reverseRowInsert T.P C.cell C.removable
          let D₂ := deleteCorner R₁.tableau C₂.cell C₂.removable
          let start₂ := C₂.cell.1 - 1
          let htr₂ : ∃ tr : ReverseRowInsertionTrace n D₂.tableau start₂ D₂.value,
              tr.RespectsLowerCap C₂.cell.2 := by
            simpa [D₂, start₂] using
              exists_reverseRowInsertionTrace_afterDelete_with_respects
                R₁.tableau C₂.cell C₂.removable hsecond_nonTop
          let tr₂ := Classical.choose htr₂
          have hcol_lt : C₂.cell.2 < C.cell.2 := by
            simpa [C, step, C₂] using
              reverseKrsStep_next_same_upper_corner_col_lt T h hprev hsame
          have hstrict :
              (let D₁ := deleteCorner T.P C.cell C.removable
               let start₁ := C.cell.1 - 1
               let htr₁ : ∃ tr : ReverseRowInsertionTrace n D₁.tableau start₁ D₁.value,
                   tr.RespectsLowerCap C.cell.2 := by
                 simpa [D₁, start₁] using
                   exists_reverseRowInsertionTrace_afterDelete_with_respects
                     T.P C.cell C.removable htop
               let tr₁ := Classical.choose htr₁
               let R₁ := reverseRowInsert T.P C.cell C.removable
               let D₂ := deleteCorner R₁.tableau C₂.cell C₂.removable
               let start₂ := C₂.cell.1 - 1
               let htr₂ : ∃ tr : ReverseRowInsertionTrace n D₂.tableau start₂ D₂.value,
                   tr.RespectsLowerCap C₂.cell.2 := by
                 simpa [D₂, start₂] using
                   exists_reverseRowInsertionTrace_afterDelete_with_respects
                     R₁.tableau C₂.cell C₂.removable hsecond_nonTop
               let tr₂ := Classical.choose htr₂
               tr₂.topCol < tr₁.topCol) := by
            simpa [C, step, C₂] using
              reverseRowInsert_second_topCol_le_first_topCol_nonTop_core
                T.P C.removable htop C₂.removable hsecond_nonTop hcol_lt
          simpa [C, step, C₂, D₁, start₁, htr₁, tr₁, R₁, D₂, start₂, htr₂, tr₂]
            using hstrict)

/-- KRS insertion sends a generalized permutation to a same-shape tableau pair. -/
noncomputable def krsTableauPair {m n : ℕ}
    (W : Biword m n) : TableauPair m n :=
  (krsForwardStateOfList W.1 W.2).toTableauPair

/-- Reverse KRS sends a same-shape tableau pair back to a generalized permutation. -/
noncomputable def reverseKrsBiword {m n : ℕ}
    (T : TableauPair m n) : Biword m n :=
  ⟨reverseKrsList T, reverseKrsList_sorted T⟩

/-- The shape size of the forward KRS state is the number of processed letters. -/
theorem krsForwardStateOfList_shape_card {m n : ℕ}
    (w : List (Fin m × Fin n))
    (hsorted : w.Pairwise (fun x y => toLex x ≤ toLex y)) :
    (krsForwardStateOfList w hsorted).shape.card = w.length := by
  exact KRSForwardRun.shape_card (krsForwardStateOfList_run w hsorted)

/-- Reverse KRS undoes KRS on biwords. -/
theorem reverse_krs_krs {m n : ℕ} :
    Function.LeftInverse
      (fun T : TableauPair m n => reverseKrsBiword T)
      (fun W : Biword m n => krsTableauPair W) := by
  classical
  intro W
  apply Subtype.ext
  change reverseKrsList (krsTableauPair W) = W.1
  -- Step 1 in the paper proof: the maximal/rightmost recording corner of the
  -- tableau produced by appending `z` is exactly the new row-insertion cell.
  have hmaxCorner :
      ∀ {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
        (hrun : KRSForwardRun w S) (z : Fin m × Fin n)
        (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y))
        (hrec : let R := rowInsert S.P z.2; RecordingAppendHyp S.Q z.1 R)
        (hnonempty : (krsForwardStep S z hrec).shape.card ≠ 0),
        (maxRecordingCorner ((krsForwardStep S z hrec).toTableauPair) hnonempty).cell =
          (rowInsert S.P z.2).newCell := by
    intro w S hrun z hsorted hrec hnonempty
    let R := rowInsert S.P z.2
    let S' := krsForwardStep S z hrec
    let C := maxRecordingCorner (S'.toTableauPair) hnonempty
    have hsource : KRSForwardRun.QEntriesFromPrefix (w := w) S :=
      KRSForwardRun.qEntriesFromPrefix hrun
    have hold_le : KRSForwardRun.OldQEntriesLeNext S z :=
      KRSForwardRun.oldQEntriesLeNext_of_entriesFromPrefix hsource z hsorted
    have hsame_left : KRSForwardRun.SameUpperCellsLeftOfNext S z :=
      KRSForwardRun.sameUpperCellsLeftOfNext_of_run hrun z hsorted
    have hnew_mem : R.newCell ∈ S'.toTableauPair.shape := by
      simpa [S', R, krsForwardStep, KRSForwardState.toTableauPair] using R.newCell_mem
    have hnew_Q : S'.toTableauPair.Q.T R.newCell.1 R.newCell.2 = z.1.val := by
      change (krsAppendRecording S.Q z.1 R hrec).T R.newCell.1 R.newCell.2 = z.1.val
      change
        RowAppendStepResult.appendEntry S.Q R.newCell z.1 R.newCell.1 R.newCell.2 =
          z.1.val
      rw [RowAppendStepResult.appendEntry_newCell]
    have hsplit : C.cell ∈ S.shape ∨ C.cell = R.newCell := by
      have hcell : C.cell ∈ R.shape := by
        simpa [C, S', R, krsForwardStep, KRSForwardState.toTableauPair] using C.cell_mem
      exact (R.shape_mem_iff C.cell).1 hcell
    rcases hsplit with hold | hnew
    · exfalso
      have hC_ne_new : C.cell ≠ R.newCell := by
        intro hC
        exact R.newCell_not_mem_old (by simpa [hC] using hold)
      have hC_Q_old :
          S'.toTableauPair.Q.T C.cell.1 C.cell.2 = S.Q.T C.cell.1 C.cell.2 := by
        change (krsAppendRecording S.Q z.1 R hrec).T C.cell.1 C.cell.2 =
          S.Q.T C.cell.1 C.cell.2
        change RowAppendStepResult.appendEntry S.Q R.newCell z.1 C.cell.1 C.cell.2 =
          S.Q.T C.cell.1 C.cell.2
        rw [RowAppendStepResult.appendEntry_ne _ _ _ hC_ne_new]
      have hC_le_z : S'.toTableauPair.Q.T C.cell.1 C.cell.2 ≤ z.1.val := by
        rw [hC_Q_old]
        exact hold_le hold
      have hz_le_C : z.1.val ≤ S'.toTableauPair.Q.T C.cell.1 C.cell.2 := by
        rw [← hnew_Q]
        exact C.max_entry hnew_mem
      have hC_eq_z : S'.toTableauPair.Q.T C.cell.1 C.cell.2 = z.1.val :=
        le_antisymm hC_le_z hz_le_C
      have hC_old_eq_z : S.Q.T C.cell.1 C.cell.2 = z.1.val := by
        rw [← hC_Q_old]
        exact hC_eq_z
      have hC_left : C.cell.2 < R.newCell.2 :=
        hsame_left hold hC_old_eq_z
      have hnew_right : R.newCell.2 ≤ C.cell.2 := by
        exact C.rightmost_of_same_entry hnew_mem (by
          rw [hnew_Q, hC_eq_z])
      exact (Nat.not_lt_of_ge hnew_right) hC_left
    · simpa [C, R] using hnew
  -- Step 2: reverse row insertion at the cell just created by row insertion
  -- recovers the previous insertion tableau and the inserted lower letter.
  have hrowInverse :
      ∀ {μ : YoungDiagram} (P : BoundedSSYT μ n) (x : Fin n),
        (reverseRowInsert (rowInsert P x).tableau
            (rowInsert P x).newCell (rowInsert P x).newCell_removable).shape = μ ∧
        HEq
          (reverseRowInsert (rowInsert P x).tableau
            (rowInsert P x).newCell (rowInsert P x).newCell_removable).tableau
          P ∧
        (reverseRowInsert (rowInsert P x).tableau
            (rowInsert P x).newCell (rowInsert P x).newCell_removable).value = x := by
    intro μ P x
    have htraceSpec : ReverseRowInsertInverseTraceSpec P x := by
      exact reverseRowInsert_inverse_traceSpec P x
    exact reverseRowInsert_inverse_of_traceSpec P x htraceSpec
  -- Step 3: combine the corner identification and row-insertion inverse into
  -- the one-step KRS inverse.
  have hstepInverse :
      ∀ {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
        (hrun : KRSForwardRun w S) (z : Fin m × Fin n)
        (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y))
        (hrec : let R := rowInsert S.P z.2; RecordingAppendHyp S.Q z.1 R)
        (hnonempty : (krsForwardStep S z hrec).shape.card ≠ 0),
        (reverseKrsStep ((krsForwardStep S z hrec).toTableauPair) hnonempty).letter = z ∧
        (reverseKrsStep ((krsForwardStep S z hrec).toTableauPair) hnonempty).previous =
          S.toTableauPair := by
    intro w S hrun z hsorted hrec hnonempty
    let R := rowInsert S.P z.2
    let S' := krsForwardStep S z hrec
    let T' := S'.toTableauPair
    let C := maxRecordingCorner T' hnonempty
    let step := reverseKrsStep T' hnonempty
    have hcorner : C.cell = R.newCell := by
      simpa [C, T', S', R] using hmaxCorner hrun z hsorted hrec hnonempty
    have hrow :
        (reverseRowInsert R.tableau R.newCell R.newCell_removable).shape = S.shape ∧
        HEq
          (reverseRowInsert R.tableau R.newCell R.newCell_removable).tableau
          S.P ∧
        (reverseRowInsert R.tableau R.newCell R.newCell_removable).value = z.2 := by
      simpa [R] using hrowInverse S.P z.2
    have hQ :
        let Q' := krsAppendRecording S.Q z.1 R hrec
        let D := deleteCorner Q' R.newCell R.newCell_removable
        D.shape = S.shape ∧ HEq D.tableau S.Q ∧ D.value = z.1 := by
      simpa [R] using krsAppendRecording_deleteCorner_inverse S.Q z.1 R hrec
    constructor
    · apply Prod.ext
      · apply Fin.ext
        calc
          step.letter.1.val =
              T'.Q.T C.cell.1 C.cell.2 := by
                simpa [step, C] using reverseKrsStep_letter_upper_eq_corner T' hnonempty
          _ = T'.Q.T R.newCell.1 R.newCell.2 := by rw [hcorner]
          _ = z.1.val := by
                simpa [T', S', R, KRSForwardState.toTableauPair, krsForwardStep] using
                  krsAppendRecording_entry_newCell S.Q z.1 R hrec
      · calc
          step.letter.2 =
              (reverseRowInsert T'.P C.cell C.removable).value := by
                simpa [step, C] using reverseKrsStep_letter_lower_eq_reverseRowInsert T' hnonempty
          _ = (reverseRowInsert R.tableau R.newCell R.newCell_removable).value := by
                exact reverseRowInsert_value_eq_of_cell_eq R.tableau C.removable
                  R.newCell_removable hcorner
          _ = z.2 := hrow.2.2
    · have hshape : step.previous.shape = S.shape := by
        calc
          step.previous.shape =
              (reverseRowInsert T'.P C.cell C.removable).shape := by
                unfold step reverseKrsStep
                rfl
          _ = (reverseRowInsert R.tableau R.newCell R.newCell_removable).shape := by
                exact reverseRowInsert_shape_eq_of_cell_eq R.tableau C.removable
                  R.newCell_removable hcorner
          _ = S.shape := hrow.1
      have hP : HEq step.previous.P S.P := by
        have hstepP :
            HEq step.previous.P
              (reverseRowInsert T'.P C.cell C.removable).tableau := by
          unfold step reverseKrsStep
          exact HEq.rfl
        have hsame :
            HEq (reverseRowInsert T'.P C.cell C.removable).tableau
              (reverseRowInsert R.tableau R.newCell R.newCell_removable).tableau := by
          exact reverseRowInsert_tableau_heq_of_cell_eq R.tableau C.removable
            R.newCell_removable hcorner
        exact hstepP.trans (hsame.trans hrow.2.1)
      have hQprev : HEq step.previous.Q S.Q := by
        let Q' := krsAppendRecording S.Q z.1 R hrec
        let D := deleteCorner Q' R.newCell R.newCell_removable
        have hQtableau : HEq D.tableau S.Q := hQ.2.1
        have hcast :
            HEq step.previous.Q D.tableau := by
          unfold step reverseKrsStep
          simp only
          let QdelC := deleteCorner T'.Q C.cell C.removable
          let PinvC := reverseRowInsert T'.P C.cell C.removable
          have hshapeC : QdelC.shape = PinvC.shape := by
            have hdel :
                QdelC.shape = (deleteCorner T'.P C.cell C.removable).shape := rfl
            exact hdel.trans (reverseRowInsert_shape_eq_deleteCorner T'.P C.cell C.removable).symm
          have hdel_heq : HEq QdelC.tableau D.tableau := by
            simpa [QdelC, T', S', R, Q', D, KRSForwardState.toTableauPair,
              krsForwardStep] using
              deleteCorner_tableau_heq_of_cell_eq Q' C.removable
                R.newCell_removable hcorner
          have hcastC : HEq (castBoundedSSYT hshapeC QdelC.tableau) QdelC.tableau :=
            castBoundedSSYT_heq hshapeC QdelC.tableau
          exact hcastC.trans hdel_heq
        exact hcast.trans hQtableau
      exact TableauPair.ext_heq hshape hP hQprev
  -- Step 4: right-to-left induction on the sorted biword.  In the `snoc` case,
  -- `hstepInverse` unfolds one reverse KRS step and the induction hypothesis
  -- rewrites the prefix.
  have hlistInverse :
      ∀ (w : List (Fin m × Fin n))
        (hsorted : w.Pairwise (fun x y => toLex x ≤ toLex y)),
        reverseKrsList
          ((krsForwardStateOfList w hsorted).toTableauPair) = w := by
    intro w hsorted
    have hrun :
        KRSForwardRun w
          (krsForwardStateOfList w hsorted) :=
      krsForwardStateOfList_run w hsorted
    have hrunInverse :
        ∀ {u : List (Fin m × Fin n)} {S : KRSForwardState m n},
          KRSForwardRun u S → reverseKrsList S.toTableauPair = u := by
      intro u S hrun
      induction hrun with
      | nil =>
          have hcard : (⊥ : YoungDiagram).card = 0 := by
            simp [YoungDiagram.card]
          change reverseKrsListAux (⊥ : YoungDiagram).card
            { shape := (⊥ : YoungDiagram), P := emptyBoundedSSYT n,
              Q := emptyBoundedSSYT m } = []
          rw [hcard]
          rfl
      | snoc z hrun hsorted hrec hsame_next ih =>
          rename_i u₀ S₀
          let S' := krsForwardStep S₀ z hrec
          have hnonempty : S'.shape.card ≠ 0 := by
            simp [S', krsForwardStep, rowInsert_adds_one_box]
          have hstep := hstepInverse hrun z hsorted hrec hnonempty
          have hcard :
              S'.toTableauPair.shape.card =
                (reverseKrsStep S'.toTableauPair hnonempty).previous.shape.card + 1 := by
            exact (reverseKrsStep S'.toTableauPair hnonempty).card_previous.symm
          calc
            reverseKrsList S'.toTableauPair =
                reverseKrsListAux S'.toTableauPair.shape.card S'.toTableauPair := rfl
            _ = reverseKrsListAux
                  (reverseKrsStep S'.toTableauPair hnonempty).previous.shape.card
                  (reverseKrsStep S'.toTableauPair hnonempty).previous ++
                [(reverseKrsStep S'.toTableauPair hnonempty).letter] := by
                  have hcells_nonempty : S'.toTableauPair.shape.cells ≠ ∅ := by
                    intro hcells
                    exact hnonempty (by
                      simpa [KRSForwardState.toTableauPair, YoungDiagram.card] using
                        congrArg Finset.card hcells)
                  rw [hcard]
                  simp [reverseKrsListAux, hcells_nonempty]
            _ = reverseKrsList S₀.toTableauPair ++ [z] := by
                  rw [hstep.1, hstep.2]
                  rfl
            _ = u₀ ++ [z] := by
                  rw [ih]
    exact hrunInverse hrun
  simpa [krsTableauPair] using hlistInverse W.1 W.2

/-- Trace-level right inverse for the non-top branch of reverse row insertion.

Starting from the tableau obtained after deleting a non-top corner and following an
upward reverse-bumping trace, ordinary row insertion from the trace output follows
the same path back down and appends the deleted value at the original corner. -/
theorem rowInsert_reverseTrace_deleteCorner_inverse {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c)
    (htop : c.1 ≠ 0)
    (tr : let D := deleteCorner T c hc
      ReverseRowInsertionTrace N D.tableau (c.1 - 1) D.value) :
    let out := tr.result
    let R := rowInsert out.1 out.2
    R.shape = μ ∧ HEq R.tableau T ∧ R.newCell = c := by
  classical
  let D := deleteCorner T c hc
  let A := deleteCorner_rowAppendStepResult T c hc
  let contRaw : RowInsertionTrace N D.tableau c.1 D.value := RowInsertionTrace.done A
  have hroweq : c.1 - 1 + 1 = c.1 := by
    omega
  let cont : RowInsertionTrace N D.tableau (c.1 - 1 + 1) D.value :=
    RowInsertionTrace.castRow hroweq contRaw
  rcases ReverseRowInsertionTrace.rowInsertionTrace_with_continuation tr cont with
    ⟨ftr, hftr⟩
  let chosen : RowInsertionTrace N tr.result.1 0 tr.result.2 :=
    rowInsertionTrace tr.result.1 tr.result.2
  have hchosen : chosen.result = ftr.result :=
    RowInsertionTrace.result_eq_of_same chosen ftr
  have hchosen_A : chosen.result = A.result := by
    calc
      chosen.result = ftr.result := hchosen
      _ = cont.result := hftr
      _ = contRaw.result := RowInsertionTrace.castRow_result_eq hroweq contRaw
      _ = A.result := rfl
  have hA := deleteCorner_rowAppendStepResult_inverse T c hc
  have hR : rowInsert tr.result.1 tr.result.2 = A.result := by
    simpa [rowInsert, rowInsertFromTrace, chosen] using hchosen_A
  constructor
  · calc
      (rowInsert tr.result.1 tr.result.2).shape = A.result.shape := by rw [hR]
      _ = μ := hA.1
  constructor
  · have htableau : HEq A.result.tableau T := hA.2.1
    rw [hR]
    exact htableau
  · calc
      (rowInsert tr.result.1 tr.result.2).newCell = A.result.newCell := by rw [hR]
      _ = c := hA.2.2

/-- Row insertion is the right inverse of true reverse row insertion at a removable
corner: after deleting/reverse-bumping from `c`, inserting the ejected value restores
the original tableau and creates exactly `c`.

This is the row-level API needed by the reverse-KRS/right-inverse proof. -/
theorem rowInsert_reverseRowInsert_inverse {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (c : ℕ × ℕ) (hc : IsRemovableCorner μ c) :
    let Pinv := reverseRowInsert T c hc
    let R := rowInsert Pinv.tableau Pinv.value
    R.shape = μ ∧ HEq R.tableau T ∧ R.newCell = c := by
  classical
  by_cases htop : c.1 = 0
  · unfold reverseRowInsert
    rw [dif_pos htop]
    let D := deleteCorner T c hc
    generalize htr : rowInsertionTrace D.tableau D.value = tr
    cases tr with
    | bump B tail =>
        exfalso
        have hDrow : D.shape.rowLen 0 = c.2 := by
          simpa [D, htop] using D.new_shape_rowLen_at_removedCell
        have hcol_lt : B.col < c.2 := by
          have hlt := B.location.col_lt_rowLen
          simpa [D, hDrow] using hlt
        have hcellD : (0, B.col) ∈ D.shape := B.cell_mem
        have hcellμ : (0, B.col) ∈ μ := D.shape_subset_old hcellD
        have hc0 : (0, c.2) ∈ μ := by
          convert D.cell_mem_old using 1
          ext <;> simp [htop]
        have hentry_eq : D.tableau.T 0 B.col = T.T 0 B.col := by
          exact deleteCorner_tableau_entry T c hc hcellD
        have hval : D.value.val = T.T 0 c.2 := by
          simp [D, deleteCorner, htop]
        have hle : D.tableau.T 0 B.col ≤ D.value.val := by
          rw [hentry_eq, hval]
          exact T.T.row_weak hcol_lt hc0
        exact (not_lt_of_ge hle) B.entry_gt
    | done A =>
        let R := A.result
        have hDrow : D.shape.rowLen 0 = c.2 := by
          simpa [D, htop] using D.new_shape_rowLen_at_removedCell
        have hnew : R.newCell = c := by
          calc
            R.newCell = (0, D.shape.rowLen 0) := A.newCell_eq
            _ = c := by
              ext <;> simp [htop, hDrow]
        have hshape : R.shape = μ := by
          ext d
          calc
            d ∈ R.shape ↔ d ∈ D.shape ∨ d = R.newCell := R.shape_mem_iff d
            _ ↔ d ∈ D.shape ∨ d = c := by rw [hnew]
            _ ↔ d ∈ μ := (D.shape_mem_iff d).symm
        have htableau : HEq R.tableau T := by
          apply BoundedSSYT.heq_of_entry_eq hshape
          intro i j
          by_cases hcellR : (i, j) ∈ R.shape
          · rcases (R.shape_mem_iff (i, j)).1 hcellR with hcellD | hcellNew
            · calc
                R.tableau.T i j = D.tableau.T i j := A.unchanged_on_old_shape hcellD
                _ = T.T i j := deleteCorner_tableau_entry T c hc hcellD
            · have hi : i = c.1 := congrArg Prod.fst (by simpa [hnew] using hcellNew)
              have hj : j = c.2 := congrArg Prod.snd (by simpa [hnew] using hcellNew)
              subst i
              subst j
              calc
                R.tableau.T c.1 c.2 = R.tableau.T 0 (D.shape.rowLen 0) := by
                  rw [htop, hDrow]
                _ = D.value.val := A.inserted_entry
                _ = T.T c.1 c.2 := by
                  simp [D, deleteCorner]
          · have hcellμ_not : (i, j) ∉ μ := by
              intro hcellμ
              exact hcellR (by simpa [hshape] using hcellμ)
            calc
              R.tableau.T i j = 0 := R.tableau.T.zeros hcellR
              _ = T.T i j := (T.T.zeros hcellμ_not).symm
        refine ⟨?_, ?_, ?_⟩
        · simpa [rowInsert, rowInsertFromTrace, htr, RowInsertionTrace.result, D, R] using
            hshape
        · change HEq (rowInsertFromTrace D.tableau D.value
          (rowInsertionTrace D.tableau D.value)).tableau T
          rw [htr]
          simpa [rowInsertFromTrace, RowInsertionTrace.result, R] using htableau
        · simpa [rowInsert, rowInsertFromTrace, htr, RowInsertionTrace.result, D, R] using
            hnew
  · unfold reverseRowInsert
    rw [dif_neg htop]
    let D := deleteCorner T c hc
    let startRow := c.1 - 1
    have htr : ∃ tr : ReverseRowInsertionTrace N D.tableau startRow D.value,
        tr.RespectsLowerCap c.2 := by
      simpa [D, startRow] using
        exists_reverseRowInsertionTrace_afterDelete_with_respects T c hc htop
    let tr : ReverseRowInsertionTrace N D.tableau startRow D.value := Classical.choose htr
    have htrace_inverse :
        let out := tr.result
        let R := rowInsert out.1 out.2
        R.shape = μ ∧ HEq R.tableau T ∧ R.newCell = c := by
      simpa [D, startRow, tr] using
        rowInsert_reverseTrace_deleteCorner_inverse T c hc htop tr
    simpa [D, startRow, htr, tr] using htrace_inverse

/-- KRS undoes reverse KRS on same-shape tableau pairs. -/
theorem krs_reverse_krs {m n : ℕ} :
    Function.RightInverse
      (fun T : TableauPair m n => reverseKrsBiword T)
      (fun W : Biword m n => krsTableauPair W) := by
  classical
  intro T
  have hstepInverse :
      ∀ (T : TableauPair m n) (h : T.shape.card ≠ 0),
        let step := reverseKrsStep T h
        ∃ hrec,
          (krsForwardStep step.previous.toForwardState step.letter hrec).toTableauPair = T := by
    intro T h
    let C := maxRecordingCorner T h
    let step := reverseKrsStep T h
    let Pinv := reverseRowInsert T.P C.cell C.removable
    let Qdel := deleteCorner T.Q C.cell C.removable
    have hrowForward :
        let R := rowInsert step.previous.P step.letter.2
        R.shape = T.shape ∧ HEq R.tableau T.P ∧ R.newCell = C.cell := by
      simpa [step, C] using
        rowInsert_reverseRowInsert_inverse T.P C.cell C.removable
    have hQForward :
        let R := rowInsert step.previous.P step.letter.2
        ∃ hrec : RecordingAppendHyp step.previous.Q step.letter.1 R,
          HEq (krsAppendRecording step.previous.Q step.letter.1 R hrec) T.Q := by
      let R := rowInsert step.previous.P step.letter.2
      have hRshape : R.shape = T.shape := hrowForward.1
      have hRcell : R.newCell = C.cell := hrowForward.2.2
      have hrec : RecordingAppendHyp step.previous.Q step.letter.1 R := by
        refine
          { left_le := ?_
            above_lt := ?_ }
        · intro j hj hcell
          simpa [step] using
            reverseKrsStep_previous_Q_le_letter T h
              (c := (R.newCell.1, j)) hcell
        · intro i hi hcell
          have hcellC : (i, C.cell.2) ∈ step.previous.shape := by
            simpa [hRcell] using hcell
          have hiC : i < C.cell.1 := by
            simpa [hRcell] using hi
          calc
            step.previous.Q.T i R.newCell.2 =
                step.previous.Q.T i C.cell.2 := by rw [hRcell]
            _ = T.Q.T i C.cell.2 := by
                simpa [step] using
                  reverseKrsStep_previous_Q_entry T h hcellC
            _ < T.Q.T C.cell.1 C.cell.2 :=
                T.Q.T.col_strict hiC C.cell_mem
            _ = step.letter.1.val := by
                simpa [step, C] using
                  (reverseKrsStep_letter_upper_eq_corner T h).symm
      refine ⟨hrec, ?_⟩
      apply BoundedSSYT.heq_of_entry_eq hRshape
      intro i j
      by_cases hcellR : (i, j) ∈ R.shape
      · rcases (R.shape_mem_iff (i, j)).1 hcellR with hprev | hnew
        · calc
            (krsAppendRecording step.previous.Q step.letter.1 R hrec).T i j =
                step.previous.Q.T i j :=
                  krsAppendRecording_entry_old step.previous.Q step.letter.1 R hrec hprev
            _ = T.Q.T i j := by
                  simpa [step] using
                    reverseKrsStep_previous_Q_entry T h hprev
        · have hnew' : ((i, j) : ℕ × ℕ) = R.newCell := hnew
          have hi_eq : i = R.newCell.1 := congrArg Prod.fst hnew'
          have hj_eq : j = R.newCell.2 := congrArg Prod.snd hnew'
          subst i
          subst j
          calc
            (krsAppendRecording step.previous.Q step.letter.1 R hrec).T
                R.newCell.1 R.newCell.2 =
                step.letter.1.val :=
                  krsAppendRecording_entry_newCell step.previous.Q step.letter.1 R hrec
            _ = T.Q.T C.cell.1 C.cell.2 := by
                  simpa [step, C] using
                    (reverseKrsStep_letter_upper_eq_corner T h).symm
            _ = T.Q.T R.newCell.1 R.newCell.2 := by rw [hRcell]
      · have hcellT_not : (i, j) ∉ T.shape := by
          intro hcellT
          exact hcellR (by simpa [hRshape] using hcellT)
        calc
          (krsAppendRecording step.previous.Q step.letter.1 R hrec).T i j = 0 :=
            (krsAppendRecording step.previous.Q step.letter.1 R hrec).T.zeros hcellR
          _ = T.Q.T i j := (T.Q.T.zeros hcellT_not).symm
    rcases hQForward with ⟨hrec, hQ⟩
    refine ⟨hrec, ?_⟩
    let R := rowInsert step.previous.P step.letter.2
    have hshape : (krsForwardStep step.previous.toForwardState step.letter hrec).shape =
        T.shape := by
      simpa [step, R, krsForwardStep, TableauPair.toForwardState] using hrowForward.1
    have hP : HEq (krsForwardStep step.previous.toForwardState step.letter hrec).P T.P := by
      simpa [step, R, krsForwardStep, TableauPair.toForwardState] using hrowForward.2.1
    have hQ' : HEq (krsForwardStep step.previous.toForwardState step.letter hrec).Q T.Q := by
      simpa [step, R, krsForwardStep, TableauPair.toForwardState] using hQ
    exact TableauPair.ext_heq hshape hP hQ'
  have hrunRebuild :
      KRSForwardRun (reverseKrsList T) T.toForwardState := by
    -- Induct over `T.shape.card` / `reverseKrsListAux`, using `hstepInverse`
    -- to append the current reverse letter back to the previous tableau pair.
    have haux :
        ∀ k : ℕ, ∀ U : TableauPair m n, U.shape.card = k →
          KRSForwardRun (reverseKrsList U) U.toForwardState := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro U hk
          by_cases hzero : U.shape.card = 0
          · have hlist : reverseKrsList U = [] := by
              unfold reverseKrsList
              rw [hzero]
              rfl
            have hstate :
                U.toForwardState = KRSForwardState.empty m n := by
              cases U with
              | mk μ P Q =>
                  change μ.card = 0 at hzero
                  change
                    ({ shape := μ, P := P, Q := Q } :
                        KRSForwardState m n) =
                      KRSForwardState.empty m n
                  have hshape : μ = (⊥ : YoungDiagram) := by
                    apply le_antisymm
                    · intro c hc
                      exfalso
                      have hcells : μ.cells = ∅ := by
                        apply Finset.card_eq_zero.mp
                        simpa [YoungDiagram.card] using hzero
                      have hc' : c ∈ μ.cells := by
                        simpa [YoungDiagram.mem_cells] using hc
                      simp [hcells] at hc'
                    · exact bot_le
                  subst μ
                  have hP : P = emptyBoundedSSYT n := by
                    apply BoundedSSYT.ext
                    intro i j
                    calc
                      P.T i j = 0 := P.T.zeros (by simp)
                      _ = (emptyBoundedSSYT n).T i j := by
                        symm
                        exact (emptyBoundedSSYT n).T.zeros (by simp)
                  have hQ : Q = emptyBoundedSSYT m := by
                    apply BoundedSSYT.ext
                    intro i j
                    calc
                      Q.T i j = 0 := Q.T.zeros (by simp)
                      _ = (emptyBoundedSSYT m).T i j := by
                        symm
                        exact (emptyBoundedSSYT m).T.zeros (by simp)
                  simp [KRSForwardState.empty, hP, hQ]
            rw [hlist, hstate]
            exact KRSForwardRun.nil
          · have hprev_lt :
                (reverseKrsStep U hzero).previous.shape.card < k := by
              have hcard :
                  (reverseKrsStep U hzero).previous.shape.card + 1 =
                    U.shape.card :=
                (reverseKrsStep U hzero).card_previous
              omega
            have hprev :
                KRSForwardRun
                  (reverseKrsList (reverseKrsStep U hzero).previous)
                  (reverseKrsStep U hzero).previous.toForwardState := by
              exact ih
                (reverseKrsStep U hzero).previous.shape.card
                hprev_lt
                (reverseKrsStep U hzero).previous
                rfl
            rcases hstepInverse U hzero with ⟨hrec, hstep⟩
            have hlist :
                reverseKrsList U =
                  reverseKrsList (reverseKrsStep U hzero).previous ++
                    [(reverseKrsStep U hzero).letter] := by
              unfold reverseKrsList
              rw [← (reverseKrsStep U hzero).card_previous]
              simp [reverseKrsListAux, hzero]
            have hsorted :
                (reverseKrsList (reverseKrsStep U hzero).previous ++
                    [(reverseKrsStep U hzero).letter]).Pairwise
                  (fun x y => toLex x ≤ toLex y) := by
              rw [← hlist]
              exact reverseKrsList_sorted U
            have hsame_next :
                ∀ y : Fin m × Fin n,
                  ((reverseKrsList (reverseKrsStep U hzero).previous ++
                        [(reverseKrsStep U hzero).letter]) ++ [y]).Pairwise
                      (fun x y => toLex x ≤ toLex y) →
                    let S' :=
                      krsForwardStep
                        (reverseKrsStep U hzero).previous.toForwardState
                        (reverseKrsStep U hzero).letter hrec
                    let R := rowInsert S'.P y.2
                    ∀ {c : ℕ × ℕ}, c ∈ S'.shape →
                      S'.Q.T c.1 c.2 = y.1.val →
                        c.2 < R.newCell.2 := by
              exact
                krsForwardStep_sameUpperCellsLeftOfNext
                  hprev
                  (reverseKrsStep U hzero).letter
                  hsorted
                  hrec
            have hrunStep :
                KRSForwardRun
                  (reverseKrsList (reverseKrsStep U hzero).previous ++
                    [(reverseKrsStep U hzero).letter])
                  (krsForwardStep
                    (reverseKrsStep U hzero).previous.toForwardState
                    (reverseKrsStep U hzero).letter
                    hrec) := by
              exact
                KRSForwardRun.snoc
                  (reverseKrsStep U hzero).letter
                  hprev
                  hsorted
                  hrec
                  hsame_next
            have hstate :
                krsForwardStep
                    (reverseKrsStep U hzero).previous.toForwardState
                    (reverseKrsStep U hzero).letter
                    hrec =
                  U.toForwardState := by
              have hpair :=
                congrArg TableauPair.toForwardState hstep
              exact ((fun a ↦ hpair) ∘ fun a ↦ m) m
            rw [hlist, ← hstate]
            exact hrunStep
    exact haux T.shape.card T rfl
  have hchosen :
      KRSForwardRun (reverseKrsList T)
        (krsForwardStateOfList
          (reverseKrsList T)
          (reverseKrsList_sorted T)) :=
    krsForwardStateOfList_run _ _
  have hstate :
      krsForwardStateOfList
          (reverseKrsList T)
          (reverseKrsList_sorted T)
        = T.toForwardState := by
    -- This will follow from determinism/uniqueness of certified forward KRS runs.
    -- A later API should prove `KRSForwardRun.unique hchosen hrunRebuild`.
    have hrun_unique :
        ∀ {u₁ : List (Fin m × Fin n)} {S₁ : KRSForwardState m n},
          KRSForwardRun u₁ S₁ →
          ∀ {u₂ : List (Fin m × Fin n)} {S₂ : KRSForwardState m n},
            KRSForwardRun u₂ S₂ →
            u₁ = u₂ →
            S₁ = S₂ := by
      intro u₁ S₁ h₁
      induction h₁ with
      | nil =>
          intro u₂ S₂ h₂ hu
          cases h₂ with
          | nil =>
              rfl
          | snoc z hrun hsorted hrec hsame_next =>
              simp at hu
      | @snoc w S z hrun hsorted hrec hsame_next ih =>
          intro u₂ S₂ h₂ hu
          cases h₂ with
          | nil =>
              simp at hu
          | @snoc w' S' z' hrun' hsorted' hrec' hsame_next' =>
              have hrev :
                  z :: w.reverse = z' :: w'.reverse := by
                simpa using congrArg List.reverse hu
              have hz : z = z' := by
                exact (List.cons.inj hrev).1
              have hwrev : w.reverse = w'.reverse := by
                exact (List.cons.inj hrev).2
              have hw : w = w' := by
                simpa using congrArg List.reverse hwrev
              subst z'
              subst w'
              have hS : S = S' := by
                exact ih hrun' rfl
              subst S'
              have hhrec : hrec = hrec' := by
                exact Subsingleton.elim _ _
              subst hrec'
              rfl
    exact hrun_unique hchosen hrunRebuild rfl
  simpa [reverseKrsBiword, krsTableauPair, TableauPair.toForwardState] using
    congrArg KRSForwardState.toTableauPair hstate

/-- KRS and reverse KRS are inverse equivalences on biwords and same-shape tableau pairs. -/
noncomputable def krsBiwordEquivTableauPair (m n : ℕ) :
    Biword m n ≃ TableauPair m n :=
  { toFun := fun W => krsTableauPair W
    invFun := fun T => reverseKrsBiword T
    left_inv := reverse_krs_krs
    right_inv := krs_reverse_krs }

/-- KRS creates one box for each letter of the input biword. -/
theorem krs_shape_numBoxes {m n : ℕ} (W : Biword m n) :
    (krsTableauPair W).shape.card = W.1.length := by
  simpa [krsTableauPair, KRSForwardState.toTableauPair] using
    krsForwardStateOfList_shape_card
      W.1 W.2

private lemma generalizedPermutation_nil {m n : ℕ} :
    generalizedPermutation ([] : List (Fin m × Fin n)) = [] := by
  apply List.eq_nil_of_length_eq_zero
  have hlen :=
    (generalizedPermutation.generalizedPermutation_perm
      ([] : List (Fin m × Fin n))).length_eq
  simpa using hlen

private lemma width_nil {m n : ℕ} :
    generalizedPermutation.width ([] : List (Fin m × Fin n)) = 0 := by
  simp [generalizedPermutation.width, generalizedPermutation.lowerWord,
    generalizedPermutation_nil]

private lemma generalizedPermutation_eq_self_of_sorted {m n : ℕ}
    {w : List (Fin m × Fin n)}
    (hsorted : w.Pairwise (fun x y => toLex x ≤ toLex y)) :
    generalizedPermutation w = w := by
  exact generalizedPermutation.generalizedPermutation_unique
    (xs := w)
    (w₁ := generalizedPermutation w)
    (w₂ := w)
    (generalizedPermutation.generalizedPermutation_perm w)
    (generalizedPermutation.generalizedPermutation_sorted w)
    (List.Perm.refl w)
    hsorted

private lemma lowerWord_eq_map_snd_of_sorted {m n : ℕ}
    {w : List (Fin m × Fin n)}
    (hsorted : w.Pairwise (fun x y => toLex x ≤ toLex y)) :
    generalizedPermutation.lowerWord w = w.map Prod.snd := by
  simp [generalizedPermutation.lowerWord, generalizedPermutation_eq_self_of_sorted hsorted]

private lemma lowerWord_append_singleton_of_sorted {m n : ℕ}
    {w : List (Fin m × Fin n)} {z : Fin m × Fin n}
    (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y)) :
    generalizedPermutation.lowerWord (w ++ [z]) =
      generalizedPermutation.lowerWord w ++ [z.2] := by
  have hsorted_w : w.Pairwise (fun x y => toLex x ≤ toLex y) :=
    (List.pairwise_append.mp hsorted).1
  simp [lowerWord_eq_map_snd_of_sorted hsorted,
    lowerWord_eq_map_snd_of_sorted hsorted_w]

private lemma width_le_of_lowerWord_sublist {m n : ℕ}
    {xs ys : List (Fin m × Fin n)}
    (hsub :
      List.Sublist (generalizedPermutation.lowerWord xs)
        (generalizedPermutation.lowerWord ys)) :
    generalizedPermutation.width xs ≤ generalizedPermutation.width ys := by
  unfold generalizedPermutation.width
  apply generalizedPermutation.foldl_max_length_le
  · exact Nat.zero_le _
  · intro s hs
    have hs_mem :
        s ∈ (generalizedPermutation.lowerWord xs).sublists := (List.mem_filter.mp hs).1
    have hs_dec :
        (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true :=
      (List.mem_filter.mp hs).2
    have hs_sub_xs : List.Sublist s (generalizedPermutation.lowerWord xs) :=
      (List.mem_sublists).1 hs_mem
    have hs_sub_ys : List.Sublist s (generalizedPermutation.lowerWord ys) :=
      hs_sub_xs.trans hsub
    exact length_le_width_of_lowerWord_sublist_pairwise_gt
      (xs := ys) hs_sub_ys
      (generalizedPermutation.pairwise_gt_of_zip_tail_all_gt hs_dec)

private lemma width_le_width_append_singleton_of_sorted {m n : ℕ}
    {w : List (Fin m × Fin n)} {z : Fin m × Fin n}
    (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y)) :
    generalizedPermutation.width w ≤ generalizedPermutation.width (w ++ [z]) := by
  apply width_le_of_lowerWord_sublist
  rw [lowerWord_append_singleton_of_sorted hsorted]
  exact List.sublist_append_left _ _

private lemma width_append_singleton_le_succ_width_of_sorted {m n : ℕ}
    {w : List (Fin m × Fin n)} {z : Fin m × Fin n}
    (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y)) :
    generalizedPermutation.width (w ++ [z]) ≤ generalizedPermutation.width w + 1 := by
  unfold generalizedPermutation.width
  rw [lowerWord_append_singleton_of_sorted hsorted, List.sublists_concat]
  apply generalizedPermutation.foldl_max_length_le
  · exact Nat.zero_le _
  · intro s hs
    have hs_mem :
        s ∈ (generalizedPermutation.lowerWord w).sublists ++
          (generalizedPermutation.lowerWord w).sublists.map
            (fun x => x ++ [z.2]) := (List.mem_filter.mp hs).1
    have hs_dec :
        (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true :=
      (List.mem_filter.mp hs).2
    rcases List.mem_append.mp hs_mem with hs_old | hs_new
    · have hsub : List.Sublist s (generalizedPermutation.lowerWord w) :=
        (List.mem_sublists).1 hs_old
      have hpair : s.Pairwise (fun a b => a > b) :=
        generalizedPermutation.pairwise_gt_of_zip_tail_all_gt hs_dec
      have hlen : s.length ≤ generalizedPermutation.width w :=
        length_le_width_of_lowerWord_sublist_pairwise_gt
          (xs := w) hsub hpair
      change s.length ≤ generalizedPermutation.width w + 1
      omega
    · rcases List.mem_map.mp hs_new with ⟨t, htmem, rfl⟩
      have ht_sub : List.Sublist t (generalizedPermutation.lowerWord w) :=
        (List.mem_sublists).1 htmem
      have hs_pair : (t ++ [z.2]).Pairwise (fun a b => a > b) :=
        generalizedPermutation.pairwise_gt_of_zip_tail_all_gt hs_dec
      have ht_pair : t.Pairwise (fun a b => a > b) :=
        hs_pair.sublist (List.sublist_append_left _ _)
      have ht_len : t.length ≤ generalizedPermutation.width w :=
        length_le_width_of_lowerWord_sublist_pairwise_gt
          (xs := w) ht_sub ht_pair
      simpa [List.length_append, generalizedPermutation.width] using ht_len

private lemma width_append_singleton_le_of_ending_subseq_bound {m n : ℕ}
    {w : List (Fin m × Fin n)} {z : Fin m × Fin n}
    (hsorted : (w ++ [z]).Pairwise (fun x y => toLex x ≤ toLex y))
    (hend :
      ∀ {t : List (Fin n)},
        List.Sublist t (generalizedPermutation.lowerWord w) →
        (t ++ [z.2]).Pairwise (fun a b => a > b) →
          t.length + 1 ≤ generalizedPermutation.width w) :
    generalizedPermutation.width (w ++ [z]) ≤ generalizedPermutation.width w := by
  unfold generalizedPermutation.width
  rw [lowerWord_append_singleton_of_sorted hsorted, List.sublists_concat]
  apply generalizedPermutation.foldl_max_length_le
  · exact Nat.zero_le _
  · intro s hs
    have hs_mem :
        s ∈ (generalizedPermutation.lowerWord w).sublists ++
          (generalizedPermutation.lowerWord w).sublists.map
            (fun x => x ++ [z.2]) := (List.mem_filter.mp hs).1
    have hs_dec :
        (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true :=
      (List.mem_filter.mp hs).2
    rcases List.mem_append.mp hs_mem with hs_old | hs_new
    · have hsub : List.Sublist s (generalizedPermutation.lowerWord w) :=
        (List.mem_sublists).1 hs_old
      have hpair : s.Pairwise (fun a b => a > b) :=
        generalizedPermutation.pairwise_gt_of_zip_tail_all_gt hs_dec
      exact length_le_width_of_lowerWord_sublist_pairwise_gt
        (xs := w) hsub hpair
    · rcases List.mem_map.mp hs_new with ⟨t, htmem, rfl⟩
      have ht_sub : List.Sublist t (generalizedPermutation.lowerWord w) :=
        (List.mem_sublists).1 htmem
      have ht_pair : (t ++ [z.2]).Pairwise (fun a b => a > b) :=
        generalizedPermutation.pairwise_gt_of_zip_tail_all_gt hs_dec
      simpa [List.length_append, generalizedPermutation.width] using
        hend ht_sub ht_pair

private lemma sublist_append_singleton_cases {α : Type*}
    {s l : List α} {a : α} (h : List.Sublist s (l ++ [a])) :
    List.Sublist s l ∨ ∃ t, List.Sublist t l ∧ s = t ++ [a] := by
  induction l generalizing s with
  | nil =>
      rcases (List.sublist_singleton.mp h) with rfl | rfl
      · exact Or.inl List.Sublist.slnil
      · exact Or.inr ⟨[], List.Sublist.slnil, rfl⟩
  | cons b l ih =>
      cases h with
      | cons _ htail =>
          rcases ih htail with hold | ⟨t, ht, rfl⟩
          · exact Or.inl (List.Sublist.cons b hold)
          · exact Or.inr ⟨t, List.Sublist.cons b ht, rfl⟩
      | cons₂ _ htail =>
          rcases ih htail with hold | ⟨t, ht, ht_eq⟩
          · exact Or.inl (List.Sublist.cons₂ b hold)
          · subst ht_eq
            exact Or.inr ⟨b :: t, List.Sublist.cons₂ b ht, by simp⟩

private lemma firstColumnHeight_bot :
    firstColumnHeight (⊥ : YoungDiagram) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hcell : (0, 0) ∈ (⊥ : YoungDiagram) := by
    rwa [YoungDiagram.mem_iff_lt_colLen]
  simp at hcell

/-- A compressed bumping-path ancestry.

Starting at `row` with threshold `x`, each layer chooses a cell weakly below the
current row whose entry is strictly larger than the current threshold.  The chosen
entry becomes the next threshold, and the next layer must occur in a strictly lower
row.  Columns are intentionally existential: they are the caps selected by the
leftmost-bump rule when this ancestry is replayed by row insertion. -/
def CompressedBumpChain {N : ℕ} {μ : YoungDiagram}
    (T : BoundedSSYT μ N) (row x : ℕ) : ℕ → Prop
  | 0 => True
  | k + 1 =>
      ∃ i j : ℕ, row ≤ i ∧ (i, j) ∈ μ ∧ x < T.T i j ∧
        CompressedBumpChain T (i + 1) (T.T i j) k

namespace CompressedBumpChain

theorem mono_threshold {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row x y k : ℕ}
    (hxy : x ≤ y) (hchain : CompressedBumpChain T row y k) :
    CompressedBumpChain T row x k := by
  induction k generalizing row y with
  | zero => trivial
  | succ k ih =>
      rcases hchain with ⟨i, j, hrow, hcell, hgt, htail⟩
      exact ⟨i, j, hrow, hcell, lt_of_le_of_lt hxy hgt, htail⟩

theorem weaken_start {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row row' x k : ℕ}
    (hrow : row' ≤ row) (hchain : CompressedBumpChain T row x k) :
    CompressedBumpChain T row' x k := by
  cases k with
  | zero => trivial
  | succ k =>
      rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
      exact ⟨i, j, le_trans hrow hi, hcell, hgt, htail⟩

theorem length_le_firstColumnHeight_of_start_le {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row x k : ℕ}
    (hstart : row ≤ firstColumnHeight μ)
    (hchain : CompressedBumpChain T row x k) :
    row + k ≤ firstColumnHeight μ := by
  induction k generalizing row x with
  | zero => simpa using hstart
  | succ k ih =>
      rcases hchain with ⟨i, j, hrow, hcell, hgt, htail⟩
      have hi_lt : i < μ.colLen j := by
        rwa [YoungDiagram.mem_iff_lt_colLen] at hcell
      have hi_height : i + 1 ≤ firstColumnHeight μ := by
        dsimp [firstColumnHeight]
        have hcol := μ.colLen_anti 0 j (Nat.zero_le j)
        omega
      have htail_bound := ih hi_height htail
      omega

theorem length_le_firstColumnHeight {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {x k : ℕ}
    (hchain : CompressedBumpChain T 0 x k) :
    k ≤ firstColumnHeight μ := by
  simpa using length_le_firstColumnHeight_of_start_le (T := T)
    (x := x) (Nat.zero_le _) hchain

theorem of_old_subset_entry_eq {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row x k : ℕ}
    (hsub : ∀ c, c ∈ μ → c ∈ ν)
    (hentry : ∀ {i j : ℕ}, row ≤ i → (i, j) ∈ μ → S.T i j = T.T i j)
    (hchain : CompressedBumpChain T row x k) :
    CompressedBumpChain S row x k := by
  induction k generalizing row x with
  | zero => trivial
  | succ k ih =>
      rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
      refine ⟨i, j, hi, hsub (i, j) hcell, ?_, ?_⟩
      · simpa [hentry hi hcell] using hgt
      · have htransport :
            CompressedBumpChain S (i + 1) (T.T i j) k := by
          apply ih
          · intro i' j' hi' hcell'
            exact hentry (by omega) hcell'
          · exact htail
        simpa [hentry hi hcell] using htransport

theorem of_rows_equiv {N : ℕ} {μ ν : YoungDiagram}
    {T : BoundedSSYT μ N} {S : BoundedSSYT ν N} {row x k : ℕ}
    (hshape : ∀ {i j : ℕ}, row ≤ i → ((i, j) ∈ μ ↔ (i, j) ∈ ν))
    (hentry : ∀ {i j : ℕ}, row ≤ i → S.T i j = T.T i j)
    (hchain : CompressedBumpChain T row x k) :
    CompressedBumpChain S row x k := by
  induction k generalizing row x with
  | zero => trivial
  | succ k ih =>
      rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
      refine ⟨i, j, hi, (hshape hi).1 hcell, ?_, ?_⟩
      · simpa [hentry hi] using hgt
      · have htransport :
            CompressedBumpChain S (i + 1) (T.T i j) k := by
          apply ih
          · intro i' j' hi'
            exact hshape (by omega)
          · intro i' j' hi'
            exact hentry (by omega)
          · exact htail
        simpa [hentry hi] using htransport

theorem after_append_start_succ {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N} {k : ℕ}
    (A : RowAppendLocation T row x)
    (hchain : CompressedBumpChain T row x.val k) :
    CompressedBumpChain T (row + 1) x.val k := by
  induction k generalizing row x with
  | zero => trivial
  | succ k ih =>
      rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
      have hi_ne : i ≠ row := by
        intro heq
        subst i
        have hj : j < μ.rowLen row := by
          rwa [YoungDiagram.mem_iff_lt_rowLen] at hcell
        exact (not_lt_of_ge (A.row_entries_le hj)) hgt
      exact ⟨i, j, by omega, hcell, hgt, htail⟩

end CompressedBumpChain

/-- Row insertion transports compressed ancestries.  If the new threshold is strictly
smaller than the inserted letter, the inserted path contributes one additional layer. -/
private theorem RowInsertionTrace.compressedBumpChain_ops {N : ℕ} {μ : YoungDiagram}
    {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (tr : RowInsertionTrace N T row x) :
    (∀ (threshold k : ℕ), CompressedBumpChain T row threshold k →
      CompressedBumpChain tr.result.tableau row threshold k) ∧
    (∀ (threshold : ℕ), threshold < x.val → ∀ k : ℕ,
      CompressedBumpChain T row x.val k →
        CompressedBumpChain tr.result.tableau row threshold (k + 1)) := by
  induction tr with
  | done A =>
      rename_i T₀ row₀ x₀
      constructor
      · intro threshold k hchain
        exact CompressedBumpChain.of_old_subset_entry_eq
          A.result.old_subset
          (fun _ hcell => A.unchanged_on_old_shape hcell)
          hchain
      · intro threshold hthreshold k hchain
        have htail :
            CompressedBumpChain A.result.tableau (row₀ + 1) x₀.val k := by
          apply CompressedBumpChain.of_old_subset_entry_eq A.result.old_subset
          · intro i j hi hcell
            exact A.unchanged_on_old_shape hcell
          · exact CompressedBumpChain.after_append_start_succ A.location hchain
        have hcell : (row₀, A.result.newCell.2) ∈ A.result.shape := by
          simpa only [← A.result_newCell_row] using A.result.newCell_mem
        have htail' :
            CompressedBumpChain A.result.tableau (row₀ + 1)
              (A.result.tableau.T row₀ A.result.newCell.2) k := by
          have hentry :
              A.result.tableau.T row₀ A.result.newCell.2 = x₀.val := by
            rw [A.result_newCell_col]
            exact A.inserted_entry
          simpa only [hentry] using htail
        refine ⟨row₀, A.result.newCell.2, le_rfl, hcell, ?_, htail'⟩
        have hentry :
            A.result.tableau.T row₀ A.result.newCell.2 = x₀.val := by
          rw [A.result_newCell_col]
          exact A.inserted_entry
        simpa only [RowInsertionTrace.result, hentry] using hthreshold
  | bump B tail ih =>
      rename_i T₀ row₀ x₀
      rcases ih with ⟨ih_preserve, ih_extend⟩
      have hlower :
          ∀ {start threshold k : ℕ}, row₀ + 1 ≤ start →
            CompressedBumpChain T₀ start threshold k →
              CompressedBumpChain B.tableau start threshold k := by
        intro start threshold k hstart hchain
        exact CompressedBumpChain.of_old_subset_entry_eq
          (fun _ hcell => hcell)
          (fun hi _ => B.unchanged_of_row_ne (by omega))
          hchain
      have htop_cell : (row₀, B.col) ∈ tail.result.shape :=
        tail.result.old_subset (row₀, B.col) B.cell_mem
      have htop_entry :
          tail.result.tableau.T row₀ B.col = x₀.val := by
        calc
          tail.result.tableau.T row₀ B.col = B.tableau.T row₀ B.col :=
            tail.result_tableau_eq_of_row_lt (by omega) B.cell_mem
          _ = x₀.val := B.replaced_entry
      constructor
      · intro threshold k hchain
        cases k with
        | zero => trivial
        | succ k =>
            rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
            by_cases hirow : i = row₀
            · subst i
              by_cases hxgt : x₀.val < T₀.T row₀ j
              · have hcol : B.col ≤ j :=
                  B.col_le_of_entry_gt hcell hxgt
                rcases lt_or_eq_of_le hcol with hcollt | hcoleq
                · have htailB := hlower (by omega) htail
                  have htailR := ih_preserve (T₀.T row₀ j) k htailB
                  have htailR' :
                      CompressedBumpChain tail.result.tableau (row₀ + 1)
                        (tail.result.tableau.T row₀ j) k := by
                    have hentry :
                        tail.result.tableau.T row₀ j = T₀.T row₀ j := by
                      calc
                        tail.result.tableau.T row₀ j = B.tableau.T row₀ j :=
                          tail.result_tableau_eq_of_row_lt (by omega) hcell
                        _ = T₀.T row₀ j :=
                          B.unchanged_of_col_ne (Nat.ne_of_gt hcollt)
                    simpa only [hentry] using htailR
                  refine ⟨row₀, j, le_rfl, tail.result.old_subset (row₀, j) hcell, ?_, htailR'⟩
                  calc
                    threshold < T₀.T row₀ j := hgt
                    _ = B.tableau.T row₀ j := by
                      symm
                      exact B.unchanged_of_col_ne (Nat.ne_of_gt hcollt)
                    _ = tail.result.tableau.T row₀ j := by
                      symm
                      exact tail.result_tableau_eq_of_row_lt (by omega) hcell
                · have hval : T₀.T row₀ j = B.bumped.val := by
                    simpa [hcoleq] using B.bumped_eq
                  have htailB := hlower (by omega) htail
                  have htailB' :
                      CompressedBumpChain B.tableau (row₀ + 1) B.bumped.val k := by
                    simpa [hval] using htailB
                  have hthreshold_bumped : threshold < B.bumped.val := by
                    simpa [← hval] using hgt
                  exact CompressedBumpChain.weaken_start (Nat.le_succ row₀)
                    (ih_extend threshold hthreshold_bumped k htailB')
              · have hcolne : B.col ≠ j := by
                  intro hcol
                  apply hxgt
                  simpa [hcol] using B.entry_gt
                have htailB := hlower (by omega) htail
                have htailR := ih_preserve (T₀.T row₀ j) k htailB
                have htailR' :
                    CompressedBumpChain tail.result.tableau (row₀ + 1)
                      (tail.result.tableau.T row₀ j) k := by
                  have hentry :
                      tail.result.tableau.T row₀ j = T₀.T row₀ j := by
                    calc
                      tail.result.tableau.T row₀ j = B.tableau.T row₀ j :=
                        tail.result_tableau_eq_of_row_lt (by omega) hcell
                      _ = T₀.T row₀ j := B.unchanged_of_col_ne hcolne.symm
                  simpa only [hentry] using htailR
                refine ⟨row₀, j, le_rfl, tail.result.old_subset (row₀, j) hcell, ?_, htailR'⟩
                calc
                  threshold < T₀.T row₀ j := hgt
                  _ = B.tableau.T row₀ j := by
                    symm
                    exact B.unchanged_of_col_ne hcolne.symm
                  _ = tail.result.tableau.T row₀ j := by
                    symm
                    exact tail.result_tableau_eq_of_row_lt (by omega) hcell
            · have hi' : row₀ + 1 ≤ i := by omega
              have hchainB :
                  CompressedBumpChain B.tableau (row₀ + 1) threshold (k + 1) := by
                refine ⟨i, j, hi', hcell, ?_, ?_⟩
                · simpa [B.unchanged_of_row_ne hirow] using hgt
                · have htailB := hlower (by omega) htail
                  have hentry : B.tableau.T i j = T₀.T i j :=
                    B.unchanged_of_row_ne hirow
                  simpa only [hentry] using htailB
              exact CompressedBumpChain.weaken_start (Nat.le_succ row₀)
                (ih_preserve threshold (k + 1) hchainB)
      · intro threshold hthreshold k hchain
        cases k with
        | zero =>
            exact ⟨row₀, B.col, le_rfl, htop_cell, by
              change threshold < tail.result.tableau.T row₀ B.col
              simpa only [htop_entry] using hthreshold,
              trivial⟩
        | succ k =>
            rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
            have hlower_result :
                CompressedBumpChain tail.result.tableau (row₀ + 1) x₀.val (k + 1) := by
              by_cases hirow : i = row₀
              · subst i
                have hcol : B.col ≤ j := B.col_le_of_entry_gt hcell hgt
                have hbumped_le : B.bumped.val ≤ T₀.T row₀ j :=
                  B.bumped_le_entry_of_entry_gt hcell hgt
                have htailB := hlower (by omega) htail
                have htailB' :
                    CompressedBumpChain B.tableau (row₀ + 1) B.bumped.val k :=
                  CompressedBumpChain.mono_threshold hbumped_le htailB
                exact ih_extend x₀.val B.bumped_gt k htailB'
              · have hi' : row₀ + 1 ≤ i := by omega
                have hchainB :
                    CompressedBumpChain B.tableau (row₀ + 1) x₀.val (k + 1) := by
                  refine ⟨i, j, hi', hcell, ?_, ?_⟩
                  · simpa [B.unchanged_of_row_ne hirow] using hgt
                  · have htailB := hlower (by omega) htail
                    have hentry : B.tableau.T i j = T₀.T i j :=
                      B.unchanged_of_row_ne hirow
                    simpa only [hentry] using htailB
                exact ih_preserve x₀.val (k + 1) hchainB
            have hlower_result' :
                CompressedBumpChain tail.result.tableau (row₀ + 1)
                  (tail.result.tableau.T row₀ B.col) (k + 1) := by
              simpa [htop_entry] using hlower_result
            exact ⟨row₀, B.col, le_rfl, htop_cell,
              by
                change threshold < tail.result.tableau.T row₀ B.col
                simpa only [htop_entry] using hthreshold,
              hlower_result'⟩

/-- Every compressed ancestry after insertion either already existed or uses the
newly inserted letter as its final layer. -/
private theorem RowInsertionTrace.compressedBumpChain_cases
    {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (tr : RowInsertionTrace N T row x) :
    ∀ {threshold k : ℕ},
      CompressedBumpChain tr.result.tableau row threshold k →
        CompressedBumpChain T row threshold k ∨
          ∃ l : ℕ, k = l + 1 ∧ threshold < x.val ∧
            CompressedBumpChain T row x.val l := by
  induction tr with
  | done A =>
      rename_i T₀ row₀ x₀
      intro threshold k hchain
      simp only [RowInsertionTrace.result] at hchain
      have hlower :
          ∀ {start value length : ℕ}, row₀ + 1 ≤ start →
            CompressedBumpChain A.result.tableau start value length →
              CompressedBumpChain T₀ start value length := by
        intro start value length hstart hchain
        apply CompressedBumpChain.of_rows_equiv
            (T := A.result.tableau) (S := T₀)
        · intro i j hi
          constructor
          · intro hcell
            rcases (A.result.shape_mem_iff (i, j)).1 hcell with hold | hnew
            · exact hold
            · have hirow : i = row₀ := by
                simpa [A.newCell_eq] using congrArg Prod.fst hnew
              omega
          · intro hcell
            exact A.result.old_subset (i, j) hcell
        · intro i j hi
          exact (A.unchanged_of_row_ne (by omega)).symm
        · exact hchain
      cases k with
      | zero => exact Or.inl trivial
      | succ k =>
          rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
          rcases (A.result.shape_mem_iff (i, j)).1 hcell with hold | hnew
          · have hentry : A.result.tableau.T i j = T₀.T i j :=
              A.unchanged_on_old_shape hold
            have htailT := hlower (by omega) htail
            left
            refine ⟨i, j, hi, hold, ?_, ?_⟩
            · simpa only [hentry] using hgt
            · simpa only [hentry] using htailT
          · have hirow : i = row₀ := by
              simpa [A.newCell_eq] using congrArg Prod.fst hnew
            have hjcol : j = A.result.newCell.2 := by
              exact congrArg Prod.snd hnew
            subst i
            subst j
            have hentry :
                A.result.tableau.T row₀ A.result.newCell.2 = x₀.val := by
              rw [A.result_newCell_col]
              exact A.inserted_entry
            have htailT := hlower (by omega) htail
            right
            refine ⟨k, rfl, ?_, ?_⟩
            · simpa only [hentry] using hgt
            · apply CompressedBumpChain.weaken_start (Nat.le_succ row₀)
              simpa only [hentry] using htailT
  | bump B tail ih =>
      rename_i T₀ row₀ x₀
      intro threshold k hchain
      simp only [RowInsertionTrace.result] at hchain
      have hlower :
          ∀ {start value length : ℕ}, row₀ + 1 ≤ start →
            CompressedBumpChain B.tableau start value length →
              CompressedBumpChain T₀ start value length := by
        intro start value length hstart hchain
        apply CompressedBumpChain.of_rows_equiv
            (T := B.tableau) (S := T₀)
        · intro i j hi
          exact Iff.rfl
        · intro i j hi
          exact (B.unchanged_of_row_ne (by omega)).symm
        · exact hchain
      have htop_old :
          ∀ {j : ℕ}, (row₀, j) ∈ tail.result.shape → (row₀, j) ∈ μ := by
        intro j hcell
        rcases (tail.result.shape_mem_iff (row₀, j)).1 hcell with hold | hnew
        · exact hold
        · have hrow : row₀ = tail.result.newCell.1 :=
            congrArg Prod.fst hnew
          have hge := tail.result_newCell_row_ge
          omega
      cases k with
      | zero => exact Or.inl trivial
      | succ k =>
          rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
          by_cases hirow : i = row₀
          · subst i
            have hcell_old : (row₀, j) ∈ μ := htop_old hcell
            have hentry :
                tail.result.tableau.T row₀ j = B.tableau.T row₀ j :=
              tail.result_tableau_eq_of_row_lt (by omega) hcell_old
            have htail' :
                CompressedBumpChain tail.result.tableau (row₀ + 1)
                  (B.tableau.T row₀ j) k := by
              simpa only [hentry] using htail
            rcases ih htail' with htail_old | ⟨l, hk, hbumped, htail_bumped⟩
            · by_cases hj : j = B.col
              · subst j
                have htailT := hlower (by omega) htail_old
                right
                refine ⟨k, rfl, ?_, ?_⟩
                · simpa only [hentry, B.replaced_entry] using hgt
                · apply CompressedBumpChain.weaken_start (Nat.le_succ row₀)
                  simpa only [B.replaced_entry] using htailT
              · have hentry_old : B.tableau.T row₀ j = T₀.T row₀ j :=
                  B.unchanged_of_col_ne hj
                have htailT := hlower (by omega) htail_old
                left
                refine ⟨row₀, j, le_rfl, hcell_old, ?_, ?_⟩
                · simpa only [hentry, hentry_old] using hgt
                · simpa only [hentry_old] using htailT
            · subst k
              have hthreshold_x : threshold < x₀.val := by
                have hthreshold_current : threshold < B.tableau.T row₀ j := by
                  simpa only [hentry] using hgt
                by_cases hj : j = B.col
                · subst j
                  simpa only [B.replaced_entry] using hthreshold_current
                · have hjlt : j < B.col := by
                    by_contra hnot
                    have hcol_le : B.col ≤ j := Nat.le_of_not_gt hnot
                    have hbumped_le_current :
                        B.bumped.val ≤ B.tableau.T row₀ j := by
                      calc
                        B.bumped.val = T₀.T row₀ B.col := B.bumped_eq.symm
                        _ ≤ T₀.T row₀ j :=
                          T₀.T.row_weak_of_le hcol_le hcell_old
                        _ = B.tableau.T row₀ j :=
                          (B.unchanged_of_col_ne hj).symm
                    exact (not_lt_of_ge hbumped_le_current) hbumped
                  have hcurrent_le : B.tableau.T row₀ j ≤ x₀.val := by
                    calc
                      B.tableau.T row₀ j = T₀.T row₀ j :=
                        B.unchanged_of_col_ne hj
                      _ ≤ x₀.val := B.left_le hjlt hcell_old
                  exact lt_of_lt_of_le hthreshold_current hcurrent_le
              have htailT := hlower (by omega) htail_bumped
              have htailT' :
                  CompressedBumpChain T₀ (row₀ + 1) (T₀.T row₀ B.col) l := by
                simpa only [B.bumped_eq] using htailT
              right
              refine ⟨l + 1, rfl, hthreshold_x, ?_⟩
              exact ⟨row₀, B.col, le_rfl, B.cell_mem, B.entry_gt, htailT'⟩
          · have hi' : row₀ + 1 ≤ i := by omega
            have hchain_lower :
                CompressedBumpChain tail.result.tableau (row₀ + 1)
                  threshold (k + 1) :=
              ⟨i, j, hi', hcell, hgt, htail⟩
            rcases ih hchain_lower with hchain_old | ⟨l, hk, hbumped, htail_bumped⟩
            · left
              exact CompressedBumpChain.weaken_start (Nat.le_succ row₀)
                (hlower (by omega) hchain_old)
            · have hl : l = k := by omega
              subst l
              have htailT := hlower (by omega) htail_bumped
              have htailT' :
                  CompressedBumpChain T₀ (row₀ + 1) (T₀.T row₀ B.col) k := by
                simpa only [B.bumped_eq] using htailT
              left
              exact ⟨row₀, B.col, le_rfl, B.cell_mem,
                by simpa only [B.bumped_eq] using hbumped, htailT'⟩

/-- The actual bumping route is itself a compressed ancestry. -/
private theorem RowInsertionTrace.exists_compressedBumpChain_length_eq_newCell_row
    {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (tr : RowInsertionTrace N T row x) :
    ∃ k : ℕ, tr.result.newCell.1 = row + k ∧
      CompressedBumpChain T row x.val k := by
  induction tr with
  | done A =>
      exact ⟨0, by simpa [RowInsertionTrace.result] using A.result_newCell_row, trivial⟩
  | bump B tail ih =>
      rename_i T₀ row₀ x₀
      rcases ih with ⟨k, hkrow, hchain⟩
      have htail :
          CompressedBumpChain T₀ (row₀ + 1) B.bumped.val k := by
        apply CompressedBumpChain.of_rows_equiv
            (T := B.tableau) (S := T₀)
        · intro i j hi
          exact Iff.rfl
        · intro i j hi
          exact (B.unchanged_of_row_ne (by omega)).symm
        · exact hchain
      have htail' :
          CompressedBumpChain T₀ (row₀ + 1) (T₀.T row₀ B.col) k := by
        simpa only [B.bumped_eq] using htail
      refine ⟨k + 1, ?_, ⟨row₀, B.col, le_rfl, B.cell_mem, B.entry_gt, htail'⟩⟩
      simpa [RowInsertionTrace.result, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hkrow

private lemma firstColumnHeight_mono {μ ν : YoungDiagram}
    (hsub : μ ≤ ν) :
    firstColumnHeight μ ≤ firstColumnHeight ν := by
  apply le_of_not_gt
  intro hgt
  have hcellμ : (ν.colLen 0, 0) ∈ μ := by
    rw [YoungDiagram.mem_iff_lt_colLen]
    exact hgt
  have hcellν : (ν.colLen 0, 0) ∈ ν := hsub hcellμ
  have hlt : ν.colLen 0 < ν.colLen 0 := by
    rwa [YoungDiagram.mem_iff_lt_colLen] at hcellν
  exact Nat.lt_irrefl _ hlt

/-- A compressed ancestry of length `k` forces insertion to reach at least row
`row + k`. -/
private theorem RowInsertionTrace.compressedBumpChain_length_succ_le_result_firstColumnHeight
    {N : ℕ} {μ : YoungDiagram} {T : BoundedSSYT μ N} {row : ℕ} {x : Fin N}
    (tr : RowInsertionTrace N T row x) {k : ℕ}
    (hchain : CompressedBumpChain T row x.val k) :
    row + k + 1 ≤ firstColumnHeight tr.result.shape := by
  induction tr generalizing k with
  | done A =>
      rename_i T₀ row₀ x₀
      cases k with
      | zero =>
          have hcell : (row₀, 0) ∈ A.result.shape :=
            A.result.shape.up_left_mem le_rfl (Nat.zero_le _)
              (by simpa only [← A.result_newCell_row] using A.result.newCell_mem)
          dsimp [firstColumnHeight]
          rw [YoungDiagram.mem_iff_lt_colLen] at hcell
          simpa only [RowInsertionTrace.result] using hcell
      | succ k =>
          rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
          have hi_ne : i ≠ row₀ := by
            intro heq
            subst i
            have hj : j < μ.rowLen row₀ := by
              rwa [YoungDiagram.mem_iff_lt_rowLen] at hcell
            exact (not_lt_of_ge (A.location.row_entries_le hj)) hgt
          have hi_height : i + 1 ≤ firstColumnHeight μ := by
            dsimp [firstColumnHeight]
            have hi_lt : i < μ.colLen j := by
              rwa [YoungDiagram.mem_iff_lt_colLen] at hcell
            have hcol := μ.colLen_anti 0 j (Nat.zero_le j)
            omega
          have htail_bound :=
            CompressedBumpChain.length_le_firstColumnHeight_of_start_le
              hi_height htail
          have hmono : firstColumnHeight μ ≤ firstColumnHeight A.result.shape :=
            firstColumnHeight_mono A.result.old_subset
          change row₀ + (k + 1) + 1 ≤
            firstColumnHeight (RowInsertionTrace.done A).result.shape
          simp only [RowInsertionTrace.result]
          omega
  | bump B tail ih =>
      rename_i T₀ row₀ x₀
      have hlower :
          ∀ {start threshold length : ℕ}, row₀ + 1 ≤ start →
            CompressedBumpChain T₀ start threshold length →
              CompressedBumpChain B.tableau start threshold length := by
        intro start threshold length hstart hchain
        exact CompressedBumpChain.of_old_subset_entry_eq
          (fun _ hcell => hcell)
          (fun _ _ => B.unchanged_of_row_ne (by omega))
          hchain
      cases k with
      | zero =>
          have hrow_ge : row₀ + 1 ≤ tail.result.newCell.1 :=
            tail.result_newCell_row_ge
          have hcell : (tail.result.newCell.1, 0) ∈ tail.result.shape :=
            tail.result.shape.up_left_mem le_rfl (Nat.zero_le _)
              tail.result.newCell_mem
          dsimp [firstColumnHeight]
          rw [YoungDiagram.mem_iff_lt_colLen] at hcell
          change row₀ + 0 + 1 ≤
            firstColumnHeight (RowInsertionTrace.bump B tail).result.shape
          simp only [RowInsertionTrace.result]
          dsimp [firstColumnHeight]
          omega
      | succ k =>
          rcases hchain with ⟨i, j, hi, hcell, hgt, htail⟩
          by_cases hirow : i = row₀
          · subst i
            have hbumped_le : B.bumped.val ≤ T₀.T row₀ j :=
              B.bumped_le_entry_of_entry_gt hcell hgt
            have htailB := hlower (by omega) htail
            have htailB' :
                CompressedBumpChain B.tableau (row₀ + 1) B.bumped.val k :=
              CompressedBumpChain.mono_threshold hbumped_le htailB
            have hbound := ih htailB'
            change row₀ + (k + 1) + 1 ≤
              firstColumnHeight (RowInsertionTrace.bump B tail).result.shape
            simp only [RowInsertionTrace.result]
            omega
          · have hi' : row₀ + 1 ≤ i := by omega
            have hchainB :
                CompressedBumpChain B.tableau (row₀ + 1) x₀.val (k + 1) := by
              refine ⟨i, j, hi', hcell, ?_, ?_⟩
              · simpa [B.unchanged_of_row_ne hirow] using hgt
              · have htailB := hlower (by omega) htail
                have hentry : B.tableau.T i j = T₀.T i j :=
                  B.unchanged_of_row_ne hirow
                simpa only [hentry] using htailB
            have hstart : row₀ + 1 ≤ firstColumnHeight μ := by
              dsimp [firstColumnHeight]
              have hi_lt : i < μ.colLen j := by
                rwa [YoungDiagram.mem_iff_lt_colLen] at hcell
              have hcol := μ.colLen_anti 0 j (Nat.zero_le j)
              omega
            have hbound :=
              CompressedBumpChain.length_le_firstColumnHeight_of_start_le
                hstart hchainB
            have hmono :
                firstColumnHeight μ ≤
                  firstColumnHeight tail.result.shape :=
              firstColumnHeight_mono tail.result.old_subset
            change row₀ + (k + 1) + 1 ≤
              firstColumnHeight (RowInsertionTrace.bump B tail).result.shape
            simp only [RowInsertionTrace.result]
            omega

private lemma firstColumnHeight_extendsByCell_eq_of_newCell_col_ne_zero
    {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (hext : ExtendsByCell μ ν c) (hc : c.2 ≠ 0) :
    firstColumnHeight ν = firstColumnHeight μ := by
  simpa [firstColumnHeight] using ExtendsByCell.colLen_eq_of_ne hext (Ne.symm hc)

private lemma firstColumnHeight_extendsByCell_eq_succ_of_newCell_col_zero
    {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (hext : ExtendsByCell μ ν c) (hnot : c ∉ μ) (hc : c.2 = 0) :
    firstColumnHeight ν = firstColumnHeight μ + 1 := by
  simpa [firstColumnHeight, hc] using ExtendsByCell.colLen_at_newCell hext hnot

private lemma rowInsert_firstColumnHeight_eq_of_newCell_col_ne_zero {N : ℕ}
    {μ : YoungDiagram} (T : BoundedSSYT μ N) (x : Fin N)
    (hc : (rowInsert T x).newCell.2 ≠ 0) :
    firstColumnHeight (rowInsert T x).shape = firstColumnHeight μ := by
  exact firstColumnHeight_extendsByCell_eq_of_newCell_col_ne_zero
    (rowInsert T x).extendsByCell hc

private lemma rowInsert_firstColumnHeight_eq_succ_of_newCell_col_zero {N : ℕ}
    {μ : YoungDiagram} (T : BoundedSSYT μ N) (x : Fin N)
    (hc : (rowInsert T x).newCell.2 = 0) :
    firstColumnHeight (rowInsert T x).shape = firstColumnHeight μ + 1 := by
  exact firstColumnHeight_extendsByCell_eq_succ_of_newCell_col_zero
    (rowInsert T x).extendsByCell (rowInsert T x).newCell_not_mem_old hc

/-- A decreasing sublist of the processed lower word is represented by a compressed
bump ancestry in the current insertion tableau. -/
private lemma krsForwardRun_descending_sublist_compressedBumpChain
    {m n : ℕ} {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
    (hrun : KRSForwardRun w S) (z : Fin n) {t : List (Fin n)}
    (ht_sub : List.Sublist t (generalizedPermutation.lowerWord w))
    (ht_pair : (t ++ [z]).Pairwise (fun a b => a > b)) :
    CompressedBumpChain S.P 0 z.val t.length := by
  induction hrun generalizing z t with
  | nil =>
      have ht_nil : t = [] := by
        simpa [generalizedPermutation.lowerWord, generalizedPermutation_nil] using ht_sub
      subst t
      trivial
  | @snoc w S y hrun hsorted hrec hsame_next ih =>
      have ht_sub' :
          List.Sublist t (generalizedPermutation.lowerWord w ++ [y.2]) := by
        simpa [lowerWord_append_singleton_of_sorted hsorted] using ht_sub
      rcases sublist_append_singleton_cases ht_sub' with ht_old | ⟨u, hu_sub, rfl⟩
      · have hchain := ih z ht_old ht_pair
        have hpreserve :=
          ((rowInsertionTrace S.P y.2).compressedBumpChain_ops).1 z.val _ hchain
        simpa [krsForwardStep, rowInsert] using hpreserve
      · have hyz_pair : (u ++ [y.2, z]).Pairwise (fun a b => a > b) := by
          simpa [List.append_assoc] using ht_pair
        have huy_pair : (u ++ [y.2]).Pairwise (fun a b => a > b) := by
          have hsub : List.Sublist (u ++ [y.2]) (u ++ [y.2, z]) := by
            simp
          exact hyz_pair.sublist hsub
        have hyz : z.val < y.2.val := by
          have htail : [y.2, z].Pairwise (fun a b => a > b) :=
            (List.pairwise_append.mp hyz_pair).2.1
          simpa using htail
        have hchain := ih y.2 hu_sub huy_pair
        have hextend :=
          ((rowInsertionTrace S.P y.2).compressedBumpChain_ops).2 z.val hyz _ hchain
        simpa [krsForwardStep, rowInsert] using hextend

/-- Conversely, every compressed ancestry in a reachable insertion tableau is
realized by a decreasing sublist of the processed lower word. -/
private lemma krsForwardRun_compressedBumpChain_exists_descending_sublist
    {m n : ℕ} {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
    (hrun : KRSForwardRun w S) {z : Fin n} {k : ℕ}
    (hchain : CompressedBumpChain S.P 0 z.val k) :
    ∃ t : List (Fin n),
      List.Sublist t (generalizedPermutation.lowerWord w) ∧
      t.length = k ∧ (t ++ [z]).Pairwise (fun a b => a > b) := by
  induction hrun generalizing z k with
  | nil =>
      have hk : k = 0 := by
        have hle := CompressedBumpChain.length_le_firstColumnHeight hchain
        simpa [KRSForwardState.empty, firstColumnHeight_bot] using hle
      subst k
      exact ⟨[], by simp [generalizedPermutation.lowerWord, generalizedPermutation_nil],
        rfl, by simp⟩
  | @snoc w S y hrun hsorted hrec hsame_next ih =>
      have hcases :
          CompressedBumpChain S.P 0 z.val k ∨
            ∃ l : ℕ, k = l + 1 ∧ z.val < y.2.val ∧
              CompressedBumpChain S.P 0 y.2.val l := by
        apply (rowInsertionTrace S.P y.2).compressedBumpChain_cases
        simpa [krsForwardStep, rowInsert] using hchain
      rcases hcases with hold | ⟨l, rfl, hzy, hchain_y⟩
      · rcases ih hold with ⟨t, ht_sub, ht_len, ht_pair⟩
        refine ⟨t, ?_, ht_len, ht_pair⟩
        rw [lowerWord_append_singleton_of_sorted hsorted]
        exact ht_sub.trans (List.sublist_append_left _ _)
      · rcases ih hchain_y with ⟨t, ht_sub, ht_len, ht_pair⟩
        refine ⟨t ++ [y.2], ?_, by simp [ht_len], ?_⟩
        · rw [lowerWord_append_singleton_of_sorted hsorted]
          exact ht_sub.append (List.Sublist.refl [y.2])
        · apply List.pairwise_append.mpr
          refine ⟨ht_pair, by simp, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at hb
          subst b
          rcases List.mem_append.mp ha with hat | hay
          · have hay_gt : a > y.2 :=
              (List.pairwise_append.mp ht_pair).2.2 a hat y.2 (by simp)
            exact lt_trans hzy hay_gt
          · simp only [List.mem_singleton] at hay
            subst a
            exact hzy

private lemma krsForwardRun_descending_suffix_length_le_rowInsert_firstColumnHeight
    {m n : ℕ} {w : List (Fin m × Fin n)} {S : KRSForwardState m n}
    (hrun : KRSForwardRun w S) (z : Fin m × Fin n)
    {t : List (Fin n)}
    (ht_sub : List.Sublist t (generalizedPermutation.lowerWord w))
    (ht_pair : (t ++ [z.2]).Pairwise (fun a b => a > b)) :
    t.length + 1 ≤ firstColumnHeight (rowInsert S.P z.2).shape := by
  have hchain :=
    krsForwardRun_descending_sublist_compressedBumpChain hrun z.2 ht_sub ht_pair
  simpa [rowInsert] using
    (rowInsertionTrace S.P z.2).compressedBumpChain_length_succ_le_result_firstColumnHeight
      hchain

/-- Schensted's theorem for the lower word: LDS equals first-column height. -/
theorem schensted_lds_eq_firstColumnHeight {m n : ℕ} (W : Biword m n) :
    generalizedPermutation.width W.1 =
      firstColumnHeight (krsTableauPair W).shape := by
  have hrun :
      KRSForwardRun W.1
        (krsForwardStateOfList W.1 W.2) := by
    exact krsForwardStateOfList_run
      W.1 W.2
  /-
  Every strictly decreasing subsequence of the processed lower word
  is controlled by the rows created in the insertion tableau.
  -/
  have hboth :
      ∀ {w : List (Fin m × Fin n)} {S : KRSForwardState m n},
        KRSForwardRun w S →
          generalizedPermutation.width w ≤ firstColumnHeight S.shape ∧
          firstColumnHeight S.shape ≤ generalizedPermutation.width w := by
    intro w S hrun
    induction hrun with
    | nil =>
        simp [KRSForwardState.empty, width_nil, firstColumnHeight_bot]
    | @snoc w S z hrun hsorted hrec hsame_next ih =>
        let R := rowInsert S.P z.2
        constructor
        · change generalizedPermutation.width (w ++ [z]) ≤
            firstColumnHeight R.shape
          by_cases hcol : R.newCell.2 = 0
          · have hwidth :
                generalizedPermutation.width (w ++ [z]) ≤
                  generalizedPermutation.width w + 1 :=
              width_append_singleton_le_succ_width_of_sorted hsorted
            have hheight : firstColumnHeight R.shape =
                firstColumnHeight S.shape + 1 := by
              simpa [R] using
                rowInsert_firstColumnHeight_eq_succ_of_newCell_col_zero S.P z.2 hcol
            omega
          · have hwidth_no_growth :
                generalizedPermutation.width (w ++ [z]) ≤
                  generalizedPermutation.width w := by
              apply width_append_singleton_le_of_ending_subseq_bound hsorted
              intro t ht_sub ht_pair
              have hshape_bound :
                  t.length + 1 ≤ firstColumnHeight R.shape := by
                simpa [R] using
                  krsForwardRun_descending_suffix_length_le_rowInsert_firstColumnHeight
                    hrun z ht_sub ht_pair
              have hheight' : firstColumnHeight R.shape = firstColumnHeight S.shape := by
                simpa [R] using
                  rowInsert_firstColumnHeight_eq_of_newCell_col_ne_zero S.P z.2 hcol
              exact le_trans (by simpa [hheight'] using hshape_bound) ih.2
            have hheight : firstColumnHeight R.shape =
                firstColumnHeight S.shape := by
              simpa [R] using
                rowInsert_firstColumnHeight_eq_of_newCell_col_ne_zero S.P z.2 hcol
            omega
        · change firstColumnHeight R.shape ≤
            generalizedPermutation.width (w ++ [z])
          by_cases hcol : R.newCell.2 = 0
          · have hheight : firstColumnHeight R.shape =
                firstColumnHeight S.shape + 1 := by
              simpa [R] using
                rowInsert_firstColumnHeight_eq_succ_of_newCell_col_zero S.P z.2 hcol
            have hwidth_growth :
                generalizedPermutation.width w + 1 ≤
                  generalizedPermutation.width (w ++ [z]) := by
              let tr := rowInsertionTrace S.P z.2
              rcases tr.exists_compressedBumpChain_length_eq_newCell_row with
                ⟨k, hkrow, hchain⟩
              have hkrow' : R.newCell.1 = k := by
                simpa [R, tr] using hkrow
              have hkheight : k = firstColumnHeight S.shape := by
                have hold := R.old_colLen_at_newCell
                rw [hcol] at hold
                dsimp [firstColumnHeight]
                omega
              rcases krsForwardRun_compressedBumpChain_exists_descending_sublist
                  hrun hchain with ⟨t, ht_sub, ht_len, ht_pair⟩
              have ht_sub_append :
                  List.Sublist (t ++ [z.2])
                    (generalizedPermutation.lowerWord (w ++ [z])) := by
                rw [lowerWord_append_singleton_of_sorted hsorted]
                exact ht_sub.append (List.Sublist.refl [z.2])
              have hlen :
                  (t ++ [z.2]).length ≤
                    generalizedPermutation.width (w ++ [z]) :=
                length_le_width_of_lowerWord_sublist_pairwise_gt
                  ht_sub_append ht_pair
              simp only [List.length_append, List.length_singleton] at hlen
              omega
            omega
          · have hheight : firstColumnHeight R.shape =
                firstColumnHeight S.shape := by
              simpa [R] using
                rowInsert_firstColumnHeight_eq_of_newCell_col_ne_zero S.P z.2 hcol
            have hwidth_mono :
                generalizedPermutation.width w ≤
                  generalizedPermutation.width (w ++ [z]) :=
              width_le_width_append_singleton_of_sorted hsorted
            omega
  have hwidth_le_height :
      ∀ {w : List (Fin m × Fin n)} {S : KRSForwardState m n},
        KRSForwardRun w S →
          generalizedPermutation.width w ≤ firstColumnHeight S.shape := by
    intro w S hrun
    exact (hboth hrun).1
  have hheight_le_width :
      ∀ {w : List (Fin m × Fin n)} {S : KRSForwardState m n},
        KRSForwardRun w S →
          firstColumnHeight S.shape ≤ generalizedPermutation.width w := by
    intro w S hrun
    exact (hboth hrun).2
  have hEq :
      generalizedPermutation.width W.1 =
        firstColumnHeight
          (krsForwardStateOfList W.1 W.2).shape := by
    exact le_antisymm
      (hwidth_le_height hrun)
      (hheight_le_width hrun)
  simpa [krsTableauPair, KRSForwardState.toTableauPair] using hEq

/-- The top row length is zero only for the empty diagram, so the first column is empty too. -/
private lemma colLen_zero_eq_zero_of_rowLen_zero {μ : YoungDiagram}
    (h : μ.rowLen 0 = 0) : μ.colLen 0 = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hcol
  have hcell : (0, 0) ∈ μ := by
    rwa [YoungDiagram.mem_iff_lt_colLen]
  have hrow : 0 < μ.rowLen 0 := by
    rwa [YoungDiagram.mem_iff_lt_rowLen] at hcell
  omega

/-- Summing column lengths over the nonempty columns counts all boxes of a Young diagram. -/
private lemma sum_colLen_eq_card (μ : YoungDiagram) :
    (∑ b : Fin (μ.rowLen 0), μ.colLen b.val) = μ.card := by
  classical
  have hmaps : ∀ c ∈ μ.cells, c.2 ∈ Finset.range (μ.rowLen 0) := by
    intro c hc
    rw [Finset.mem_range]
    have hcell : c ∈ μ := by
      simpa using hc
    have htop : (0, c.2) ∈ μ :=
      μ.up_left_mem (Nat.zero_le c.1) le_rfl hcell
    rwa [YoungDiagram.mem_iff_lt_rowLen] at htop
  have hcard :=
    Finset.card_eq_sum_card_fiberwise
      (s := μ.cells) (t := Finset.range (μ.rowLen 0)) (f := Prod.snd) hmaps
  rw [Fin.sum_univ_eq_sum_range (fun b => μ.colLen b)]
  change (∑ b ∈ Finset.range (μ.rowLen 0), μ.colLen b) = μ.cells.card
  rw [hcard]
  apply Finset.sum_congr rfl
  intro b hb
  rw [YoungDiagram.colLen_eq_card, YoungDiagram.col]

/-- The minor read from one column of a bounded semistandard tableau pair. -/
noncomputable def columnMinorIndex {m n : ℕ} (T : TableauPair m n)
    (b : Fin (T.shape.rowLen 0)) :
    MinorIndex m n (T.shape.colLen b.val) where
  row :=
    OrderEmbedding.ofStrictMono
      (fun a : Fin (T.shape.colLen b.val) =>
        ⟨T.Q.T a.val b.val,
          T.Q.bound (by
            rw [YoungDiagram.mem_iff_lt_colLen]
            exact a.isLt)⟩)
      (by
        intro a c hac
        rw [Fin.lt_def]
        exact T.Q.T.col_strict (Fin.lt_def.mp hac) (by
          rw [YoungDiagram.mem_iff_lt_colLen]
          exact c.isLt))
  col :=
    OrderEmbedding.ofStrictMono
      (fun a : Fin (T.shape.colLen b.val) =>
        ⟨T.P.T a.val b.val,
          T.P.bound (by
            rw [YoungDiagram.mem_iff_lt_colLen]
            exact a.isLt)⟩)
      (by
        intro a c hac
        rw [Fin.lt_def]
        exact T.P.T.col_strict (Fin.lt_def.mp hac) (by
          rw [YoungDiagram.mem_iff_lt_colLen]
          exact c.isLt))

/-- The raw bitableau obtained from a same-shape pair by reading columns as minors. -/
noncomputable def tableauPairToYoungBitableauRaw {m n : ℕ}
    (T : TableauPair m n) : YoungBitableau m n where
  v := T.shape.rowLen 0
  size := fun b => T.shape.colLen b.val
  size_pos := by
    intro b
    have hcell : (0, b.val) ∈ T.shape := by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      exact b.isLt
    rwa [YoungDiagram.mem_iff_lt_colLen] at hcell
  minorindex := columnMinorIndex T
  shape_antitone := by
    intro a b hab
    exact T.shape.colLen_anti a.val b.val (Fin.le_def.mp hab)

/-- Convert a KRS tableau pair to the Lean bitableau by reading tableau columns as minors. -/
noncomputable def tableauPairToYoungBitableau {m n : ℕ}
    (T : TableauPair m n) : StandardYoungBitableau m n :=
  ⟨tableauPairToYoungBitableauRaw T, by
    intro a b hnext j
    have hab : a.val ≤ b.val := by omega
    have hcell : (j.val, b.val) ∈ T.shape := by
      rw [YoungDiagram.mem_iff_lt_colLen]
      exact j.isLt
    constructor
    · rw [Fin.le_def]
      exact T.Q.T.row_weak_of_le hab hcell
    · rw [Fin.le_def]
      exact T.P.T.row_weak_of_le hab hcell⟩

/-- The Young diagram whose column heights are the sizes of the bitableau factors. -/
noncomputable def shapeOfBitableau {m n : ℕ} (B : YoungBitableau m n) :
    YoungDiagram where
  cells :=
    (Finset.univ : Finset (Fin B.v)).biUnion fun j =>
      (Finset.range (B.size j)).image fun i => (i, j.val)
  isLowerSet := by
    intro a b hab hb
    rcases Finset.mem_biUnion.mp hb with ⟨j, _hj, hjmem⟩
    rcases Finset.mem_image.mp hjmem with ⟨i, hi, hpair⟩
    have hb_fst : i = a.1 := congrArg Prod.fst hpair
    have hb_snd : j.val = a.2 := congrArg Prod.snd hpair
    have hb'_fst : b.1 ≤ i := by
      simpa [← hb_fst] using (Prod.mk_le_mk.mp hab).1
    have hb'_snd : b.2 ≤ j.val := by
      simpa [← hb_snd] using (Prod.mk_le_mk.mp hab).2
    let j' : Fin B.v := ⟨b.2, lt_of_le_of_lt hb'_snd j.isLt⟩
    refine Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨b.1, ?_, ?_⟩
    · rw [Finset.mem_range]
      exact lt_of_le_of_lt hb'_fst
        (lt_of_lt_of_le (Finset.mem_range.mp hi)
          (B.shape_antitone j' j (Fin.le_def.mpr hb'_snd)))
    · cases b
      rfl

private lemma mem_shapeOfBitableau_iff {m n : ℕ} (B : YoungBitableau m n)
    {i j : ℕ} :
    (i, j) ∈ shapeOfBitableau B ↔ ∃ hj : j < B.v, i < B.size ⟨j, hj⟩ := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨b, _hb, hbmem⟩
    rcases Finset.mem_image.mp hbmem with ⟨i', hi', hpair⟩
    have hi_eq : i' = i := congrArg Prod.fst hpair
    have hj_eq : b.val = j := congrArg Prod.snd hpair
    refine ⟨?_, ?_⟩
    · simp [← hj_eq]
    · subst i'
      subst j
      simpa using hi'
  · rintro ⟨hj, hi⟩
    refine Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

private lemma mem_shapeOf_tableauPairToYoungBitableauRaw_iff {m n : ℕ}
    (T : TableauPair m n) {i j : ℕ} :
    (i, j) ∈ shapeOfBitableau (tableauPairToYoungBitableauRaw T) ↔ (i, j) ∈ T.shape := by
  rw [mem_shapeOfBitableau_iff]
  constructor
  · rintro ⟨hj, hi⟩
    change i < T.shape.colLen j at hi
    rwa [YoungDiagram.mem_iff_lt_colLen]
  · intro hcell
    have htop : (0, j) ∈ T.shape :=
      T.shape.up_left_mem (Nat.zero_le i) le_rfl hcell
    have hj : j < (tableauPairToYoungBitableauRaw T).v := by
      change j < T.shape.rowLen 0
      rwa [YoungDiagram.mem_iff_lt_rowLen] at htop
    refine ⟨hj, ?_⟩
    change i < T.shape.colLen j
    rwa [← YoungDiagram.mem_iff_lt_colLen]

private lemma shapeOf_tableauPairToYoungBitableauRaw {m n : ℕ}
    (T : TableauPair m n) :
    shapeOfBitableau (tableauPairToYoungBitableauRaw T) = T.shape := by
  ext c
  exact mem_shapeOf_tableauPairToYoungBitableauRaw_iff T

private lemma shapeOfBitableau_rowLen_zero {m n : ℕ}
    (B : YoungBitableau m n) :
    (shapeOfBitableau B).rowLen 0 = B.v := by
  apply le_antisymm
  · apply Nat.le_of_not_gt
    intro hv
    have hcell : (0, B.v) ∈ shapeOfBitableau B := by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      exact hv
    rcases (mem_shapeOfBitableau_iff B).1 hcell with ⟨hj, _⟩
    exact (Nat.lt_irrefl B.v) hj
  · apply Nat.le_of_not_gt
    intro hrow
    let j : Fin B.v := ⟨(shapeOfBitableau B).rowLen 0, hrow⟩
    have hcell : (0, (shapeOfBitableau B).rowLen 0) ∈ shapeOfBitableau B :=
      (mem_shapeOfBitableau_iff B).2 ⟨j.isLt, B.size_pos j⟩
    have hlt : (shapeOfBitableau B).rowLen 0 < (shapeOfBitableau B).rowLen 0 := by
      rwa [YoungDiagram.mem_iff_lt_rowLen] at hcell
    exact (Nat.lt_irrefl _) hlt

private lemma shapeOfBitableau_colLen {m n : ℕ}
    (B : YoungBitableau m n) (j : Fin B.v) :
    (shapeOfBitableau B).colLen j.val = B.size j := by
  apply le_antisymm
  · apply Nat.le_of_not_gt
    intro hsize
    have hcell : (B.size j, j.val) ∈ shapeOfBitableau B := by
      rw [YoungDiagram.mem_iff_lt_colLen]
      exact hsize
    rcases (mem_shapeOfBitableau_iff B).1 hcell with ⟨hj, hi⟩
    have hj_eq : (⟨j.val, hj⟩ : Fin B.v) = j := by
      ext
      rfl
    simp [hj_eq] at hi
  · apply Nat.le_of_not_gt
    intro hcol
    have hcell : ((shapeOfBitableau B).colLen j.val, j.val) ∈ shapeOfBitableau B := by
      exact (mem_shapeOfBitableau_iff B).2 ⟨j.isLt, hcol⟩
    have hlt :
        (shapeOfBitableau B).colLen j.val < (shapeOfBitableau B).colLen j.val := by
      rwa [YoungDiagram.mem_iff_lt_colLen] at hcell
    exact (Nat.lt_irrefl _) hlt

/-- Row-tableau entry read from the row index of a bitableau minor. -/
noncomputable def bitableauRowEntry {m n : ℕ} (B : YoungBitableau m n)
    (i j : ℕ) : ℕ :=
  if hj : j < B.v then
    if hi : i < B.size ⟨j, hj⟩ then
      (B.minorindex ⟨j, hj⟩).row ⟨i, hi⟩
    else 0
  else 0

/-- Column-tableau entry read from the column index of a bitableau minor. -/
noncomputable def bitableauColEntry {m n : ℕ} (B : YoungBitableau m n)
    (i j : ℕ) : ℕ :=
  if hj : j < B.v then
    if hi : i < B.size ⟨j, hj⟩ then
      (B.minorindex ⟨j, hj⟩).col ⟨i, hi⟩
    else 0
  else 0

private lemma bitableauRowEntry_of_mem {m n : ℕ} (B : YoungBitableau m n)
    {i j : ℕ} (hj : j < B.v) (hi : i < B.size ⟨j, hj⟩) :
    bitableauRowEntry B i j =
      (B.minorindex ⟨j, hj⟩).row ⟨i, hi⟩ := by
  simp [bitableauRowEntry, hj, hi]

private lemma bitableauColEntry_of_mem {m n : ℕ} (B : YoungBitableau m n)
    {i j : ℕ} (hj : j < B.v) (hi : i < B.size ⟨j, hj⟩) :
    bitableauColEntry B i j =
      (B.minorindex ⟨j, hj⟩).col ⟨i, hi⟩ := by
  simp [bitableauColEntry, hj, hi]

private lemma bitableauRowEntry_tableauPairToYoungBitableauRaw {m n : ℕ}
    (T : TableauPair m n) (i j : ℕ) :
    bitableauRowEntry (tableauPairToYoungBitableauRaw T) i j = T.Q.T i j := by
  unfold bitableauRowEntry
  by_cases hj : j < (tableauPairToYoungBitableauRaw T).v
  · by_cases hi : i < (tableauPairToYoungBitableauRaw T).size ⟨j, hj⟩
    · have hj' : j < T.shape.rowLen 0 := by
        change j < T.shape.rowLen 0 at hj
        exact hj
      have hi' : i < T.shape.colLen j := by
        change i < T.shape.colLen j at hi
        exact hi
      simp [tableauPairToYoungBitableauRaw, columnMinorIndex, hj', hi']
    · have hnot : (i, j) ∉ T.shape := by
        intro hcell
        have hicol : i < T.shape.colLen j := by
          rwa [YoungDiagram.mem_iff_lt_colLen] at hcell
        exact hi (by
          change i < T.shape.colLen j
          exact hicol)
      simp [hj, hi, T.Q.T.zeros hnot]
  · have hnot : (i, j) ∉ T.shape := by
      intro hcell
      have htop : (0, j) ∈ T.shape :=
        T.shape.up_left_mem (Nat.zero_le i) le_rfl hcell
      have hj' : j < T.shape.rowLen 0 := by
        rwa [YoungDiagram.mem_iff_lt_rowLen] at htop
      exact hj (by
        change j < T.shape.rowLen 0
        exact hj')
    simp [hj, T.Q.T.zeros hnot]

private lemma bitableauColEntry_tableauPairToYoungBitableauRaw {m n : ℕ}
    (T : TableauPair m n) (i j : ℕ) :
    bitableauColEntry (tableauPairToYoungBitableauRaw T) i j = T.P.T i j := by
  unfold bitableauColEntry
  by_cases hj : j < (tableauPairToYoungBitableauRaw T).v
  · by_cases hi : i < (tableauPairToYoungBitableauRaw T).size ⟨j, hj⟩
    · have hj' : j < T.shape.rowLen 0 := by
        change j < T.shape.rowLen 0 at hj
        exact hj
      have hi' : i < T.shape.colLen j := by
        change i < T.shape.colLen j at hi
        exact hi
      simp [tableauPairToYoungBitableauRaw, columnMinorIndex, hj', hi']
    · have hnot : (i, j) ∉ T.shape := by
        intro hcell
        have hicol : i < T.shape.colLen j := by
          rwa [YoungDiagram.mem_iff_lt_colLen] at hcell
        exact hi (by
          change i < T.shape.colLen j
          exact hicol)
      simp [hj, hi, T.P.T.zeros hnot]
  · have hnot : (i, j) ∉ T.shape := by
      intro hcell
      have htop : (0, j) ∈ T.shape :=
        T.shape.up_left_mem (Nat.zero_le i) le_rfl hcell
      have hj' : j < T.shape.rowLen 0 := by
        rwa [YoungDiagram.mem_iff_lt_rowLen] at htop
      exact hj (by
        change j < T.shape.rowLen 0
        exact hj')
    simp [hj, T.P.T.zeros hnot]

private theorem youngBitableau_ext_cast {m n : ℕ} {B C : YoungBitableau m n}
    (hv : B.v = C.v)
    (hsize : ∀ c : Fin C.v, B.size (Fin.cast hv.symm c) = C.size c)
    (hminor : ∀ c : Fin C.v,
      HEq (B.minorindex (Fin.cast hv.symm c)) (C.minorindex c)) :
    B = C := by
  cases B with
  | mk vB sizeB size_posB minorindexB shape_antitoneB =>
      cases C with
      | mk vC sizeC size_posC minorindexC shape_antitoneC =>
          dsimp at hv hsize hminor
          cases hv
          have hsize_eq : sizeB = sizeC := by
            funext c
            exact hsize c
          cases hsize_eq
          have hminor_eq : minorindexB = minorindexC := by
            funext c
            exact eq_of_heq (hminor c)
          cases hminor_eq
          rfl

private theorem minorIndex_heq_of_cast_apply_eq {m n t u : ℕ} (h : t = u)
    {I : MinorIndex m n t} {J : MinorIndex m n u}
    (hrow : ∀ a : Fin u, I.row (Fin.cast h.symm a) = J.row a)
    (hcol : ∀ a : Fin u, I.col (Fin.cast h.symm a) = J.col a) :
    HEq I J := by
  cases h
  apply heq_of_eq
  cases I with
  | mk rowI colI =>
      cases J with
      | mk rowJ colJ =>
          dsimp at hrow hcol
          have hrow_eq : rowI = rowJ := by
            ext a
            exact congrArg Fin.val (hrow a)
          have hcol_eq : colI = colJ := by
            ext a
            exact congrArg Fin.val (hcol a)
          cases hrow_eq
          cases hcol_eq
          rfl

private lemma bitableauRowEntry_zero {m n : ℕ} (B : YoungBitableau m n)
    {i j : ℕ} (hcell : (i, j) ∉ shapeOfBitableau B) :
    bitableauRowEntry B i j = 0 := by
  unfold bitableauRowEntry
  by_cases hj : j < B.v
  · by_cases hi : i < B.size ⟨j, hj⟩
    · exact False.elim (hcell ((mem_shapeOfBitableau_iff B).2 ⟨hj, hi⟩))
    · simp [hj, hi]
  · simp [hj]

private lemma bitableauColEntry_zero {m n : ℕ} (B : YoungBitableau m n)
    {i j : ℕ} (hcell : (i, j) ∉ shapeOfBitableau B) :
    bitableauColEntry B i j = 0 := by
  unfold bitableauColEntry
  by_cases hj : j < B.v
  · by_cases hi : i < B.size ⟨j, hj⟩
    · exact False.elim (hcell ((mem_shapeOfBitableau_iff B).2 ⟨hj, hi⟩))
    · simp [hj, hi]
  · simp [hj]

private lemma bitableauRowEntry_row_weak_succ {m n : ℕ}
    (B : StandardYoungBitableau m n) {i j : ℕ}
    (hcell : (i, j + 1) ∈ shapeOfBitableau B.1) :
    bitableauRowEntry B.1 i j ≤ bitableauRowEntry B.1 i (j + 1) := by
  rcases (mem_shapeOfBitableau_iff B.1).1 hcell with ⟨hj_next, hi_next⟩
  have hj_cur : j < B.1.v := Nat.lt_of_succ_lt hj_next
  let a : Fin B.1.v := ⟨j, hj_cur⟩
  let b : Fin B.1.v := ⟨j + 1, hj_next⟩
  have hnext : a.val + 1 = b.val := rfl
  have hsize : B.1.size b ≤ B.1.size a :=
    B.1.shape_antitone a b (by simp [a, b])
  have hi_cur : i < B.1.size a := lt_of_lt_of_le hi_next hsize
  have hstandard := B.2 a b hnext ⟨i, hi_next⟩
  rw [bitableauRowEntry_of_mem B.1 hj_cur hi_cur,
    bitableauRowEntry_of_mem B.1 hj_next hi_next]
  exact hstandard.1

private lemma bitableauColEntry_row_weak_succ {m n : ℕ}
    (B : StandardYoungBitableau m n) {i j : ℕ}
    (hcell : (i, j + 1) ∈ shapeOfBitableau B.1) :
    bitableauColEntry B.1 i j ≤ bitableauColEntry B.1 i (j + 1) := by
  rcases (mem_shapeOfBitableau_iff B.1).1 hcell with ⟨hj_next, hi_next⟩
  have hj_cur : j < B.1.v := Nat.lt_of_succ_lt hj_next
  let a : Fin B.1.v := ⟨j, hj_cur⟩
  let b : Fin B.1.v := ⟨j + 1, hj_next⟩
  have hnext : a.val + 1 = b.val := rfl
  have hsize : B.1.size b ≤ B.1.size a :=
    B.1.shape_antitone a b (by simp [a, b])
  have hi_cur : i < B.1.size a := lt_of_lt_of_le hi_next hsize
  have hstandard := B.2 a b hnext ⟨i, hi_next⟩
  rw [bitableauColEntry_of_mem B.1 hj_cur hi_cur,
    bitableauColEntry_of_mem B.1 hj_next hi_next]
  exact hstandard.2

private lemma bitableauRowEntry_row_weak {m n : ℕ}
    (B : StandardYoungBitableau m n) {i j₁ j₂ : ℕ}
    (hj : j₁ < j₂) (hcell : (i, j₂) ∈ shapeOfBitableau B.1) :
    bitableauRowEntry B.1 i j₁ ≤ bitableauRowEntry B.1 i j₂ := by
  revert j₁ hcell hj
  induction j₂ with
  | zero =>
      intro j₁ hj hcell
      omega
  | succ j₂ ih =>
      intro j₁ hj hcell
      by_cases hlast : j₁ = j₂
      · subst j₁
        exact bitableauRowEntry_row_weak_succ B hcell
      · have hj' : j₁ < j₂ := by omega
        have hcell' : (i, j₂) ∈ shapeOfBitableau B.1 :=
          (shapeOfBitableau B.1).up_left_mem le_rfl (Nat.le_succ j₂) hcell
        exact le_trans (ih hj' hcell') (bitableauRowEntry_row_weak_succ B hcell)

private lemma bitableauColEntry_row_weak {m n : ℕ}
    (B : StandardYoungBitableau m n) {i j₁ j₂ : ℕ}
    (hj : j₁ < j₂) (hcell : (i, j₂) ∈ shapeOfBitableau B.1) :
    bitableauColEntry B.1 i j₁ ≤ bitableauColEntry B.1 i j₂ := by
  revert j₁ hcell hj
  induction j₂ with
  | zero =>
      intro j₁ hj hcell
      omega
  | succ j₂ ih =>
      intro j₁ hj hcell
      by_cases hlast : j₁ = j₂
      · subst j₁
        exact bitableauColEntry_row_weak_succ B hcell
      · have hj' : j₁ < j₂ := by omega
        have hcell' : (i, j₂) ∈ shapeOfBitableau B.1 :=
          (shapeOfBitableau B.1).up_left_mem le_rfl (Nat.le_succ j₂) hcell
        exact le_trans (ih hj' hcell') (bitableauColEntry_row_weak_succ B hcell)

private lemma bitableauRowEntry_col_strict {m n : ℕ}
    (B : YoungBitableau m n) {i₁ i₂ j : ℕ}
    (hi : i₁ < i₂) (hcell : (i₂, j) ∈ shapeOfBitableau B) :
    bitableauRowEntry B i₁ j < bitableauRowEntry B i₂ j := by
  rcases (mem_shapeOfBitableau_iff B).1 hcell with ⟨hj, hi₂⟩
  have hi₁ : i₁ < B.size ⟨j, hj⟩ := lt_trans hi hi₂
  rw [bitableauRowEntry_of_mem B hj hi₁, bitableauRowEntry_of_mem B hj hi₂]
  exact (B.minorindex ⟨j, hj⟩).row.strictMono hi

private lemma bitableauColEntry_col_strict {m n : ℕ}
    (B : YoungBitableau m n) {i₁ i₂ j : ℕ}
    (hi : i₁ < i₂) (hcell : (i₂, j) ∈ shapeOfBitableau B) :
    bitableauColEntry B i₁ j < bitableauColEntry B i₂ j := by
  rcases (mem_shapeOfBitableau_iff B).1 hcell with ⟨hj, hi₂⟩
  have hi₁ : i₁ < B.size ⟨j, hj⟩ := lt_trans hi hi₂
  rw [bitableauColEntry_of_mem B hj hi₁, bitableauColEntry_of_mem B hj hi₂]
  exact (B.minorindex ⟨j, hj⟩).col.strictMono hi

/-- The row-index tableau associated to a standard bitableau. -/
noncomputable def rowBoundedSSYTOfBitableau {m n : ℕ}
    (B : StandardYoungBitableau m n) :
    BoundedSSYT (shapeOfBitableau B.1) m where
  T :=
    { entry := bitableauRowEntry B.1
      row_weak' := bitableauRowEntry_row_weak B
      col_strict' := bitableauRowEntry_col_strict B.1
      zeros' := by
        intro i j hcell
        exact bitableauRowEntry_zero B.1 hcell }
  bound := by
    intro i j hcell
    rcases (mem_shapeOfBitableau_iff B.1).1 hcell with ⟨hj, hi⟩
    change bitableauRowEntry B.1 i j < m
    rw [bitableauRowEntry_of_mem B.1 hj hi]
    exact ((B.1.minorindex ⟨j, hj⟩).row ⟨i, hi⟩).isLt

/-- The column-index tableau associated to a standard bitableau. -/
noncomputable def colBoundedSSYTOfBitableau {m n : ℕ}
    (B : StandardYoungBitableau m n) :
    BoundedSSYT (shapeOfBitableau B.1) n where
  T :=
    { entry := bitableauColEntry B.1
      row_weak' := bitableauColEntry_row_weak B
      col_strict' := bitableauColEntry_col_strict B.1
      zeros' := by
        intro i j hcell
        exact bitableauColEntry_zero B.1 hcell }
  bound := by
    intro i j hcell
    rcases (mem_shapeOfBitableau_iff B.1).1 hcell with ⟨hj, hi⟩
    change bitableauColEntry B.1 i j < n
    rw [bitableauColEntry_of_mem B.1 hj hi]
    exact ((B.1.minorindex ⟨j, hj⟩).col ⟨i, hi⟩).isLt

/-- Convert a standard Lean bitableau back to a same-shape semistandard tableau pair. -/
noncomputable def youngBitableauToTableauPair {m n : ℕ}
    (B : StandardYoungBitableau m n) : TableauPair m n where
  shape := shapeOfBitableau B.1
  P := colBoundedSSYTOfBitableau B
  Q := rowBoundedSSYTOfBitableau B

/-- Converting a tableau pair to a bitableau and back recovers the underlying shape. -/
theorem youngBitableauToTableauPair_tableauPairToYoungBitableau_shape
    {m n : ℕ} (T : TableauPair m n) :
    (youngBitableauToTableauPair (tableauPairToYoungBitableau T)).shape = T.shape :=
  shapeOf_tableauPairToYoungBitableauRaw T

/-- Converting a tableau pair to a bitableau and back recovers the lower tableau entries. -/
theorem youngBitableauToTableauPair_tableauPairToYoungBitableau_P_entry
    {m n : ℕ} (T : TableauPair m n) (i j : ℕ) :
    (youngBitableauToTableauPair (tableauPairToYoungBitableau T)).P.T i j =
      T.P.T i j :=
  bitableauColEntry_tableauPairToYoungBitableauRaw T i j

/-- Converting a tableau pair to a bitableau and back recovers the recording tableau entries. -/
theorem youngBitableauToTableauPair_tableauPairToYoungBitableau_Q_entry
    {m n : ℕ} (T : TableauPair m n) (i j : ℕ) :
    (youngBitableauToTableauPair (tableauPairToYoungBitableau T)).Q.T i j =
      T.Q.T i j :=
  bitableauRowEntry_tableauPairToYoungBitableauRaw T i j

/-- The tableau-pair to bitableau conversion is left-inverse to the reconstruction.

This packages the shape and entrywise bridge lemmas above into the dependent structure equality.
The proof is mostly cast management for `BoundedSSYT` over equal `YoungDiagram`s. -/
theorem youngBitableauToTableauPair_tableauPairToYoungBitableau
    {m n : ℕ} :
    Function.LeftInverse
      (fun B : StandardYoungBitableau m n => youngBitableauToTableauPair B)
      (fun T : TableauPair m n => tableauPairToYoungBitableau T) := by
  intro T
  let S := youngBitableauToTableauPair (tableauPairToYoungBitableau T)
  change S = T
  have hshape : S.shape = T.shape :=
    youngBitableauToTableauPair_tableauPairToYoungBitableau_shape T
  refine TableauPair.ext_heq hshape ?_ ?_
  · apply BoundedSSYT.heq_of_entry_eq hshape
    intro i j
    simpa [S] using
      youngBitableauToTableauPair_tableauPairToYoungBitableau_P_entry T i j
  · apply BoundedSSYT.heq_of_entry_eq hshape
    intro i j
    simpa [S] using
      youngBitableauToTableauPair_tableauPairToYoungBitableau_Q_entry T i j

/-- Reconstructing a tableau pair from a standard bitableau and reading columns returns the
original standard bitableau. -/
theorem tableauPairToYoungBitableau_youngBitableauToTableauPair
    {m n : ℕ} :
    Function.RightInverse
      (fun B : StandardYoungBitableau m n => youngBitableauToTableauPair B)
      (fun T : TableauPair m n => tableauPairToYoungBitableau T) := by
  intro B
  apply Subtype.ext
  cases B with
  | mk B hstd =>
      cases B with
      | mk v size size_pos minorindex shape_antitone =>
          let Braw : YoungBitableau m n :=
            { v := v
              size := size
              size_pos := size_pos
              minorindex := minorindex
              shape_antitone := shape_antitone }
          change
            tableauPairToYoungBitableauRaw
                (youngBitableauToTableauPair ⟨Braw, hstd⟩) =
              Braw
          refine youngBitableau_ext_cast
            (B := tableauPairToYoungBitableauRaw
              (youngBitableauToTableauPair ⟨Braw, hstd⟩))
            (C := Braw)
            (shapeOfBitableau_rowLen_zero Braw) ?_ ?_
          · intro c
            simp [tableauPairToYoungBitableauRaw, youngBitableauToTableauPair,
              shapeOfBitableau_colLen, Braw]
          · intro c
            have hsize :
                (tableauPairToYoungBitableauRaw
                    (youngBitableauToTableauPair ⟨Braw, hstd⟩)).size
                    (Fin.cast (shapeOfBitableau_rowLen_zero Braw).symm c) =
                  Braw.size c := by
              simp [tableauPairToYoungBitableauRaw, youngBitableauToTableauPair,
                shapeOfBitableau_colLen, Braw]
            change HEq
              (columnMinorIndex
                { shape := shapeOfBitableau Braw
                  P := colBoundedSSYTOfBitableau ⟨Braw, hstd⟩
                  Q := rowBoundedSSYTOfBitableau ⟨Braw, hstd⟩ }
                (Fin.cast (shapeOfBitableau_rowLen_zero Braw).symm c))
              (minorindex c)
            rcases hI : minorindex c with ⟨rowI, colI⟩
            apply minorIndex_heq_of_cast_apply_eq hsize
            · intro a
              apply Fin.ext
              change bitableauRowEntry Braw a.val c.val = (rowI a).val
              rw [bitableauRowEntry_of_mem Braw c.isLt a.isLt]
              simp [Braw, hI]
            · intro a
              apply Fin.ext
              change bitableauColEntry Braw a.val c.val = (colI a).val
              rw [bitableauColEntry_of_mem Braw c.isLt a.isLt]
              simp [Braw, hI]

/-- The column conversion produces a standard Young bitableau. -/
theorem tableauPair_to_youngBitableau_isStandard {m n : ℕ}
    (T : TableauPair m n) :
    YoungBitableau.IsStandard (tableauPairToYoungBitableau T).1 := by
  exact (tableauPairToYoungBitableau T).2

/-- The degree of the column bitableau is the number of boxes of the common shape. -/
theorem tableauPair_to_youngBitableau_degree {m n : ℕ}
    (T : TableauPair m n) :
    YoungBitableau.degree (tableauPairToYoungBitableau T).1 =
      T.shape.card := by
  simp [tableauPairToYoungBitableau, tableauPairToYoungBitableauRaw,
    YoungBitableau.degree, sum_colLen_eq_card]

/-- The length of the column bitableau is the first-column height of the KRS shape. -/
theorem tableauPair_to_youngBitableau_length {m n : ℕ}
    (T : TableauPair m n) :
    YoungBitableau.length (tableauPairToYoungBitableau T).1 =
      firstColumnHeight T.shape := by
  by_cases hrow : 0 < T.shape.rowLen 0
  · rw [YoungBitableau.length_eq_size_zero _ hrow]
    simp [tableauPairToYoungBitableau, tableauPairToYoungBitableauRaw, firstColumnHeight]
  · have hrow_zero : T.shape.rowLen 0 = 0 := by omega
    have hcol_zero : T.shape.colLen 0 = 0 :=
      colLen_zero_eq_zero_of_rowLen_zero hrow_zero
    change
      Finset.univ.sup (fun b : Fin (T.shape.rowLen 0) => T.shape.colLen b.val) =
        T.shape.colLen 0
    rw [hcol_zero]
    apply le_antisymm
    · apply Finset.sup_le
      intro b _
      exact Fin.elim0 (hrow_zero ▸ b)
    · exact Nat.zero_le _

/-- Convert a generalized permutation to its exponent-vector multiplicity function. -/
noncomputable def biwordToMonomialExp {m n : ℕ}
    (W : Biword m n) : (Fin m × Fin n) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => W.1.count p

/-- The expanded list of a monomial exponent vector has length equal to total degree. -/
lemma indicesOfMonomialExp_length_eq_degree {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) :
    (generalizedPermutation.indicesOfMonomialExp E).length = Finsupp.degree E := by
  classical
  rw [Finsupp.degree_eq_sum]
  rw [generalizedPermutation.indicesOfMonomialExp]
  simp only [List.length_flatMap, List.length_replicate]
  calc
    (List.map
        (fun i : Fin m =>
          (List.map (fun j : Fin n => E (i, j)) (List.finRange n)).sum)
        (List.finRange m)).sum
        = ∑ i : Fin m,
            (List.map (fun j : Fin n => E (i, j)) (List.finRange n)).sum := by
          simpa [Function.comp_def] using
            (Fin.sum_univ_def
              (fun i : Fin m =>
                (List.map (fun j : Fin n => E (i, j)) (List.finRange n)).sum)).symm
    _   = ∑ i : Fin m, ∑ j : Fin n, E (i, j) := by
          apply Finset.sum_congr rfl
          intro i _
          simpa [Function.comp_def] using
            (Fin.sum_univ_def (fun j : Fin n => E (i, j))).symm
    _ = ∑ p : Fin m × Fin n, E p := by
          rw [← Finset.sum_product' Finset.univ Finset.univ]
          simp

/-- The expanded biword has length equal to the total degree of the exponent vector. -/
theorem expandedBiword_length_eq_degree {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) :
    (expandedBiword E).1.length = Finsupp.degree E := by
  dsimp [expandedBiword]
  rw [(generalizedPermutation.generalizedPermutation_perm
    (generalizedPermutation.indicesOfMonomialExp E)).length_eq]
  exact indicesOfMonomialExp_length_eq_degree E

/-- The width computed from the sorted expanded biword is the monomial width. -/
theorem expandedBiword_width_eq_monomialWidth {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) :
    generalizedPermutation.width (expandedBiword E).1 = monomialWidth E := by
  classical
  let xs := generalizedPermutation.indicesOfMonomialExp E
  have hsort :
      Determinantal.generalizedPermutation
          (Determinantal.generalizedPermutation xs) =
        Determinantal.generalizedPermutation xs := by
    exact generalizedPermutation.generalizedPermutation_unique
      (xs := Determinantal.generalizedPermutation xs)
      (w₁ := Determinantal.generalizedPermutation
        (Determinantal.generalizedPermutation xs))
      (w₂ := Determinantal.generalizedPermutation xs)
      (generalizedPermutation.generalizedPermutation_perm
        (Determinantal.generalizedPermutation xs))
      (generalizedPermutation.generalizedPermutation_sorted
        (Determinantal.generalizedPermutation xs))
      (List.Perm.refl _)
      (generalizedPermutation.generalizedPermutation_sorted xs)
  simp [expandedBiword, monomialWidth, generalizedPermutation.width,
    generalizedPermutation.lowerWord, xs, hsort]

/-- The expanded biword and the exponent vector contain the same multiplicities. -/
theorem biwordToMonomialExp_expandedBiword {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) :
    biwordToMonomialExp (expandedBiword E) = E := by
  classical
  ext p
  simp [biwordToMonomialExp, expandedBiword,
    (generalizedPermutation.generalizedPermutation_perm
      (generalizedPermutation.indicesOfMonomialExp E)).count_eq,
    generalizedPermutation.count_indicesOfMonomialExp]

/-- The multiplicity list reconstructed from a biword has the same counts as the biword. -/
lemma indicesOfMonomialExp_biwordToMonomialExp_count {m n : ℕ}
    (W : Biword m n) (p : Fin m × Fin n) :
    (generalizedPermutation.indicesOfMonomialExp (biwordToMonomialExp W)).count p =
      W.1.count p := by
  classical
  rw [generalizedPermutation.count_indicesOfMonomialExp]
  simp [biwordToMonomialExp]

/-- Expanding the exponent vector associated to an already sorted biword recovers that biword. -/
theorem expandedBiword_biwordToMonomialExp {m n : ℕ}
    (W : Biword m n) :
    expandedBiword (biwordToMonomialExp W) = W := by
  classical
  apply Subtype.ext
  let xs :=
    generalizedPermutation.indicesOfMonomialExp (biwordToMonomialExp W)
  have hperm : xs.Perm W.1 := by
    rw [List.perm_iff_count]
    intro p
    exact indicesOfMonomialExp_biwordToMonomialExp_count W p
  change Determinantal.generalizedPermutation xs = W.1
  exact generalizedPermutation.generalizedPermutation_unique
    (xs := xs)
    (w₁ := Determinantal.generalizedPermutation xs)
    (w₂ := W.1)
    (generalizedPermutation.generalizedPermutation_perm xs)
    (generalizedPermutation.generalizedPermutation_sorted xs)
    hperm.symm
    W.2

/-- Exponent vectors and sorted generalized permutations carry the same multiplicity data. -/
noncomputable def monomialExpEquivBiword (m n : ℕ) :
    ((Fin m × Fin n) →₀ ℕ) ≃ Biword m n :=
  { toFun := expandedBiword
    invFun := biwordToMonomialExp
    left_inv := biwordToMonomialExp_expandedBiword
    right_inv := expandedBiword_biwordToMonomialExp }

/-- Same-shape bounded semistandard tableau pairs are equivalent to standard Young bitableaux
via column reading. -/
noncomputable def tableauPairEquivYoungBitableau (m n : ℕ) :
    TableauPair m n ≃ StandardYoungBitableau m n :=
  { toFun := fun T => tableauPairToYoungBitableau T
    invFun := fun B => youngBitableauToTableauPair B
    left_inv := youngBitableauToTableauPair_tableauPairToYoungBitableau
    right_inv := tableauPairToYoungBitableau_youngBitableauToTableauPair }

/-- Forward KRS map from monomial exponent vectors to standard Young bitableaux. -/
noncomputable def forward {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) : StandardYoungBitableau m n :=
  tableauPairToYoungBitableau
    (krsTableauPair (expandedBiword E))

/-- Inverse KRS map from standard Young bitableaux to monomial exponent vectors. -/
noncomputable def inverse {m n : ℕ}
    (B : StandardYoungBitableau m n) : (Fin m × Fin n) →₀ ℕ :=
  biwordToMonomialExp
    (reverseKrsBiword
      (youngBitableauToTableauPair B))

/-- Left inverse statement for the KRS equivalence. -/
theorem krs_left_inverse {m n : ℕ} :
    Function.LeftInverse
      (fun B : StandardYoungBitableau m n => inverse B)
      (fun E : (Fin m × Fin n) →₀ ℕ => forward E) := by
  intro E
  change inverse (forward E) = E
  unfold inverse forward
  have htableau :=
    youngBitableauToTableauPair_tableauPairToYoungBitableau
      (krsTableauPair (expandedBiword E))
  change
    youngBitableauToTableauPair
        (tableauPairToYoungBitableau (krsTableauPair (expandedBiword E))) =
      krsTableauPair (expandedBiword E) at htableau
  have hkrs := reverse_krs_krs (expandedBiword E)
  change reverseKrsBiword (krsTableauPair (expandedBiword E)) =
    expandedBiword E at hkrs
  rw [htableau, hkrs]
  exact biwordToMonomialExp_expandedBiword E

/-- Right inverse statement for the KRS equivalence. -/
theorem krs_right_inverse {m n : ℕ} :
    Function.RightInverse
      (fun B : StandardYoungBitableau m n => inverse B)
      (fun E : (Fin m × Fin n) →₀ ℕ => forward E) := by
  intro B
  change forward (inverse B) = B
  unfold inverse forward
  have hkrs := krs_reverse_krs (youngBitableauToTableauPair B)
  change krsTableauPair (reverseKrsBiword (youngBitableauToTableauPair B)) =
    youngBitableauToTableauPair B at hkrs
  rw [expandedBiword_biwordToMonomialExp, hkrs]
  exact tableauPairToYoungBitableau_youngBitableauToTableauPair B

/-- The Knuth-Robinson-Schensted correspondence as a Lean equivalence.

It sends monomial exponent vectors in the variables of the generic `m × n` matrix to standard
Young bitableaux, with inverse given by reverse KRS. -/
noncomputable def krsEquiv (m n : ℕ) :
    ((Fin m × Fin n) →₀ ℕ) ≃ StandardYoungBitableau m n :=
  { toFun := fun E => forward E
    invFun := fun B => inverse B
    left_inv := krs_left_inverse
    right_inv := krs_right_inverse }

/-- KRS preserves total degree. -/
theorem krs_degree {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) :
    YoungBitableau.degree ((krsEquiv m n E).1) =
      Finsupp.degree E := by
  change
    YoungBitableau.degree
        (tableauPairToYoungBitableau
          (krsTableauPair (expandedBiword E))).1 =
      Finsupp.degree E
  rw [tableauPair_to_youngBitableau_degree, krs_shape_numBoxes]
  exact expandedBiword_length_eq_degree E

/-- KRS sends monomial width to bitableau length. -/
theorem krs_width {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) :
    monomialWidth E =
      YoungBitableau.length ((krsEquiv m n E).1) := by
  change
    monomialWidth E =
      YoungBitableau.length
        (tableauPairToYoungBitableau
          (krsTableauPair (expandedBiword E))).1
  rw [← expandedBiword_width_eq_monomialWidth E, tableauPair_to_youngBitableau_length]
  exact schensted_lds_eq_firstColumnHeight (expandedBiword E)

end KRS

/-!
KRS is reopened here for public consequences phrased in terms of
`YoungBitableau`, after the main forward/reverse algorithm has been built.
-/

namespace KRS

/-- Public cell characterization for the Young diagram attached to a bitableau. -/
lemma shapeOfBitableau_mem_iff
    {m n : ℕ} (B : YoungBitableau m n) {i j : ℕ} :
    (i, j) ∈ shapeOfBitableau B ↔
      ∃ hj : j < B.v, i < B.size ⟨j, hj⟩ :=
  mem_shapeOfBitableau_iff B

/-- In one reverse-KRS step applied to the tableau pair of a standard bitableau,
the upper letter is one of the row indices in the original minor factor
corresponding to the selected column of the bitableau shape. -/
lemma reverseKrsStep_youngBitableau_letter_upper_factor
    {m n : ℕ}
    (B : StandardYoungBitableau m n)
    (h : (youngBitableauToTableauPair B).shape.card ≠ 0) :
    ∃ a : Fin B.1.v, ∃ i : Fin (B.1.size a),
      (reverseKrsStep (youngBitableauToTableauPair B) h).letter.1 =
        (B.1.minorindex a).row i ∧
      (maxRecordingCorner (youngBitableauToTableauPair B) h).cell =
        (i.val, a.val) := by
  classical
  let T := youngBitableauToTableauPair B
  let C := maxRecordingCorner T h
  have hcell : C.cell ∈ shapeOfBitableau B.1 := by
    simpa [T, youngBitableauToTableauPair] using C.cell_mem
  rcases (mem_shapeOfBitableau_iff B.1).1 hcell with ⟨hj, hi⟩
  let a : Fin B.1.v := ⟨C.cell.2, hj⟩
  let i : Fin (B.1.size a) := ⟨C.cell.1, by simpa [a] using hi⟩
  refine ⟨a, i, ?_, ?_⟩
  · apply Fin.ext
    rw [reverseKrsStep_letter_upper_eq_corner]
    change bitableauRowEntry B.1 C.cell.1 C.cell.2 =
      ((B.1.minorindex a).row i).val
    rw [bitableauRowEntry_of_mem B.1 hj hi]
  · simp [T, C, a, i]

/-- In one reverse-KRS step from a standard bitableau, the selected upper
letter identifies a row of a minor factor, and the ejected lower letter is
bounded by the column entry in the same selected cell. -/
lemma reverseKrsStep_youngBitableau_letter_lower_le_selected_col
    {m n : ℕ}
    (B : StandardYoungBitableau m n)
    (h : (youngBitableauToTableauPair B).shape.card ≠ 0) :
    ∃ a : Fin B.1.v, ∃ i : Fin (B.1.size a),
      (reverseKrsStep (youngBitableauToTableauPair B) h).letter.1 =
        (B.1.minorindex a).row i ∧
      (reverseKrsStep (youngBitableauToTableauPair B) h).letter.2.val ≤
        ((B.1.minorindex a).col i).val ∧
      (maxRecordingCorner (youngBitableauToTableauPair B) h).cell =
        (i.val, a.val) := by
  classical
  let T := youngBitableauToTableauPair B
  let C := maxRecordingCorner T h
  rcases reverseKrsStep_youngBitableau_letter_upper_factor B h with
    ⟨a, i, hupper, hcell⟩
  refine ⟨a, i, hupper, ?_, hcell⟩
  have hlower :
      (reverseKrsStep T h).letter.2.val ≤ T.P.T C.cell.1 C.cell.2 := by
    simpa [T, C] using reverseKrsStep_letter_lower_le_deleted_P_entry T h
  have hcell_mem : C.cell ∈ shapeOfBitableau B.1 := by
    simpa [T, youngBitableauToTableauPair] using C.cell_mem
  rcases (mem_shapeOfBitableau_iff B.1).1 hcell_mem with ⟨hj, hi⟩
  have hP :
      T.P.T C.cell.1 C.cell.2 =
        ((B.1.minorindex a).col i).val := by
    change bitableauColEntry B.1 C.cell.1 C.cell.2 =
      ((B.1.minorindex a).col i).val
    rw [bitableauColEntry_of_mem B.1 hj hi]
    have hC : C.cell = (i.val, a.val) := by
      simpa [T, C] using hcell
    have ha : (⟨C.cell.2, hj⟩ : Fin B.1.v) = a := by
      apply Fin.ext
      exact congrArg Prod.snd hC
    subst a
    have hi_eq :
        (⟨C.cell.1, hi⟩ : Fin (B.1.size ⟨C.cell.2, hj⟩)) = i := by
      apply Fin.ext
      exact congrArg Prod.fst hC
    rw [hi_eq]
  exact le_trans hlower (le_of_eq hP)

end KRS

/--
Proposition 2, KRS correspondence.

There exists a bijection from monomial exponent vectors to standard Young
bitableaux, preserving total degree and sending monomial width to bitableau length.
-/
theorem exists_krsEquiv
    (m n : ℕ) :
    ∃ κ :
      ((Fin m × Fin n) →₀ ℕ) ≃
        StandardYoungBitableau m n,
      (∀ E : (Fin m × Fin n) →₀ ℕ,
        YoungBitableau.degree ((κ E).1) =
          Finsupp.degree E)
      ∧
      (∀ E : (Fin m × Fin n) →₀ ℕ,
        monomialWidth E =
          YoungBitableau.length ((κ E).1)) := by
  exact ⟨KRS.krsEquiv m n, KRS.krs_degree, KRS.krs_width⟩

/--
Degree-fixed version of the KRS correspondence.
-/
theorem exists_krsEquiv_of_degree
    (m n d : ℕ) :
    ∃ κ :
      { E : (Fin m × Fin n) →₀ ℕ //
          Finsupp.degree E = d } ≃
        { B : StandardYoungBitableau m n //
          YoungBitableau.degree B.1 = d },
      ∀ E,
        monomialWidth E.1 =
          YoungBitableau.length ((κ E).1.1) := by
  rcases exists_krsEquiv m n with ⟨κ, hdeg, hwidth⟩
  let κd :
      { E : (Fin m × Fin n) →₀ ℕ //
          Finsupp.degree E = d } ≃
        { B : StandardYoungBitableau m n //
          YoungBitableau.degree B.1 = d } :=
    κ.subtypeEquiv
      (p := fun E => Finsupp.degree E = d)
      (q := fun B => YoungBitableau.degree B.1 = d)
      (by
        intro E
        constructor
        · intro hE
          simpa [hdeg E] using hE
        · intro hB
          simpa [hdeg E] using hB)
  refine ⟨κd, ?_⟩
  intro E
  simpa [κd] using hwidth E.1

/--
Degree- and width-filtered form of the KRS correspondence.

For a fixed degree `d`, KRS restricts to a bijection between monomials of
width at most `r` and standard bitableaux of degree `d` and length at most `r`.
-/
theorem exists_krsEquiv_of_degree_widthLE
    (m n r d : ℕ) :
    ∃ _κ :
      { E : (Fin m × Fin n) →₀ ℕ //
          Finsupp.degree E = d ∧ monomialWidth E ≤ r } ≃
        { B : StandardYoungBitableauOfLengthLE m n r //
          YoungBitableau.degree B.1.1 = d },
      True := by
  classical
  rcases exists_krsEquiv_of_degree m n d with ⟨κd, hwidth⟩
  refine ⟨?_, trivial⟩
  refine
  { toFun := ?toFun
    invFun := ?invFun
    left_inv := ?left_inv
    right_inv := ?right_inv }
  · intro E
    let E' : { E : (Fin m × Fin n) →₀ ℕ // Finsupp.degree E = d } :=
      ⟨E.1, E.2.1⟩
    refine ⟨⟨(κd E').1, ?_⟩, (κd E').2⟩
    simpa [E', hwidth E'] using E.2.2
  · intro B
    let B' : { B : StandardYoungBitableau m n //
        YoungBitableau.degree B.1 = d } :=
      ⟨B.1.1, B.2⟩
    let E' : { E : (Fin m × Fin n) →₀ ℕ // Finsupp.degree E = d } :=
      κd.symm B'
    refine ⟨E'.1, E'.2, ?_⟩
    have hκ : κd E' = B' := by
      simp [E', B']
    have hw := hwidth E'
    rw [hκ] at hw
    simpa [B'] using hw.symm ▸ B.1.2
  · intro E
    ext
    simp
  · intro B
    ext
    simp

/-- Cardinality form of the degree- and width-filtered KRS correspondence. -/
theorem natCard_standardBitableau_lengthLE_degree_eq_monomial_widthLE
    (m n r d : ℕ) :
    Nat.card
      { B : StandardYoungBitableauOfLengthLE m n r //
          YoungBitableau.degree B.1.1 = d }
      =
    Nat.card
      { E : (Fin m × Fin n) →₀ ℕ //
          Finsupp.degree E = d ∧ monomialWidth E ≤ r } := by
  rcases exists_krsEquiv_of_degree_widthLE m n r d with ⟨κ, _⟩
  exact (Nat.card_congr κ).symm

/-- Linear independence of standard bitableau polynomials implies uniqueness of the
polynomial part of a straightening expansion. -/
theorem straightening_law_unique_of_linearIndependent
    {m n : ℕ}
    (k : Type*) [Field k]
    (hli :
      LinearIndependent k
        (fun S : StandardYoungBitableau m n =>
          YoungBitableau.toPolynomial k S.1))
    (B : YoungBitableau m n) :
    ∀ c d : StandardYoungBitableau m n →₀ k,
      YoungBitableau.toPolynomial k B
        =
      c.sum (fun S a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k S.1) →
      YoungBitableau.toPolynomial k B
        =
      d.sum (fun S a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k S.1) →
      c = d := by
  intro c d hc hd
  let v : StandardYoungBitableau m n →
      MvPolynomial (Fin m × Fin n) k :=
    fun S => YoungBitableau.toPolynomial k S.1
  have hcLin :
      Finsupp.linearCombination k v c = YoungBitableau.toPolynomial k B := by
    rw [Finsupp.linearCombination_apply]
    simpa [v, MvPolynomial.C_mul'] using hc.symm
  have hdLin :
      Finsupp.linearCombination k v d = YoungBitableau.toPolynomial k B := by
    rw [Finsupp.linearCombination_apply]
    simpa [v, MvPolynomial.C_mul'] using hd.symm
  have hlin :
      Finsupp.linearCombination k v (c - d) = 0 := by
    rw [map_sub, hcLin, hdLin, sub_self]
  have hcd : c - d = 0 :=
    (linearIndependent_iff.mp hli (c - d)) hlin
  exact sub_eq_zero.mp hcd

/-- Homogeneous projection of one scalar multiple of a standard bitableau polynomial. -/
lemma homogeneousComponent_C_mul_standardBitableau_toPolynomial
    {m n : ℕ}
    (k : Type*) [Field k]
    (d : ℕ) (a : k) (B : StandardYoungBitableau m n) :
    MvPolynomial.homogeneousComponent d
      (MvPolynomial.C a * YoungBitableau.toPolynomial k B.1)
      =
    if YoungBitableau.degree B.1 = d then
      MvPolynomial.C a * YoungBitableau.toPolynomial k B.1
    else
      0 := by
  rw [MvPolynomial.homogeneousComponent_C_mul]
  have hmem :
      YoungBitableau.toPolynomial k B.1 ∈
        MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k
          (YoungBitableau.degree B.1) := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact YoungBitableau.toPolynomial_isHomogeneous k B.1
  rw [MvPolynomial.homogeneousComponent_of_mem (m := d) hmem]
  by_cases hdeg : d = YoungBitableau.degree B.1
  · simp [hdeg]
  · have hdeg' : YoungBitableau.degree B.1 ≠ d := fun h => hdeg h.symm
    simp [hdeg, hdeg']

/-- Homogeneous projection of a finite standard-bitableau expansion. -/
lemma homogeneousComponent_standardBitableau_finsupp_sum
    {m n : ℕ}
    (k : Type*) [Field k]
    (d : ℕ)
    (c : StandardYoungBitableau m n →₀ k) :
    MvPolynomial.homogeneousComponent d
      (c.sum fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1)
      =
    (c.filter fun B => YoungBitableau.degree B.1 = d).sum fun B a =>
      MvPolynomial.C a * YoungBitableau.toPolynomial k B.1 := by
  classical
  rw [Finsupp.sum, map_sum]
  simp_rw [homogeneousComponent_C_mul_standardBitableau_toPolynomial
    k]
  rw [Finsupp.sum, Finsupp.support_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hdeg : YoungBitableau.degree B.1 = d
  · simp [hdeg]
  · simp [hdeg]

/-- It is enough to prove linear independence in each fixed total degree. -/
theorem standardBitableau_linearIndependent_of_degreewise
    {m n : ℕ}
    {k : Type*} [Field k]
    (hdeg :
      ∀ d : ℕ,
        LinearIndependent k
          (fun S : { S : StandardYoungBitableau m n //
              YoungBitableau.degree S.1 = d } =>
            YoungBitableau.toPolynomial k S.1.1)) :
    LinearIndependent k
      (fun S : StandardYoungBitableau m n =>
        YoungBitableau.toPolynomial k S.1) := by
  classical
  rw [linearIndependent_iff]
  intro c hc
  ext S
  let d : ℕ := YoungBitableau.degree S.1
  let P : StandardYoungBitableau m n → Prop :=
    fun T => YoungBitableau.degree T.1 = d
  let cd : { T : StandardYoungBitableau m n // P T } →₀ k :=
    c.subtypeDomain P
  have hsum_zero :
      (c.sum fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) = 0 := by
    rw [Finsupp.linearCombination_apply] at hc
    simpa [MvPolynomial.C_mul'] using hc
  have hfilter_zero :
      (c.filter P).sum (fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) = 0 := by
    have hcomp_zero :
        MvPolynomial.homogeneousComponent d
          (c.sum fun B a =>
            MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) = 0 := by
      rw [hsum_zero]
      simp
    have hcomp :=
      homogeneousComponent_standardBitableau_finsupp_sum
        k d c
    simpa [P] using hcomp.symm.trans hcomp_zero
  have hsubtype_zero :
      cd.sum (fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1) = 0 := by
    have hcd_eq :
        cd = (c.filter P).subtypeDomain P := by
      ext T
      simp [cd, T.2]
    have hp :
        ∀ T ∈ (c.filter P).support, P T := by
      intro T hT
      rw [Finsupp.support_filter] at hT
      exact (Finset.mem_filter.mp hT).2
    have hsum_subtype :
        ((c.filter P).subtypeDomain P).sum (fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1)
          =
        (c.filter P).sum (fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) := by
      simpa using
        (Finsupp.sum_subtypeDomain_index
          (v := c.filter P)
          (p := P)
          (h := fun B a =>
            MvPolynomial.C a * YoungBitableau.toPolynomial k B.1)
          hp)
    rw [hcd_eq, hsum_subtype]
    exact hfilter_zero
  have hlin_cd :
      Finsupp.linearCombination k
        (fun T : { T : StandardYoungBitableau m n // P T } =>
          YoungBitableau.toPolynomial k T.1.1) cd = 0 := by
    rw [Finsupp.linearCombination_apply]
    simpa [MvPolynomial.C_mul'] using hsubtype_zero
  have hcd_zero : cd = 0 := by
    exact (linearIndependent_iff.mp (hdeg d) cd) (by
      simpa [P] using hlin_cd)
  have hS := DFunLike.congr_fun hcd_zero ⟨S, rfl⟩
  simpa [cd, P, d] using hS

/-!
KRS is reopened once more for inverse-map support lemmas used by the
straightening and linear-independence arguments below.
-/

namespace KRS

/-- The inverse side of the KRS equivalence is injective on standard bitableaux. -/
theorem inverse_injective {m n : ℕ} :
    Function.Injective (fun B : StandardYoungBitableau m n => inverse B) := by
  intro B C hBC
  change inverse B = inverse C at hBC
  calc
    B = forward (inverse B) := (krs_right_inverse B).symm
    _ = forward (inverse C) := by rw [hBC]
    _ = C := krs_right_inverse C

/-- The inverse KRS monomial of a standard bitableau has the same total degree. -/
theorem inverse_degree {m n : ℕ}
    (B : StandardYoungBitableau m n) :
    Finsupp.degree (inverse B) =
      YoungBitableau.degree B.1 := by
  have h := krs_degree (inverse B)
  have hκ :
      krsEquiv m n (inverse B) = B :=
    krs_right_inverse B
  rw [hκ] at h
  exact h.symm

end KRS

/-- Every nonzero coefficient of a generic minor comes from one Leibniz
permutation term. -/
lemma genericMinor_coeff_ne_zero_exists_permExp
    {m n t : ℕ}
    (k : Type*) [CommRing k]
    (I : MinorIndex m n t) {E : (Fin m × Fin n) →₀ ℕ}
    (hcoeff : MvPolynomial.coeff E (genericMinor k I) ≠ 0) :
    ∃ σ : Equiv.Perm (Fin t), E = permExp I σ := by
  classical
  rw [minor_eq_sum_permTerm I, MvPolynomial.coeff_sum] at hcoeff
  by_contra h
  push_neg at h
  exact hcoeff <| by
    refine Finset.sum_eq_zero ?_
    intro σ hσ
    simp [coeff_permTerm, h σ]

/-- A Leibniz permutation exponent is in the support of the corresponding
generic minor over a field. -/
lemma genericMinor_permExp_mem_support
    {m n t : ℕ}
    (k : Type*) [Field k]
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)) :
    permExp I σ ∈ (genericMinor k I).support := by
  rw [MvPolynomial.mem_support_iff, coeff_minor_permExp]
  exact permCoeff_ne_zero k σ

/-- Support of a generic minor, expressed as Leibniz permutation exponent
vectors. -/
lemma genericMinor_mem_support_iff_exists_permExp
    {m n t : ℕ}
    (k : Type*) [Field k]
    (I : MinorIndex m n t) (E : (Fin m × Fin n) →₀ ℕ) :
    E ∈ (genericMinor k I).support ↔
      ∃ σ : Equiv.Perm (Fin t), E = permExp I σ := by
  constructor
  · intro hE
    exact genericMinor_coeff_ne_zero_exists_permExp k I
      (by simpa [MvPolynomial.mem_support_iff] using hE)
  · rintro ⟨σ, rfl⟩
    exact genericMinor_permExp_mem_support k I σ

namespace YoungBitableau

/-- Exponent vector obtained by choosing one Leibniz permutation term from each
minor factor of a Young bitableau. -/
noncomputable def permChoiceExp
    {m n : ℕ} (B : YoungBitableau m n)
    (π : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) :
    (Fin m × Fin n) →₀ ℕ :=
  ∑ a : Fin B.v, permExp (B.minorindex a) (π a)

/-- Coefficient obtained by choosing one Leibniz permutation term from each
minor factor of a Young bitableau. -/
noncomputable def permChoiceCoeff
    (k : Type*) [CommRing k] {m n : ℕ}
    (B : YoungBitableau m n)
    (π : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) : k :=
  ∏ a : Fin B.v, permCoeff k (π a)

/-- The monomial term obtained by choosing one Leibniz permutation term from
each minor factor of a Young bitableau. -/
noncomputable def permChoiceTerm
    (k : Type*) [CommRing k] {m n : ℕ}
    (B : YoungBitableau m n)
    (π : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) :
    MvPolynomial (Fin m × Fin n) k :=
  MvPolynomial.monomial (permChoiceExp B π) (permChoiceCoeff k B π)

/-- Multiplying the selected Leibniz terms from every minor factor gives the
single bitableau permutation-choice monomial. -/
lemma prod_permTerm_eq_permChoiceTerm
    {m n : ℕ} (k : Type*) [CommRing k]
    (B : YoungBitableau m n)
    (π : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) :
    (∏ a : Fin B.v, permTerm k (B.minorindex a) (π a)) =
      permChoiceTerm k B π := by
  classical
  rw [permChoiceTerm, permChoiceExp, permChoiceCoeff]
  calc
    (∏ a : Fin B.v, permTerm k (B.minorindex a) (π a))
        =
      ∏ a : Fin B.v,
        (MvPolynomial.C (permCoeff k (π a)) *
          MvPolynomial.monomial (permExp (B.minorindex a) (π a)) (1 : k)) := by
        apply Finset.prod_congr rfl
        intro a ha
        rw [permTerm]
        symm
        rw [MvPolynomial.C_mul_monomial]
        simp
    _ =
      (∏ a : Fin B.v, MvPolynomial.C (permCoeff k (π a))) *
        ∏ a : Fin B.v,
          MvPolynomial.monomial (permExp (B.minorindex a) (π a)) (1 : k) := by
        rw [Finset.prod_mul_distrib]
    _ =
      MvPolynomial.C (∏ a : Fin B.v, permCoeff k (π a)) *
        ∏ a : Fin B.v,
          MvPolynomial.monomial (permExp (B.minorindex a) (π a)) (1 : k) := by
        simp
    _ =
      MvPolynomial.monomial
        (∑ a : Fin B.v, permExp (B.minorindex a) (π a))
        (∏ a : Fin B.v, permCoeff k (π a)) := by
        rw [← MvPolynomial.monomial_sum_index Finset.univ
          (fun a : Fin B.v => permExp (B.minorindex a) (π a))
          (∏ a : Fin B.v, permCoeff k (π a))]

/-- Leibniz expansion of the polynomial attached to a Young bitableau: choose
one permutation term from each minor factor. -/
theorem toPolynomial_eq_sum_permChoiceTerm
    {m n : ℕ} (k : Type*) [CommRing k]
    (B : YoungBitableau m n) :
    toPolynomial k B =
      ∑ π : (∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))),
        permChoiceTerm k B π := by
  classical
  calc
    toPolynomial k B =
        ∏ a : Fin B.v,
          ∑ σ : Equiv.Perm (Fin (B.size a)),
            permTerm k (B.minorindex a) σ := by
          simp [toPolynomial, minor_eq_sum_permTerm]
    _ =
        ∑ π ∈ (Finset.univ : Finset (Fin B.v)).pi
            (fun a => (Finset.univ : Finset (Equiv.Perm (Fin (B.size a))))),
          ∏ x ∈ (Finset.univ : Finset (Fin B.v)).attach,
            permTerm k (B.minorindex x.1) (π x.1 x.2) := by
          simpa using
            (Finset.prod_sum
              (s := (Finset.univ : Finset (Fin B.v)))
              (t := fun a => (Finset.univ : Finset (Equiv.Perm (Fin (B.size a)))))
              (f := fun a σ => permTerm k (B.minorindex a) σ))
    _ =
        ∑ π : (∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))),
          ∏ a : Fin B.v, permTerm k (B.minorindex a) (π a) := by
          let e :
              ((a : Fin B.v) → a ∈ (Finset.univ : Finset (Fin B.v)) →
                Equiv.Perm (Fin (B.size a))) ≃
              ((a : Fin B.v) → Equiv.Perm (Fin (B.size a))) :=
            { toFun := fun π a => π a (Finset.mem_univ a)
              invFun := fun π a _ => π a
              left_inv := by
                intro π
                funext a ha
                rfl
              right_inv := by
                intro π
                funext a
                rfl }
          have hpi :
              (Finset.univ : Finset (Fin B.v)).pi
                (fun a => (Finset.univ : Finset (Equiv.Perm (Fin (B.size a))))) =
              (Finset.univ :
                Finset ((a : Fin B.v) →
                  a ∈ (Finset.univ : Finset (Fin B.v)) →
                    Equiv.Perm (Fin (B.size a)))) := by
            ext π
            simp
          rw [hpi]
          exact Fintype.sum_equiv e
            (fun π =>
              ∏ x ∈ (Finset.univ : Finset (Fin B.v)).attach,
                permTerm k (B.minorindex x.1) (π x.1 x.2))
            (fun π =>
              ∏ a : Fin B.v, permTerm k (B.minorindex a) (π a))
            (by
              intro π
              dsimp [e]
              exact Finset.prod_attach Finset.univ
                (fun a : Fin B.v =>
                  permTerm k (B.minorindex a) (π a (Finset.mem_univ a))))
    _ =
        ∑ π : (∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))),
          permChoiceTerm k B π := by
          apply Finset.sum_congr rfl
          intro π hπ
          rw [prod_permTerm_eq_permChoiceTerm k]

/-- The coefficient of a permutation-choice term at its own exponent. -/
lemma coeff_permChoiceTerm_permChoiceExp
    {m n : ℕ} (k : Type*) [CommRing k]
    (B : YoungBitableau m n)
    (π : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) :
    MvPolynomial.coeff (permChoiceExp B π) (permChoiceTerm k B π) =
      permChoiceCoeff k B π := by
  simp [permChoiceTerm]

/-- The coefficient attached to any bitableau permutation choice is nonzero
over a field. -/
lemma permChoiceCoeff_ne_zero
    {m n : ℕ} (k : Type*) [Field k]
    (B : YoungBitableau m n)
    (π : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) :
    permChoiceCoeff k B π ≠ 0 := by
  classical
  rw [permChoiceCoeff]
  exact Finset.prod_ne_zero_iff.mpr fun a ha =>
    permCoeff_ne_zero k (π a)

/-- Any nonzero coefficient in a Young-bitableau polynomial comes from at
least one choice of Leibniz permutation term in every minor factor.  This is a
one-way statement only; it does not assert that different choices cannot
collide or cancel. -/
lemma toPolynomial_coeff_ne_zero_exists_permChoiceExp
    {m n : ℕ} (k : Type*) [CommRing k]
    (B : YoungBitableau m n) {E : (Fin m × Fin n) →₀ ℕ}
    (hcoeff : MvPolynomial.coeff E (toPolynomial k B) ≠ 0) :
    ∃ π : (∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))),
      E = permChoiceExp B π := by
  classical
  rw [toPolynomial_eq_sum_permChoiceTerm k B, MvPolynomial.coeff_sum] at hcoeff
  by_contra h
  push_neg at h
  exact hcoeff <| by
    refine Finset.sum_eq_zero ?_
    intro π hπ
    simp only [permChoiceTerm, MvPolynomial.coeff_monomial, ite_eq_right_iff]
    intro p
    exact not_neZero.mp fun a ↦ h π (id (Eq.symm p))

/-- Support-form version of
`toPolynomial_coeff_ne_zero_exists_permChoiceExp`. -/
lemma toPolynomial_mem_support_exists_permChoiceExp
    {m n : ℕ} (k : Type*) [CommRing k]
    (B : YoungBitableau m n) {E : (Fin m × Fin n) →₀ ℕ}
    (hE : E ∈ (toPolynomial k B).support) :
    ∃ π : (∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))),
      E = permChoiceExp B π := by
  exact toPolynomial_coeff_ne_zero_exists_permChoiceExp
    k B (by simpa [MvPolynomial.mem_support_iff] using hE)

/-- The support of a Young-bitableau polynomial is contained in the range of
its permutation-choice exponents. -/
lemma toPolynomial_support_subset_permChoiceExp_range
    {m n : ℕ} (k : Type*) [CommRing k]
    (B : YoungBitableau m n) :
    ((toPolynomial k B).support : Set ((Fin m × Fin n) →₀ ℕ)) ⊆
      Set.range (fun π : (∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) =>
        permChoiceExp B π) := by
  intro E hE
  rcases toPolynomial_mem_support_exists_permChoiceExp k B hE with ⟨π, rfl⟩
  exact ⟨π, rfl⟩

/-- If a permutation-choice exponent is produced by a unique choice, then its
coefficient in the full Young-bitableau polynomial is nonzero.  This isolates
the no-cancellation input needed later for the KRS diagonal coefficient. -/
lemma toPolynomial_coeff_permChoiceExp_ne_zero_of_unique
    {m n : ℕ} (k : Type*) [Field k]
    (B : YoungBitableau m n)
    (π : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a)))
    (huniq : ∀ τ : (∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))),
      permChoiceExp B τ = permChoiceExp B π → τ = π) :
    MvPolynomial.coeff (permChoiceExp B π) (toPolynomial k B) ≠ 0 := by
  classical
  rw [toPolynomial_eq_sum_permChoiceTerm k B, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single π]
  · rw [coeff_permChoiceTerm_permChoiceExp k]
    exact permChoiceCoeff_ne_zero k B π
  · intro τ hτ hτne
    have hne : permChoiceExp B π ≠ permChoiceExp B τ := by
      intro hEq
      exact hτne ((huniq τ hEq.symm))
    simp only [permChoiceTerm, MvPolynomial.coeff_monomial, ite_eq_right_iff]
    intro p
    exact not_neZero.mp fun a ↦ hτne (huniq τ p)
  · intro hπ
    simp at hπ

/-- If every minor factor has size `1`, then the permutation choice is unique.
This is the base case of the diagonal KRS coefficient uniqueness argument:
there is no nontrivial determinant permutation in any factor. -/
lemma permChoice_unique_of_forall_size_eq_one
    {m n : ℕ}
    (B : YoungBitableau m n)
    (hsize : ∀ a : Fin B.v, B.size a = 1)
    (π τ : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) :
    τ = π := by
  funext a
  ext x
  have hx : Subsingleton (Fin (B.size a)) := by
    rw [hsize a]
    infer_instance
  have h : (τ a) x = (π a) x := Subsingleton.elim _ _
  simpa using congrArg Fin.val h

/-- In the all-`1 × 1` case, any chosen permutation-choice exponent is
uniquely produced. -/
lemma permChoiceExp_unique_of_forall_size_eq_one
    {m n : ℕ}
    (B : YoungBitableau m n)
    (hsize : ∀ a : Fin B.v, B.size a = 1)
    (π : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) :
    ∀ τ : (∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))),
      permChoiceExp B τ = permChoiceExp B π → τ = π := by
  intro τ _hExp
  exact permChoice_unique_of_forall_size_eq_one B hsize π τ

/-- All-`1 × 1` specialization of the no-cancellation coefficient lemma. -/
lemma toPolynomial_coeff_permChoiceExp_ne_zero_of_forall_size_eq_one
    {m n : ℕ} (k : Type*) [Field k]
    (B : YoungBitableau m n)
    (hsize : ∀ a : Fin B.v, B.size a = 1)
    (π : ∀ a : Fin B.v, Equiv.Perm (Fin (B.size a))) :
    MvPolynomial.coeff (permChoiceExp B π) (toPolynomial k B) ≠ 0 := by
  exact toPolynomial_coeff_permChoiceExp_ne_zero_of_unique
    k B π (permChoiceExp_unique_of_forall_size_eq_one B hsize π)

end YoungBitableau

/-- Monomials are spanned, already in the polynomial ring, by products of
`1 × 1` minors, hence by Young bitableaux.  This feeds the filtered-existence
route to fixed-degree spanning. -/
theorem monomial_mem_span_youngBitableau_toPolynomial_aux
    {m n : ℕ}
    (k : Type*) [Field k]
    (E : (Fin m × Fin n) →₀ ℕ) :
    MvPolynomial.monomial E (1 : k) ∈
      Submodule.span k
        (Set.range
          (fun B : YoungBitableau m n =>
            YoungBitableau.toPolynomial k B)) := by
  classical
  let W : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
    Submodule.span k
      (Set.range
        (fun vf : Σ v : ℕ, Fin v → Fin m × Fin n =>
          YoungBitableau.toPolynomial k
            (YoungBitableau.oneMinorVec vf.1 vf.2)))
  have hmonoW :
      MvPolynomial.monomial E (1 : k) ∈ W := by
    simpa using
      (MvPolynomial.induction_on_monomial
        (motive := fun p : MvPolynomial (Fin m × Fin n) k => p ∈ W)
        (fun a => by
          have hgen :
              YoungBitableau.toPolynomial k
                  (YoungBitableau.oneMinorVec 0 (Fin.elim0)) ∈ W := by
            exact Submodule.subset_span ⟨⟨0, Fin.elim0⟩, rfl⟩
          have hsmul :
              a • YoungBitableau.toPolynomial k
                (YoungBitableau.oneMinorVec 0 (Fin.elim0)) ∈ W :=
            W.smul_mem a hgen
          simpa [YoungBitableau.toPolynomial_oneMinorVec,
            MvPolynomial.C_eq_smul_one] using hsmul)
        (fun p x hp => by
          refine Submodule.span_induction
            (p := fun y hy => y * MvPolynomial.X x ∈ W)
            ?mem ?zero ?add ?smul hp
          · intro y hy
            rcases hy with ⟨vf, rfl⟩
            rcases vf with ⟨v, f⟩
            have hgen :
                YoungBitableau.toPolynomial k
                    (YoungBitableau.oneMinorVec (v + 1) (Fin.snoc f x)) ∈ W := by
              exact Submodule.subset_span ⟨⟨v + 1, Fin.snoc f x⟩, rfl⟩
            rw [YoungBitableau.toPolynomial_oneMinorVec_snoc] at hgen
            exact hgen
          · simp
          · intro y z hy hz hyX hzX
            simpa [add_mul] using W.add_mem hyX hzX
          · intro a y hy hyX
            simpa [MvPolynomial.smul_eq_C_mul, mul_assoc] using W.smul_mem a hyX)
        E (1 : k))
  have hW_le :
      W ≤
        Submodule.span k
          (Set.range
            (fun B : YoungBitableau m n =>
              YoungBitableau.toPolynomial k B)) := by
    rw [Submodule.span_le]
    rintro p ⟨vf, rfl⟩
    exact Submodule.subset_span ⟨YoungBitableau.oneMinorVec vf.1 vf.2, rfl⟩
  exact hW_le hmonoW

/-- The filtered straightening statement is immediate for an already standard bitableau. -/
lemma straightening_law_exists_filtered_of_isStandard
    {m n : ℕ}
    (k : Type*) [Field k]
    (B : YoungBitableau m n)
    (hB : YoungBitableau.IsStandard B) :
    ∃ c : StandardYoungBitableau m n →₀ k,
      YoungBitableau.toPolynomial k B =
        c.sum (fun S a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k S.1)
      ∧
      (∀ S, c S ≠ 0 →
        YoungBitableau.degree S.1 = YoungBitableau.degree B)
      ∧
      (∀ S, c S ≠ 0 →
        YoungBitableau.length B ≤ YoungBitableau.length S.1) := by
  classical
  let SB : StandardYoungBitableau m n := ⟨B, hB⟩
  refine ⟨Finsupp.single SB (1 : k), ?_, ?_, ?_⟩
  · simp [SB]
  · intro S hS
    have hS_eq : S = SB := by
      by_contra hne
      have hzero : (Finsupp.single SB (1 : k)) S = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hS hzero
    simp [hS_eq, SB]
  · intro S hS
    have hS_eq : S = SB := by
      by_contra hne
      have hzero : (Finsupp.single SB (1 : k)) S = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hS hzero
    simp [hS_eq, SB]

lemma exists_adjacent_violation_of_not_isStandard
    {m n : ℕ}
    (B : YoungBitableau m n)
    (hB : ¬ YoungBitableau.IsStandard B) :
    ∃ (a b : Fin B.v) (hnext : a.val + 1 = b.val)
      (j : Fin (B.size b)),
      ¬
        ((B.minorindex a).row
            ⟨j.val,
              lt_of_lt_of_le j.isLt
                (B.shape_antitone a b (by grind))⟩
          ≤ (B.minorindex b).row j
        ∧
        (B.minorindex a).col
            ⟨j.val,
              lt_of_lt_of_le j.isLt
                (B.shape_antitone a b (by grind))⟩
          ≤ (B.minorindex b).col j) := by
  classical
  simpa [YoungBitableau.IsStandard, not_forall] using hB

lemma exists_adjacent_not_pairLE_of_not_isStandard
    {m n : ℕ}
    (B : YoungBitableau m n)
    (hB : ¬ YoungBitableau.IsStandard B) :
    ∃ (a b : Fin B.v), a.val + 1 = b.val ∧
      ¬ MinorIndex.PairLE (B.minorindex a) (B.minorindex b) := by
  classical
  rw [YoungBitableau.isStandard_iff_adjacent_pairLE] at hB
  simpa [not_forall, Classical.not_imp] using hB


end Determinantal
