import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Unfolding.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

abbrev Cell := (Party × Good) ⊕ Entitlement.Duty.Key (Party := Party) (Good := Good)

def scope : List (Cell (Party := Party) (Good := Good)) :=
  (Responsibility.Family.positiveScope mechanism past nature response).map Sum.inl ++
    (Entitlement.Duty.scope (window seed)).map Sum.inr

def remaining (current : Current seed claim) : Cell (Party := Party) (Good := Good) → ℚ
  | .inl key => current.productive key
  | .inr key => current.gross key

theorem remaining_nonnegative (current : Current seed claim) (cell : Cell (Party := Party) (Good := Good)) :
    0 ≤ remaining seed claim current cell := by
  cases cell with
  | inl key => exact current.productive_nonnegative key
  | inr key => exact current.gross_nonnegative key

theorem actual_word_never_refills_either_original_row
    (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (cell : Cell (Party := Party) (Good := Good)) :
    remaining seed claim (Current.advance seed claim current word) cell ≤ remaining seed claim current cell := by
  cases cell with
  | inl key => exact Current.actual_word_never_refills_productive seed claim current word key
  | inr key => exact Current.actual_word_never_refills_gross seed claim current word key

def unpaidCells (current : Current seed claim) : List (Cell (Party := Party) (Good := Good)) :=
  (scope seed).filter fun cell => decide (0 < remaining seed claim current cell)

def budget (current : Current seed claim) : Nat := (unpaidCells seed claim current).length

theorem zero_budget_iff_both_original_rows_are_paid (current : Current seed claim) :
    budget seed claim current = 0 ↔ Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current := by
  have empty : budget seed claim current = 0 ↔ ∀ cell ∈ scope seed, remaining seed claim current cell = 0 := by
    constructor
    · intro zero cell original
      have noCells := List.length_eq_zero_iff.mp zero
      have nonpositive : ¬ 0 < remaining seed claim current cell := by
        intro positive
        have inside : cell ∈ unpaidCells seed claim current := List.mem_filter.mpr ⟨original,decide_eq_true positive⟩
        rw [noCells] at inside
        exact List.not_mem_nil inside
      exact le_antisymm (le_of_not_gt nonpositive) (remaining_nonnegative seed claim current cell)
    · intro paid
      apply List.length_eq_zero_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro cell original
      simp only [paid cell original,lt_self_iff_false,decide_false,Bool.false_eq_true,not_false_eq_true]
  rw [empty]
  constructor
  · intro paid
    exact ⟨fun key original => paid (.inl key) (List.mem_append_left _ (List.mem_map.mpr ⟨key,original,rfl⟩)),
      fun key original => paid (.inr key) (List.mem_append_right _ (List.mem_map.mpr ⟨key,original,rfl⟩))⟩
  · rintro ⟨productive,gross⟩ cell original
    change cell ∈ (Responsibility.Family.positiveScope mechanism past nature response).map Sum.inl ++
      (Entitlement.Duty.scope (window seed)).map Sum.inr at original
    simp only [List.mem_append,List.mem_map] at original
    rcases original with ⟨key,member,same⟩ | ⟨key,member,same⟩
    · cases same
      exact productive key member
    · cases same
      exact gross key member

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
