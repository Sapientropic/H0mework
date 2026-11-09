import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Items
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.NeedFloor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument)
  (roster : List Party) (word : RawEvent Party Good Port Technology Instrument)

/-- This word pays the original and current needs at the exact opening
cut. A later period may replenish a reserve used here. -/
structure Period : Prop where
  own : ∀ item ∈ input.law.rawItems current word, OwnItem input.law roster item
  originalFloor : OriginalNeedFloor input origin current roster word
  currentFloor : OriginalNeedFloor input current current roster word
  positiveClock : 0 < input.law.duration current

inductive Issue : Type
  | instruction (failure : ItemFailure input.law roster (input.law.rawItems current word))
  | originalNeed (short : NeedFloorIssue input origin current roster word)
  | currentNeed (short : NeedFloorIssue input current current roster word)
  | clock (blocked : input.law.duration current ≤ 0)

theorem Issue.refutes (issue : Issue input origin current roster word) : ¬ Period input origin current roster word := by
  intro paid
  cases issue with
  | instruction failure => exact failure.refutes _ _ _ paid.own
  | originalNeed short => exact short.refutes input paid.originalFloor
  | currentNeed short => exact short.refutes input paid.currentFloor
  | clock blocked => exact (not_lt_of_ge blocked) paid.positiveClock

def inspect : Issue input origin current roster word ⊕ PLift (Period input origin current roster word) :=
  match inspectItems input.law roster (input.law.rawItems current word) with
  | .inl failure => .inl (.instruction failure)
  | .inr own =>
    match checkOriginalNeedFloor input origin current roster word with
    | .rejected short => .inl (.originalNeed short)
    | .accepted original =>
      match checkOriginalNeedFloor input current current roster word with
      | .rejected short => .inl (.currentNeed short)
      | .accepted live =>
        if positive : 0 < input.law.duration current then
          .inr ⟨⟨own.down, original, live, positive⟩⟩
        else .inl (.clock (le_of_not_gt positive))

theorem inspect_passes_iff :
    (∃ funded, inspect input origin current roster word = .inr funded) ↔ Period input origin current roster word := by
  constructor
  · rintro ⟨funded, _⟩
    exact funded.down
  · intro funded
    cases inspect input origin current roster word with
    | inl failed => exact (failed.refutes _ _ _ _ _ funded).elim
    | inr accepted => exact ⟨accepted, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply
