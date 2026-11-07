import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive.Types
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

def localCursor (absolute : Physical.Cursor Party Good Port Technology Instrument) :=
  Physical.receive (Physical.Prefix.cursor (absolute.past.drop oldPast.length)) absolute.incoming

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem localizing_the_source_cursor_keeps_the_literal_public_prefix :
    localCursor oldPast (Physical.receive (Physical.Prefix.cursor (oldPast ++ current.past)) current.incoming) = current := by
  simp only [localCursor, Physical.receive, Physical.Prefix.past_readback, List.drop_left]

theorem an_available_current_source_word_cannot_be_vetoed
    (available : ∃ word ∈ candidates input depth count prefixLimit renewalLimit oldPast current,
      Checks input depth count prefixLimit renewalLimit oldPast current word) :
    ∃ plan, compile input depth count prefixLimit renewalLimit oldPast current = .accepted plan := by
  cases generated : compile input depth count prefixLimit renewalLimit oldPast current with
  | accepted plan => exact ⟨plan, rfl⟩
  | obstructed obstruction =>
      obtain ⟨word, present, checked⟩ := available
      exact (obstruction.excluded word present checked).elim

def selectedRaw (raw : Compile.RawInput Party Good Port Technology Instrument) :
    Compile.RawInput Party Good Port Technology Instrument :=
  match raw with
  | .advance => match compile input depth count prefixLimit renewalLimit oldPast current with
      | .accepted plan => .execute plan.rawWord
      | .obstructed _ => .advance
  | other => other

def reader (original : Macro.Raw.Reader input depth count) : Macro.Raw.Reader input depth count :=
  fun absolute account => selectedRaw input depth count prefixLimit renewalLimit oldPast
    (localCursor oldPast absolute) (original absolute account)

#print axioms reader
#print axioms an_available_current_source_word_cannot_be_vetoed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive
