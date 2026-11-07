import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive.Compiler
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

def Report : Compile.RawInput Party Good Port Technology Instrument → Type
  | .advance => Outcome input depth count prefixLimit renewalLimit oldPast current
  | _ => Unit

def report (raw : Compile.RawInput Party Good Port Technology Instrument) :
    Report input depth count prefixLimit renewalLimit oldPast current raw := by
  cases raw with
  | advance => exact compile input depth count prefixLimit renewalLimit oldPast current
  | primitive request => exact ()
  | execute word => exact ()
  | migrate pair => exact ()
  | code submission => exact ()
  | review code => exact ()
  | stopReview => exact ()

theorem an_automatic_failure_carries_each_precise_source_issue
    (obstruction : Obstruction input depth count prefixLimit renewalLimit oldPast current)
    (generated : compile input depth count prefixLimit renewalLimit oldPast current = .obstructed obstruction) :
    report input depth count prefixLimit renewalLimit oldPast current .advance = .obstructed obstruction ∧
      selectedRaw input depth count prefixLimit renewalLimit oldPast current .advance = .advance := by
  simp only [report, selectedRaw, generated]
  exact ⟨rfl, trivial⟩

#print axioms report
#print axioms an_automatic_failure_carries_each_precise_source_issue

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive
