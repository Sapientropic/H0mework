import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

def selectedCursor (raw : Compile.RawInput Party Good Port Technology Instrument) :=
  Physical.receive current (executionRaw input depth count prefixLimit renewalLimit oldPast current raw)

def actualResult (raw : Compile.RawInput Party Good Port Technology Instrument) :=
  Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast
    (selectedCursor input depth count prefixLimit renewalLimit oldPast current raw)

theorem an_actual_scope_rejection_cannot_advance_the_physical_current
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (failed : Failure input depth count prefixLimit renewalLimit oldPast current raw)
    (generated : inspect input depth count prefixLimit renewalLimit oldPast current raw = .rejected failed) :
    (actualResult input depth count prefixLimit renewalLimit oldPast current raw).next =
        actualState input depth count prefixLimit renewalLimit oldPast current ∧
      (actualResult input depth count prefixLimit renewalLimit oldPast current raw).execution.items = [] := by
  have stopped := (every_actual_rejection_stops_and_keeps_its_original_residual input depth count
    prefixLimit renewalLimit oldPast current raw failed generated).1
  unfold actualResult selectedCursor
  rw [stopped]
  exact ⟨rfl, rfl⟩

theorem an_actual_scope_rejection_keeps_the_clock_and_original_failure
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (failed : Failure input depth count prefixLimit renewalLimit oldPast current raw)
    (generated : inspect input depth count prefixLimit renewalLimit oldPast current raw = .rejected failed) :
    (actualResult input depth count prefixLimit renewalLimit oldPast current raw).next.raw.clock =
        (actualState input depth count prefixLimit renewalLimit oldPast current).raw.clock ∧
      failure? input depth count prefixLimit renewalLimit oldPast current raw = some failed ∧
      deferred input depth count prefixLimit renewalLimit oldPast current raw = some raw := by
  have preserved := (an_actual_scope_rejection_cannot_advance_the_physical_current input depth count
    prefixLimit renewalLimit oldPast current raw failed generated).1
  exact ⟨congrArg (fun state => state.raw.clock) preserved,
    (every_actual_rejection_stops_and_keeps_its_original_residual input depth count
      prefixLimit renewalLimit oldPast current raw failed generated).2⟩

#print axioms actualResult
#print axioms an_actual_scope_rejection_cannot_advance_the_physical_current
#print axioms an_actual_scope_rejection_keeps_the_clock_and_original_failure

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope
