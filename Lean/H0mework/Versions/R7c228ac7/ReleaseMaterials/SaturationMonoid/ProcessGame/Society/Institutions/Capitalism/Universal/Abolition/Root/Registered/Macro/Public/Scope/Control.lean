import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Check

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

def failure? (raw : Compile.RawInput Party Good Port Technology Instrument) :
    Option (Failure input depth count prefixLimit renewalLimit oldPast current raw) :=
  match inspect input depth count prefixLimit renewalLimit oldPast current raw with
  | .rejected failed => some failed
  | .delegated _ | .accepted .. => none

/-- Only a rejected full period changes opcode. Its original proposal and
the same-source failure remain available to the root's report face. -/
def executionRaw (raw : Compile.RawInput Party Good Port Technology Instrument) :
    Compile.RawInput Party Good Port Technology Instrument :=
  match inspect input depth count prefixLimit renewalLimit oldPast current raw with
  | .rejected _ => .stopReview
  | .delegated _ | .accepted .. => raw

def deferred (raw : Compile.RawInput Party Good Port Technology Instrument) :
    Option (Compile.RawInput Party Good Port Technology Instrument) :=
  match failure? input depth count prefixLimit renewalLimit oldPast current raw with
  | none => none
  | some _ => some raw

theorem every_actual_rejection_stops_and_keeps_its_original_residual
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (failed : Failure input depth count prefixLimit renewalLimit oldPast current raw)
    (generated : inspect input depth count prefixLimit renewalLimit oldPast current raw = .rejected failed) :
    executionRaw input depth count prefixLimit renewalLimit oldPast current raw = .stopReview ∧
      failure? input depth count prefixLimit renewalLimit oldPast current raw = some failed ∧
      deferred input depth count prefixLimit renewalLimit oldPast current raw = some raw := by
  simp [executionRaw, failure?, deferred, generated]

theorem every_nonperiod_proposal_keeps_its_actual_route
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (noPeriod : periodWord? input depth count prefixLimit renewalLimit oldPast current raw = none) :
    executionRaw input depth count prefixLimit renewalLimit oldPast current raw = raw ∧
      failure? input depth count prefixLimit renewalLimit oldPast current raw = none ∧
      deferred input depth count prefixLimit renewalLimit oldPast current raw = none := by
  cases result : inspect input depth count prefixLimit renewalLimit oldPast current raw with
  | delegated absent => simp [executionRaw, failure?, deferred, result]
  | accepted word selected proof =>
      rw [noPeriod] at selected
      contradiction
  | rejected failed =>
      have selected := failed.selected
      rw [noPeriod] at selected
      contradiction

theorem every_checked_period_executes_the_original_proposal
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : periodWord? input depth count prefixLimit renewalLimit oldPast current raw = some word)
    (checked : Checks input depth count prefixLimit renewalLimit oldPast current word) :
    executionRaw input depth count prefixLimit renewalLimit oldPast current raw = raw ∧
      failure? input depth count prefixLimit renewalLimit oldPast current raw = none ∧
      deferred input depth count prefixLimit renewalLimit oldPast current raw = none := by
  obtain ⟨source, proof, generated⟩ := every_checked_actual_period_is_accepted input depth count
    prefixLimit renewalLimit oldPast current raw word selected checked
  simp [executionRaw, failure?, deferred, generated]

theorem every_forwarded_period_carries_the_full_current_checks
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (period : periodWord? input depth count prefixLimit renewalLimit oldPast current raw = some word)
    (forwarded : executionRaw input depth count prefixLimit renewalLimit oldPast current raw = raw) :
    Checks input depth count prefixLimit renewalLimit oldPast current word := by
  cases result : inspect input depth count prefixLimit renewalLimit oldPast current raw with
  | delegated absent =>
      rw [period] at absent
      contradiction
  | accepted actual selected checked =>
      have same : actual = word := Option.some.inj (selected.symm.trans period)
      exact same ▸ checked
  | rejected failed =>
      simp only [executionRaw, result] at forwarded
      subst raw
      cases period

#print axioms executionRaw
#print axioms every_actual_rejection_stops_and_keeps_its_original_residual
#print axioms every_nonperiod_proposal_keeps_its_actual_route
#print axioms every_forwarded_period_carries_the_full_current_checks

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope
