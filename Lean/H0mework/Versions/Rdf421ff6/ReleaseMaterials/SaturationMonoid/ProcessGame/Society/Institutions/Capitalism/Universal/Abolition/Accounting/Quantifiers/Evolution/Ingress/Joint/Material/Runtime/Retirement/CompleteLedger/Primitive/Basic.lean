import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Native.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Control

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive

open ResponsibilityLifecycle Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

def submitted (word : RawEvent Party Good Port Technology Instrument) := word.map Compile.RawInput.primitive

theorem the_existing_raw_scope_preserves_each_original_primitive
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    Macro.Public.Scope.executionRaw input depth count 0 0 [] current (.primitive request) = .primitive request ∧
      Macro.Public.Scope.failure? input depth count 0 0 [] current (.primitive request) = none ∧
      Macro.Public.Scope.deferred input depth count 0 0 [] current (.primitive request) = none :=
  Macro.Public.Scope.every_nonperiod_proposal_keeps_its_actual_route input depth count 0 0 [] current (.primitive request) rfl

omit [DecidableEq Port] in
theorem one_checked_original_primitive_has_one_actual_material_step
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (request : Request Party Good Port Technology Instrument) (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter input).Valid before.raw request) :
    (Physical.Public.compile input before (.primitive request)).isAccepted = true ∧
      (Physical.Public.compile input before (.primitive request)).execution.items = [⟨0,before.raw,request⟩] ∧
      (Physical.Public.compile input before (.primitive request)).next =
        { before with raw := (Physical.Public.interpreter input).step before.raw request } := by
  unfold Physical.Public.compile
  simp only [Physical.Public.wordAt,Request.resign_self request noConsents]
  split
  · exact ⟨rfl,rfl,rfl⟩
  · rename_i item listed failed inspected
    have member : item = ⟨0,before.raw,request⟩ := by
      simpa only [RawLaw.rawItems,RawLaw.execute,List.mem_singleton,Request.resign_self request noConsents] using listed
    subst item
    exact (failed valid).elim

theorem the_source_history_extends_by_this_same_primitive
    (history : List (Compile.RawInput Party Good Port Technology Instrument))
    (request : Request Party Good Port Technology Instrument) :
    Physical.Public.stateAt input depth count 0 0 [] (history ++ [.primitive request]) =
      (Physical.Public.compile input (Physical.Public.stateAt input depth count 0 0 [] history) (.primitive request)).next := by
  simp only [Physical.Public.stateAt,List.foldl_append,List.foldl_cons,List.foldl_nil]

omit [DecidableEq Port] in
theorem ordinary_steps_preserve_the_original_clock_and_round
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (law.step before request).clock = before.clock ∧ (law.step before request).round = before.round := by
  unfold RawLaw.step
  split <;> exact ⟨rfl,rfl⟩

omit [DecidableEq Port] in
theorem a_whole_instruction_word_preserves_the_clock_until_the_period_boundary
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument) :
    (law.execute before index word).final.clock = before.clock ∧
      (law.execute before index word).final.round = before.round := by
  induction word generalizing before index with
  | nil => exact ⟨rfl,rfl⟩
  | cons request tail ih =>
      have rest := ih (law.step before request) (index + 1)
      have first := ordinary_steps_preserve_the_original_clock_and_round law before request
      exact ⟨rest.1.trans first.1,rest.2.trans first.2⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
