import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Physics

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

private theorem an_initial_source_operation_cannot_invent_a_period
    (state : Actual.Current (Party := Party) (Good := Good) (Port := Bool)
      (Technology := Nat) (Instrument := Unit)) (seeking : state.phase = .seeking)
    (operation : Actual.Operation input 0 count 0 0 state) :
    (operation.next input 0 count 0 0).raw.round = state.raw.round := by
  cases operation with
  | migration plan selected =>
      have origin : Actual.origin input 0 count = Control.Scenario.seed :=
        the_original_physical_seed_is_the_actual_capital_successor
      rw [origin, the_original_member_inventory_is_generated_before_the_trial] at plan
      exact ((a_zero_length_renewal_cannot_pay_the_original_members state.raw).false plan).elim
  | renewal word phase checked => cases seeking.symm.trans phase
  | repair cause attempt =>
      change (input.law.step state.raw attempt.request).round = _
      unfold RawLaw.step
      split <;> rfl

theorem the_initial_automatic_attempt_keeps_the_original_round :
    (Compile.next input 0 count 0 0 (Actual.initial input 0 count) .advance).raw.round = 2 := by
  have original : (Actual.initial input 0 count).raw.round = 2 := by
    change (Actual.origin input 0 count).round = _
    rw [show Actual.origin input 0 count = Control.Scenario.seed from
      the_original_physical_seed_is_the_actual_capital_successor]
    rfl
  unfold Compile.next Compile.compile
  cases dispatch : Actual.dispatch input 0 count 0 0 (Actual.initial input 0 count) with
  | refusal obstruction source => exact original
  | automatic generated =>
      exact (an_initial_source_operation_cannot_invent_a_period _ rfl generated.operation).trans original

theorem the_first_actual_scope_still_reads_the_original_round (nature : RequestAt) :
    (Physical.stateAt input 0 count 0 0 (firstRaw nature).germ.snapshot.past).raw.round = 2 := by
  rw [(the_first_raw_cut_keeps_the_original_reader_and_physical_prefix nature).2.1]
  change (Compile.next input 0 count 0 0 (Actual.initial input 0 count)
    (Mandatory.executionRaw (review := none) input 0 count 0 0 Physical.initial
      (.primitive Control.Scenario.ownerPresent))).raw.round = 2
  rcases the_initial_opcode_is_an_advance_or_the_original_primitive with advance | primitive
  · rw [advance]
    exact the_initial_automatic_attempt_keeps_the_original_round
  · rw [primitive]
    unfold Compile.next Compile.compile
    cases Actual.inspectPrimitive input (Actual.initial input 0 count) Control.Scenario.ownerPresent <;>
      change (Actual.origin input 0 count).round = 2 <;>
      rw [show Actual.origin input 0 count = Control.Scenario.seed from
        the_original_physical_seed_is_the_actual_capital_successor] <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
