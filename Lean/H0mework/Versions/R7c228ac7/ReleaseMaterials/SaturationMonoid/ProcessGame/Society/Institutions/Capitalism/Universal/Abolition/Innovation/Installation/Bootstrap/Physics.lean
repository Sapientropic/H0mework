import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Context
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Ingress

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

theorem a_zero_length_renewal_cannot_pay_the_original_members
    (current : Raw) :
    IsEmpty (Material.Migration.Plan input Control.Scenario.seed current [0,1,2] 0 0) := by
  refine ⟨fun plan => ?_⟩
  have generated := (Material.Migration.sourcePairs_complete input current 0 0 plan.pair).mp plan.generated
  have empty : plan.pair.2 = [] := List.eq_nil_of_length_eq_zero (by omega)
  have paid := (plan.checked.2.1.2.1 0 (by simp)).1
  rw [empty] at paid
  rcases paid with noNeed | ⟨item, inside, _, _⟩
  · cases noNeed
  · cases inside

theorem the_first_original_frame_keeps_the_literal_primitive_proposal (nature : RequestAt) :
    (firstOriginal nature).start = Physical.initial ∧
      (firstOriginal nature).proposal = .primitive Control.Scenario.ownerPresent := ⟨rfl, rfl⟩

theorem the_initial_old_current_is_seeking :
    (Physical.stateAt input 0 count 0 0 []).phase = .seeking := by
  rw [the_empty_physical_past_reads_the_original_seed_without_replaying_finance]

theorem no_zero_length_plan_can_change_a_seeking_current_to_renewal
    (state : Actual.Current (Party := Party) (Good := Good) (Port := Bool)
      (Technology := Nat) (Instrument := Unit))
    (seeking : state.phase = .seeking)
    (operation : Actual.Operation input 0 count 0 0 state)
    (generated : Actual.decide input 0 count 0 0 state = .action operation) :
    (operation.next input 0 count 0 0).phase = .seeking := by
  cases operation with
  | migration plan selected =>
      have original : Actual.origin input 0 count = Control.Scenario.seed :=
        the_original_physical_seed_is_the_actual_capital_successor
      rw [original, the_original_member_inventory_is_generated_before_the_trial] at plan
      exact ((a_zero_length_renewal_cannot_pay_the_original_members state.raw).false plan).elim
  | renewal word phase checked => cases seeking.symm.trans phase
  | repair cause attempt => rfl

theorem an_initial_advance_cannot_preinstall_a_legacy_renewal :
    (Compile.next input 0 count 0 0 (Actual.initial input 0 count) .advance).phase = .seeking := by
  unfold Compile.next Compile.compile
  cases dispatch : Actual.dispatch input 0 count 0 0 (Actual.initial input 0 count) with
  | refusal obstruction source => rfl
  | automatic generated =>
      exact no_zero_length_plan_can_change_a_seeking_current_to_renewal _ rfl
        generated.operation generated.source_exact

theorem the_initial_opcode_is_an_advance_or_the_original_primitive :
    Mandatory.executionRaw (review := none) input 0 count 0 0 Physical.initial
        (.primitive Control.Scenario.ownerPresent) = .advance ∨
      Mandatory.executionRaw (review := none) input 0 count 0 0 Physical.initial
        (.primitive Control.Scenario.ownerPresent) = .primitive Control.Scenario.ownerPresent := by
  have inactive : ReviewSource.Control.action input 0 count 0 0 Physical.initial = .inactive := rfl
  have clear := Mandatory.CurrentScope.a_seeking_current_has_no_scope_failure
    input 0 count 0 0 Physical.initial the_initial_old_current_is_seeking
  have safe := (Mandatory.CurrentScope.safe_iff_no_hazard input 0 count 0 0 Physical.initial).mp
    (Mandatory.CurrentScope.a_clear_scope_has_no_renewal_hazard input 0 count 0 0 Physical.initial clear)
  unfold Mandatory.executionRaw
  rw [inactive]
  simp only [Mandatory.CurrentScope.filterRaw, safe]
  unfold Mandatory.ordinaryRaw
  simp only [Mandatory.priorityMigration?]
  cases Mandatory.select input 0 count 0 0 Physical.initial with
  | mandatory reason => exact Or.inl rfl
  | admitted permission => exact Or.inr rfl

theorem the_first_actual_snapshot_cannot_hide_a_legacy_renewal (nature : RequestAt) :
    (Physical.stateAt input 0 count 0 0 (firstOriginal nature).snapshot.past).phase = .seeking := by
  change (Compile.next input 0 count 0 0 (Actual.initial input 0 count)
    (Mandatory.executionRaw (review := none) input 0 count 0 0 Physical.initial
      (.primitive Control.Scenario.ownerPresent))).phase = .seeking
  rcases the_initial_opcode_is_an_advance_or_the_original_primitive with advance | primitive
  · rw [advance]
    exact an_initial_advance_cannot_preinstall_a_legacy_renewal
  · rw [primitive]
    unfold Compile.next Compile.compile
    cases Actual.inspectPrimitive input (Actual.initial input 0 count) Control.Scenario.ownerPresent <;> rfl

theorem the_first_actual_admission_reads_the_seeking_source (nature : RequestAt) :
    (Physical.stateAt input 0 count 0 0 (firstRaw nature).germ.snapshot.past).phase = .seeking := by
  rw [(the_first_raw_cut_keeps_the_original_reader_and_physical_prefix nature).2.1]
  exact the_first_actual_snapshot_cannot_hide_a_legacy_renewal nature

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
