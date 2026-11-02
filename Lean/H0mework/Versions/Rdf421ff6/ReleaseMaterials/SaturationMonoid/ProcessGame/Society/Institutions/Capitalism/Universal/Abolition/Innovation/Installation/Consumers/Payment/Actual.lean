import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Payment.Prefix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Settlement

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

private theorem actual_next_cursor_is_injective : Function.Injective (Physical.next (Party := Party)
    (Good := Good) (Port := Bool) (Technology := Nat) (Instrument := Unit)) := by
  intro first second same
  rcases first with ⟨firstPast,firstRaw⟩
  rcases second with ⟨secondPast,secondRaw⟩
  obtain ⟨rfl,rfl⟩ := List.append_singleton_inj.mp (congrArg Physical.Cursor.past same)
  rfl

private theorem original_start_is_the_same_consumed_primitive
    {origin : Functions.Revision.Context (input := input) (review := none) 0 count 0 0 0 count}
    {admission : Functions.Revision.InitialAdmissionAt origin} (frame : Macro.Public.Runtime.Frame origin admission)
    (past : List InputAt) (request : RequestAt)
    (actual : frame.snapshot = Physical.Prefix.cursor (past ++ [.primitive request])) :
    frame.start = Physical.receive (Physical.Prefix.cursor past) (.primitive request) :=
  actual_next_cursor_is_injective (frame.snapshot_is_the_literal_after.symm.trans
    (actual.trans (Physical.Prefix.cursor_append past (.primitive request))))

theorem both_actual_settlements_have_their_literal_original_singleton_start
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (actualPublicVisit (Control.Scenario.discovery version) 10).start =
      Physical.receive (Physical.Prefix.cursor (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version) ++ [.primitive (riskLiability version),.execute Control.Scenario.commonWork]))
        (.primitive (firstSettlement version)) ∧
    (actualPublicVisit (Control.Scenario.discovery version) 11).start =
      Physical.receive (Physical.Prefix.cursor (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version) ++ [.primitive (riskLiability version),.execute Control.Scenario.commonWork,
          .primitive (firstSettlement version)])) (.primitive (lastSettlement version)) := by
  let nature := Control.Scenario.discovery version
  let oldPast := (firstRaw nature).germ.snapshot.past
  constructor
  · apply original_start_is_the_same_consumed_primitive
    exact (the_same_actual_trial_submits_its_first_finite_settlement version tested).trans
      (congrArg Physical.Prefix.cursor (List.append_assoc (submittedInputs oldPast nature)
        [.primitive (riskLiability version),.execute Control.Scenario.commonWork] [.primitive (firstSettlement version)]).symm)
  · apply original_start_is_the_same_consumed_primitive
    exact (the_same_actual_trial_completes_its_four_original_performance_attempts version tested).trans
      (congrArg Physical.Prefix.cursor (List.append_assoc (submittedInputs oldPast nature)
        [.primitive (riskLiability version),.execute Control.Scenario.commonWork,.primitive (firstSettlement version)]
        [.primitive (lastSettlement version)]).symm)

theorem both_settlements_on_the_original_actual_root_are_really_accepted
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (Physical.Public.resultAt input 0 count 0 0 (firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past
      (actualPublicVisit (Control.Scenario.discovery version) 10).start).isAccepted = true ∧
    (Physical.Public.resultAt input 0 count 0 0 (firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past
      (actualPublicVisit (Control.Scenario.discovery version) 11).start).isAccepted = true := by
  let nature := Control.Scenario.discovery version
  let oldPast := (firstRaw nature).germ.snapshot.past
  have paid := every_original_three_branch_disposition_has_its_real_paid_contract
    (Physical.stateAt input 0 count 0 0 oldPast).raw
    (the_first_actual_raw_is_in_its_actual_source_inventory nature) version tested
  have starts := both_actual_settlements_have_their_literal_original_singleton_start version tested
  constructor
  · have parsed := congrArg (fun cursor : CursorAt => (Physical.Public.resultAt input 0 count 0 0 oldPast cursor).isAccepted) starts.1
    exact parsed.trans ((the_original_public_prefix_and_primitive_own_the_same_result oldPast _ _).trans
      ((the_actual_primitive_acceptance_uses_only_its_original_raw _
        (performanceWork (Physical.stateAt input 0 count 0 0 oldPast).raw version).next
        (the_first_settlement_prefix_has_the_original_work_raw oldPast version) (firstSettlement version)).trans paid.2.1))
  · have parsed := congrArg (fun cursor : CursorAt => (Physical.Public.resultAt input 0 count 0 0 oldPast cursor).isAccepted) starts.2
    exact parsed.trans ((the_original_public_prefix_and_primitive_own_the_same_result oldPast _ _).trans
      ((the_actual_primitive_acceptance_uses_only_its_original_raw _
        (performanceFirstSettlement (Physical.stateAt input 0 count 0 0 oldPast).raw version).next
        (the_last_settlement_prefix_has_the_original_first_payment_raw oldPast version) (lastSettlement version)).trans paid.2.2.1))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
