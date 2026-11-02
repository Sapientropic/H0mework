import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Signal.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Observation

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

theorem the_original_current_pays_and_learns_its_own_trial_observation
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (Observation.originalResult input 0 count 0 0 (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        rule (beforeReadInputs (Control.Scenario.discovery version))).isAccepted = true ∧
      observedSignal (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version) = discoverySignal version := by
  let nature := Control.Scenario.discovery version
  let before := Physical.stateAt input 0 count 0 0 (firstRaw nature).germ.snapshot.past
  have normalized := an_explicit_prefix_reads_only_its_original_raw before
    (⟨before.raw,.seeking,[]⟩ : PhysicalState) rfl (beforeReadInputs nature)
    (the_original_pre_read_requests_have_no_automatic_advance nature)
  have checked := of_decide_eq_true ((List.all_eq_true.mp
    ((List.all_eq_true.mp each_original_trial_branch_pays_its_own_read_and_acquires_the_real_signal)
      before.raw (the_first_actual_raw_is_in_its_actual_source_inventory nature))) version tested)
  refine ⟨the_explicit_paid_read_is_accepted _ ?_, ?_⟩
  · exact Eq.mpr (congrArg (fun raw : Raw => (Physical.Public.interpreter input).Valid raw rule.request) normalized) checked.1
  · exact (congrArg (fun raw : Raw => rule.code.readLocal rule.site (rule.code.snapshot rule.site raw)) normalized).trans checked.2

private theorem original_next_cursor_is_injective : Function.Injective (Physical.next (Party := Party)
    (Good := Good) (Port := Bool) (Technology := Nat) (Instrument := Unit)) := by
  intro first second same
  rcases first with ⟨firstPast,firstRaw⟩
  rcases second with ⟨secondPast,secondRaw⟩
  have lists := congrArg Physical.Cursor.past same
  obtain ⟨rfl,rfl⟩ := List.append_singleton_inj.mp lists
  rfl

private theorem the_original_fee_result_is_at_the_literal_prefix
    (oldPast past : List InputAt) :
    (Physical.Public.resultAt input 0 count 0 0 oldPast
      (Physical.receive (Physical.Prefix.cursor past) (.primitive rule.request))).isAccepted =
        (Observation.originalResult input 0 count 0 0 oldPast rule past).isAccepted := by
  dsimp only [Physical.Public.resultAt, Physical.receive, Observation.originalResult]
  rw [Physical.Prefix.past_readback]

theorem the_read_on_the_actual_root_is_the_literal_self_paid_source_item (version : Nat) :
    (actualPublicVisit (Control.Scenario.discovery version) 6).start =
      Physical.receive (Physical.Prefix.cursor (beforeReadInputs (Control.Scenario.discovery version)))
        (.primitive rule.request) := by
  let frame := actualPublicVisit (Control.Scenario.discovery version) 6
  apply original_next_cursor_is_injective
  exact frame.snapshot_is_the_literal_after.symm.trans
    ((the_same_actual_trial_root_itself_requests_and_consumes_the_read version).trans
      (Physical.Prefix.cursor_append _ _))

theorem the_original_actual_root_really_pays_for_its_trial_signal
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    (Physical.Public.resultAt input 0 count 0 0 (firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past
      (actualPublicVisit (Control.Scenario.discovery version) 6).start).isAccepted = true ∧
    observedSignal (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
      (Control.Scenario.discovery version) = discoverySignal version := by
  have produced := the_original_current_pays_and_learns_its_own_trial_observation version tested
  refine ⟨?_,produced.2⟩
  have same := congrArg (fun cursor : CursorAt => (Physical.Public.resultAt input 0 count 0 0
    (firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past cursor).isAccepted)
      (the_read_on_the_actual_root_is_the_literal_self_paid_source_item version)
  have sameOld : (firstOrigin (Control.Scenario.discovery version)).germ.snapshot.past =
      (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past := by
    unfold firstOrigin Macro.Runtime.Frame.controlOrigin Functions.Revision.Enactment.Inquiry.contextAt
    rfl
  have originalRead := congrArg (fun oldPast : List InputAt =>
    (Physical.Public.resultAt input 0 count 0 0 oldPast
      (Physical.receive (Physical.Prefix.cursor (beforeReadInputs (Control.Scenario.discovery version)))
        (.primitive rule.request))).isAccepted) sameOld
  exact same.trans (originalRead.trans ((the_original_fee_result_is_at_the_literal_prefix _ _).trans produced.1))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
