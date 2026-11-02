import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Head
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.PreRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Performance.Risk
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Effects

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

abbrev headFrame (nature : RequestAt) (index : Nat) := (actualPublicVisit nature index).next
abbrev HeadRegistration (nature : RequestAt) (index : Nat) :=
  Macro.Public.Accounting.Registration input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
    (headFrame nature index).start (headFrame nature index).actual.actual

/-- The live slot is on the original runtime's next native write. -/
def NativeIssueAt (nature : RequestAt) (index : Nat) (quantity : ℚ) : Prop :=
  0 < quantity ∧ ∃ registered : HeadRegistration nature index,
    Macro.Public.Accounting.registration? input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
        (headFrame nature index).start (headFrame nature index).actual.actual = some registered ∧
      registered.claim.quantity = quantity ∧
      (headFrame nature index).next = (headFrame nature index).born registered ∧
      (headFrame nature index).next.account.current.slots[(headFrame nature index).account.current.slots.length]? =
        some (.live (Epoch.Finance.admission input 0 count (.inr registered.claim)).toObligation)

private theorem original_next_is_injective : Function.Injective (Physical.next (Party := Party)
    (Good := Good) (Port := Bool) (Technology := Nat) (Instrument := Unit)) := by
  intro first second same
  rcases first with ⟨firstPast,firstRaw⟩
  rcases second with ⟨secondPast,secondRaw⟩
  have lists := congrArg Physical.Cursor.past same
  obtain ⟨rfl,rfl⟩ := List.append_singleton_inj.mp lists
  rfl

theorem an_actual_source_issue_gets_its_own_native_slot
    (nature : RequestAt) (index : Nat) (past : List InputAt)
    (debtor holder : Party) (quantity : ℚ) (positive : 0 < quantity)
    (source : (actualPublicVisit nature (index + 1)).snapshot =
      Physical.Prefix.cursor (past ++ [.primitive (Control.Scenario.request debtor (.issue () debtor holder quantity))])) :
    NativeIssueAt nature index quantity := by
  let frame := headFrame nature index
  let request := Control.Scenario.request debtor (.issue () debtor holder quantity)
  have complete := every_public_visit_is_ready_at_its_original_raw_boundary nature (actualAdmission nature) index
  have position : frame.actual.actual.position = 0 :=
    the_new_raw_reentry_starts_at_its_original_first_head _ complete
  have snapshot : frame.snapshot = Physical.Prefix.cursor (past ++ [.primitive request]) :=
    (the_generated_drain_keeps_the_actual_body_and_complete_account_run frame).1.symm.trans source
  have start : frame.start = Physical.receive (Physical.Prefix.cursor past) (.primitive request) := by
    apply original_next_is_injective
    exact frame.snapshot_is_the_literal_after.symm.trans (snapshot.trans (Physical.Prefix.cursor_append past _))
  let before := (Physical.Public.stateAt input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
    (Physical.Prefix.cursor past).past).raw
  have valid : (Physical.Public.interpreter input).Valid before (request.resign request.signer) :=
    the_signed_public_issue_is_valid (input := input) before () debtor holder quantity false positive.le
  have inventory : (Physical.Public.execution input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
      frame.start).items = [⟨0,before,request.resign request.signer⟩] :=
    (congrArg (fun cursor : CursorAt => (Physical.Public.execution input 0 count 0 0
      (firstOrigin nature).germ.snapshot.past cursor).items) start).trans
        (the_original_valid_public_primitive_has_its_singleton_inventory
          (input := input) (origin := firstOrigin nature) (Physical.Prefix.cursor past) request valid)
  exact ⟨positive,an_actual_single_issue_generates_its_registration_and_live_slot frame before
    (request.resign request.signer) position inventory () debtor holder quantity rfl valid⟩

theorem the_actual_initial_loan_is_registered_in_the_original_native_live_slot (nature : RequestAt) :
    NativeIssueAt nature 0 3 := by
  apply an_actual_source_issue_gets_its_own_native_slot nature 0 [.execute Control.Scenario.commonWork] 0 1 3
    (by norm_num)
  have source := every_pre_read_request_is_consumed_on_the_original_actual_root nature 1 (by omega)
  rw [the_pre_read_source_inventory_is_the_original_five_requests] at source
  exact source

theorem the_actual_paid_signal_risk_is_registered_in_the_original_native_live_slot
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    NativeIssueAt (Control.Scenario.discovery version) 7
      (if version = 0 then Control.Scenario.coverageUnits else Control.Scenario.premiumUnits) := by
  have source := the_actual_paid_signal_submits_the_native_risk_before_its_work version tested
  by_cases zero : version = 0
  · rw [if_pos zero]
    apply an_actual_source_issue_gets_its_own_native_slot _ 7
      (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version)) 1 0 _
      (by rw [Control.Scenario.the_native_claim_sizes_use_the_original_settlement_rate.2]; norm_num)
    simpa only [riskLiability,if_pos zero,Control.Scenario.failureLiability] using source
  · rw [if_neg zero]
    apply an_actual_source_issue_gets_its_own_native_slot _ 7
      (submittedInputs (firstRaw (Control.Scenario.discovery version)).germ.snapshot.past
        (Control.Scenario.discovery version)) 0 1 _
      (by rw [Control.Scenario.the_native_claim_sizes_use_the_original_settlement_rate.1]; norm_num)
    simpa only [riskLiability,if_neg zero,Control.Scenario.successLiability] using source

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native
