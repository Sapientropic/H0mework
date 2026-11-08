import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartySource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartyControls
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Repayment.Recovery (Good)
open WholePartyLift

abbrev source := LiveJointRepaymentControls.final.source
abbrev original := source.input
theorem lawExact : original.law = oldLaw := AtomicWorkControls.materialLaw
def outside : Good → ℚ := fun _ => 0
abbrev carried := WholePartySource.input original outside
abbrev production := LiveJointRepaymentControls.production
abbrev start := LiveJointRepaymentSource.start LiveJointRepaymentControls.old LiveJointRepaymentControls.saved
abbrev stages := LiveJointRepaymentControls.stages
abbrev ordinal := EventStep.boundary production.cursor
abbrev oldVisit (n : Nat) := (ProgrammeHistory.visitAt original n).current
abbrev newVisit (n : Nat) := (ProgrammeHistory.visitAt carried n).current
abbrev before := ProgrammeSource.rawCurrent carried (newVisit ordinal)
abbrev after := ProgrammeSource.rawCurrent carried (newVisit (ordinal+1))
abbrev emitted := ProgrammeSource.rawEvent carried (newVisit ordinal)

theorem production_is_an_original_record : production ∈ StageTrace.records start stages := List.mem_cons_self
abbrev originalRecord := StageTrace.every_record_is_a_completed_occurrence_of_the_final_source
  start stages production production_is_an_original_record

theorem before_exact : before = current production.before.current outside := by
  change ProgrammeSource.rawCurrent carried (ProgrammeHistory.visitAt carried ordinal).current = _
  rw [WholePartySource.every_original_root_visit_is_replayed original lawExact,WholePartySource.rawCurrent]
  exact congrArg (fun here => current here outside) originalRecord.1.symm

theorem after_exact : after = current production.after.current outside := by
  change ProgrammeSource.rawCurrent carried (ProgrammeHistory.visitAt carried (ordinal+1)).current = _
  rw [WholePartySource.every_original_root_visit_is_replayed original lawExact,WholePartySource.rawCurrent]
  exact congrArg (fun here => current here outside) originalRecord.2.2.1.symm

theorem word_exact : emitted = production.submitted.map request := by
  change ProgrammeSource.rawEvent carried (ProgrammeHistory.visitAt carried ordinal).current = _
  rw [WholePartySource.every_original_root_visit_is_replayed original lawExact,WholePartySource.rawEvent]
  exact congrArg (List.map request) originalRecord.2.1.symm

-- This is the actual old live-source repayment, located inside the new root's own visits.
theorem the_original_payment_progress_and_every_instruction_are_carried :
    emitted.length = 12 ∧ (newLaw.rawItems before emitted).length = 12 ∧
      after.claims () (.inl 1) (.inl 2) < before.claims () (.inl 1) (.inl 2) ∧
      1 ≤ after.stock (.inl 1) .service ∧
      (∀ good, after.stock (.inr ()) good = 0) := by
  have paid := LiveJointRepaymentControls.the_same_live_source_now_pays_principal_and_preserves_transport_liquidity
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [word_exact,List.length_map]
    exact paid.2.2.2.1
  · rw [RawLaw.rawItems,RawLaw.inventory_length,word_exact,List.length_map]
    exact paid.2.2.2.1
  · rw [before_exact,after_exact]
    exact paid.2.2.2.2.2.2.2.1
  · rw [after_exact]
    exact paid.2.2.2.2.2.2.2.2.1
  · rw [after_exact]
    exact fun _ => rfl

theorem the_old_financial_record_has_its_complete_carried_partner :
    newLaw.rawItems before emitted = (oldLaw.rawItems production.before.current production.submitted).map
      (WholePartyExecution.item outside) := by
  rw [before_exact,word_exact]
  exact congrArg ExecutionResult.items (WholePartyExecution.execute _ outside 0 _)

theorem the_actual_machine_observation_is_retained :
    carried.observedEmission?.isSome = true ∧
      ProgrammeSource.registrationSize carried = ProgrammeSource.registrationSize original :=
  ⟨rfl,WholePartySource.registration original outside⟩

abbrev observedReport := WholePartySource.actual_machine_report source outside production.before.current
abbrev everyRootVisit (n : Nat) := WholePartySource.every_original_root_visit_is_replayed original lawExact outside n
abbrev everyRootTrace (n : Nat) := WholePartySource.every_original_root_word_and_full_trace_are_replayed original lawExact outside n
abbrev native := WholePartySource.native original outside ordinal

abbrev invalid := NativeMaterialPotentialControls.negative
abbrev oldTerminal := NativeMaterialPotentialControls.terminal

theorem genuine_original_refusal_keeps_its_position_and_changes_no_stock :
    ¬ newLaw.Valid (current oldTerminal outside) (request invalid) ∧
      newLaw.step (current oldTerminal outside) (request invalid) = current oldTerminal outside ∧
      (newLaw.rawItems (current oldTerminal outside) [request invalid]).length = 1 := by
  have refused := NativeMaterialPotentialControls.source_shortage_and_invalid_input_cannot_mint_the_missing_budget.2.2.1
  have carriedRefusal : ¬ newLaw.Valid (current oldTerminal outside) (request invalid) :=
    fun legal => refused ((valid oldTerminal outside invalid).mp legal)
  exact ⟨carriedRefusal,RawLaw.rejected_preserves_current _ _ _ carriedRefusal,RawLaw.inventory_length _ _ _ _⟩

def forged : OldAction := {WorkerInputLaw.energyLabor with signer := 2}
set_option linter.unusedSimpArgs false in
theorem wrong_signer_cannot_borrow_the_original_workers_port (old : OldCurrent) :
    ¬ newLaw.Valid (current old outside) (request forged) := by
  intro accepted
  have policy := ((valid old outside forged).mp accepted).1.2
  simp [oldLaw,FuelMandateLaw.law,Mandate.law,RawLaw.operationAllowed,RawPolicy.eval,
    FuelMandateLaw.base,RenewedQuorumMaterial.base,Repayment.Recovery.base,forged,
    WorkerInputLaw.energyLabor,RenewedQuorumMaterial.give,Mandate.eraseCurrent,Mandate.eraseRequest,
    Mandate.eraseOperation] at policy

theorem no_old_mandate_map_installs_the_new_actor (old : OldState) :
    (state old).holder ≠ some (.inr ()) ∧ (state old).offered ≠ some (.inr ()) := by
  cases holder : old.holder <;> cases offered : old.offered <;> simp [state,holder,offered]

-- An arbitrary old original report and a planning tag are never treated as a new signature.
abbrev oldReceipt := LiveJointRepaymentControls.received
abbrev originalReceiptConsumer := LiveJointRepaymentControls.actualDelivery
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartyControls
