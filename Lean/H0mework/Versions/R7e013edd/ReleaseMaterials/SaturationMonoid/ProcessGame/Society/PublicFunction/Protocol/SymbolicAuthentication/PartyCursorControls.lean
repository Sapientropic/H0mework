import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyRoot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 48000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyCursorControls
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Repayment.Recovery (Good)
open WholePartyLift PartyCode
abbrev old := LiveJointRepaymentControls.active
def outside : Good → ℚ := fun _ => 0
theorem lawExact : old.law = oldLaw := WholePartyControls.lawExact
abbrev saved := LiveJointRepaymentControls.generated
abbrev finished := LiveJointRepaymentControls.final
abbrev carried := PartyCursor.cursor old outside lawExact saved
abbrev completed := PartyCursor.cursor old outside lawExact finished

theorem complete_live_cursor_is_retained :
    EventStep.seed carried = PartyFeedback.state old outside (EventStep.seed saved) ∧
      carried.cut = saved.cut ∧ carried.ownerStart = saved.ownerStart ∧
      carried.overrides = PartyCursor.controls old outside saved.overrides ∧
      carried.entry.budget = saved.entry.budget :=
  ⟨PartyCursor.whole_live_seed outside old lawExact saved rfl,rfl,rfl,rfl,rfl⟩

theorem live_delivery_preserves_the_actual_packets_and_memory :
    (EventStep.seed completed).frame = PartyFrame.frame old outside (EventStep.seed finished).frame ∧
      (EventStep.seed completed).past = (EventStep.seed finished).past.map event ∧
      (EventStep.seed completed).history = (EventStep.seed finished).history.map (List.map request) := by
  have exactState := PartyCursor.whole_live_seed outside old lawExact finished rfl
  exact ⟨congrArg (fun s => s.frame) exactState,congrArg (fun s => s.past) exactState,
    congrArg (fun s => s.history) exactState⟩

abbrev row := LiveJointRepaymentControls.deliveryRow
abbrev ordinal := EventStep.boundary row.cursor
abbrev oldVisit (n : Nat) := (ProgrammeHistory.visitAt finished.source.input n).current
abbrev newVisit (n : Nat) := (ProgrammeHistory.visitAt completed.source.input n).current
abbrev before := ProgrammeSource.rawCurrent completed.source.input (newVisit ordinal)
abbrev after := ProgrammeSource.rawCurrent completed.source.input (newVisit (ordinal+1))
abbrev emitted := ProgrammeSource.rawEvent completed.source.input (newVisit ordinal)

theorem delivery_is_an_original_record : row ∈ StageTrace.records WholePartyControls.start WholePartyControls.stages :=
  List.mem_cons_of_mem _ List.mem_cons_self
abbrev originalRecord := StageTrace.every_record_is_a_completed_occurrence_of_the_final_source
  WholePartyControls.start WholePartyControls.stages row delivery_is_an_original_record

theorem before_exact : before = current row.before.current outside := by
  change ProgrammeSource.rawCurrent (PartyCursor.machine finished.source outside lawExact).input
    (ProgrammeHistory.visitAt (PartyCursor.machine finished.source outside lawExact).input ordinal).current = _
  rw [PartyRoot.every_root_visit finished.source outside lawExact rfl,PartyRoot.raw_current]
  exact congrArg (fun here => current here outside) originalRecord.1.symm

theorem after_exact : after = current row.after.current outside := by
  change ProgrammeSource.rawCurrent (PartyCursor.machine finished.source outside lawExact).input
    (ProgrammeHistory.visitAt (PartyCursor.machine finished.source outside lawExact).input (ordinal+1)).current = _
  rw [PartyRoot.every_root_visit finished.source outside lawExact rfl,PartyRoot.raw_current]
  exact congrArg (fun here => current here outside) originalRecord.2.2.1.symm

theorem word_exact : emitted = row.submitted.map request := by
  change ProgrammeSource.rawEvent (PartyCursor.machine finished.source outside lawExact).input
    (ProgrammeHistory.visitAt (PartyCursor.machine finished.source outside lawExact).input ordinal).current = _
  rw [PartyRoot.every_root_visit finished.source outside lawExact rfl,PartyRoot.raw_event finished.source outside lawExact rfl]
  exact congrArg (List.map request) originalRecord.2.1.symm

theorem the_new_root_consumes_the_actual_delivery_fee :
    emitted.length = 1 ∧ (newLaw.rawItems before emitted).length = 1 ∧
      before.stock (.inl 1) .service = 1 ∧ after.stock (.inl 1) .service = 0 ∧
      after.claims () (.inl 1) (.inl 2) = before.claims () (.inl 1) (.inl 2) ∧
      after.stock (.inr ()) .service = 0 := by
  rw [word_exact,before_exact,after_exact,RawLaw.rawItems,RawLaw.inventory_length,List.length_map]
  change row.submitted.length = 1 ∧ row.submitted.length = 1 ∧
    row.before.current.stock 1 .service = 1 ∧ row.after.current.stock 1 .service = 0 ∧
    row.after.current.claims () 1 2 = row.before.current.claims () 1 2 ∧ outside .service = 0
  and_intros <;> decide +kernel

theorem delivery_has_its_complete_financial_items :
    newLaw.rawItems before emitted = (oldLaw.rawItems row.before.current row.submitted).map (WholePartyExecution.item outside) := by
  rw [before_exact,word_exact]
  exact congrArg ExecutionResult.items (WholePartyExecution.execute _ outside 0 _)

abbrev everyRoot (n : Nat) := PartyRoot.all_actual_words_items_and_next finished.source outside lawExact rfl n
abbrev observation (here : OldCurrent) := PartyRoot.observed_report finished.source outside lawExact rfl here
abbrev native := PartyRoot.native finished.source outside lawExact ordinal

-- The exterior actor has no old identity. A word containing it is rejected in full.
def foreignRequest : WholeCursorLaw.Action := {request WorkerInputLaw.energyLabor with signer := .inr ()}
theorem no_foreign_identity_is_decoded : decode foreignRequest = none := rfl

theorem no_partial_word_is_relabelled_as_an_old_word :
    word? [request WorkerInputLaw.energyLabor,foreignRequest] = none := by
  simp [word?,decode_request,no_foreign_identity_is_decoded]

theorem a_foreign_word_does_not_call_the_original_opponent (rival : Opponent old) (f : old.Frame) :
    PartyFeedback.opponent old outside rival [] []
      {PartyFrame.frame old outside f with word := [foreignRequest]} = none := rfl

-- Duplicate override indices remain ordered, and explicit suppression remains effective.
abbrev suppressed : Cursor old := {saved with overrides := [(saved.cut,some saved.reference),(saved.cut,none)]}
theorem explicit_suppression_wins_at_the_same_cut :
    (PartyCursor.cursor old outside lawExact suppressed).source.feedbackPolicy saved.cut = none := by
  change (PartyCursor.machine suppressed.source outside lawExact).feedbackPolicy saved.cut = none
  rw [PartyCursor.feedbackPolicy suppressed.source outside lawExact rfl]
  simp only [Machine.feedbackPolicy,Cursor.source,suppressed,List.foldl_cons,List.foldl_nil,ite_true,Option.map_none]

theorem stopped_feedback_cannot_make_a_packet (entry : Input old) (s : Feedback.State old) (stopped : s.remaining = 0) :
    (Feedback.advance (code old outside) (some (policy old outside saved.reference))
      (PartyFeedback.input old outside entry) (PartyFeedback.state old outside s)).frame = PartyFrame.frame old outside s.frame := by
  rw [← show (some saved.reference).map (policy old outside) = some (policy old outside saved.reference) from rfl,
    PartyFeedback.advance old outside lawExact]
  simp only [Feedback.advance,Feedback.decision,stopped,if_pos,PartyFeedback.state]

theorem no_callback_has_no_new_paid_delivery (p : old.Policy) (s : Feedback.State old) :
    (Feedback.advance (code old outside) (some (policy old outside p))
      (PartyFeedback.input old outside ⟨EventStep.fixed none,1⟩) (PartyFeedback.state old outside s)).frame =
      PartyFrame.frame old outside s.frame := by
  rw [← show (some p).map (policy old outside) = some (policy old outside p) from rfl,
    PartyFeedback.advance old outside lawExact]
  simp only [Feedback.advance,Feedback.decision,EventStep.fixed,ite_self]
  rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyCursorControls
