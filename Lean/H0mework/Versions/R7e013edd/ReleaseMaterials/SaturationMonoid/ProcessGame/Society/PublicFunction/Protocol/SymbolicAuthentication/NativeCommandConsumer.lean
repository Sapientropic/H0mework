import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeCommandService

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeCommandConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (state : LocalCommandRun.State model start)

theorem a_generated_service_closes_the_actual_original_inventory_row
    (receipt : NativeCommandService.Receipt model start state) :
    (NativeCommandService.before model start state receipt.ready receipt.original).isPending _ _ = true ∧
    ∃ row ∈ NativeReview.inventory model start (NativeCommandCompiler.after model start state receipt.ready).stages,
      HEq row.1 receipt.original ∧ row.2.isPending _ _ = false := by
  refine ⟨receipt.pending,?_⟩
  rw [NativeCommandCompiler.the_compiled_command_keeps_the_literal_native_history model start state receipt.ready]
  obtain ⟨row,inside,same⟩ := List.mem_map.mp receipt.member
  have closed := NativeReviewHistory.a_paid_actual_attempt_closes_every_ready_original model start state.stages receipt.ready
    (EventStep.fixed none) receipt.original receipt.accepted receipt.aligned
  rw [← same] at closed
  refine ⟨row,inside,heq_of_eq same,?_⟩
  obtain ⟨birth,_,mapped⟩ := List.mem_flatMap.mp inside
  obtain ⟨claim,_,identity⟩ := List.mem_map.mp mapped
  cases identity
  exact closed

theorem a_refused_native_command_preserves_every_original_status
    (ready : NativeReview.Ready model start state.stages)
    (denied : ¬ model.source.code.law.Valid (EventStep.seed (state.current model start)).current
      (NativeReview.action model start state.stages ready.receiver))
    (original : NativeCommandService.Original model start state ready) :
    (Mandate.Challenge.through (NativeReviewHistory.family model start state.stages ready (EventStep.fixed none))
      (NativeReviewHistory.sourceIndex model start state.stages ready (EventStep.fixed none)) original
      ((NativeReviewHistory.position model start state.stages ready (EventStep.fixed none)).ordinal+1)).isPending _ _ =
    (NativeCommandService.before model start state ready original).isPending _ _ :=
  NativeReviewHistory.a_refused_actual_attempt_preserves_every_original_status model start state.stages ready
    (EventStep.fixed none) original denied

theorem the_same_closed_original_is_in_the_actual_root_inventory
    (receipt : NativeCommandService.Receipt model start state) :
    let final := (NativeCommandCompiler.after model start state receipt.ready).current model start
    ∃ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
      HEq original receipt.original ∧
      ∃ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
        row.1 = original ∧ row.2.isPending (WithdrawalInquiryRuntime.family model final)
          (WithdrawalInquiryRuntime.sourceIndex model final) = false := by
  dsimp only
  obtain ⟨_,row,inside,same,closed⟩ := a_generated_service_closes_the_actual_original_inventory_row model start state receipt
  refine ⟨row.1,same,row,?_,rfl,closed⟩
  rw [(WithdrawalInquiryRuntime.authority model
    ((NativeCommandCompiler.after model start state receipt.ready).current model start)).current_exact]
  exact inside

theorem every_generated_result_preserves_its_original_timing (delay : Nat)
    (result : NativeCommandService.Result model start state delay)
    (past : AdaptiveRejectionHistory.Compliant start delay state.stages) :
    AdaptiveRejectionHistory.Compliant start delay (result.after model start state).stages := by
  unfold NativeCommandService.Result.after
  split
  next input actual =>
    apply (DynamicCommandSource.actual_admission_is_exactly_the_original_prefix_timing_extension model start delay state input).mpr
    exact ⟨past,(List.mem_filter.mp (NativeCommandService.every_generated_input_is_in_the_actual_dynamic_domain
      model start state delay result input actual)).2⟩
  next => exact past

theorem the_actual_service_consumes_its_original_source_ledger_and_next
    (receipt : NativeCommandService.Receipt model start state) :
    let next := NativeCommandCompiler.after model start state receipt.ready
    let final := next.current model start
    let runtime := WithdrawalInquiryRuntime.runtime model final
    next.inputs = state.inputs ++ [NativeCommandCompiler.input model start state receipt.ready] ∧
    state.entries <+: next.entries ∧ state.stages <+: next.stages ∧
    next.entries.map (LocalCommandSource.Entry.row model) = StageTrace.records start next.stages ∧
    (∀ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
      let history := Mandate.Challenge.through (WithdrawalInquiryRuntime.family model final)
        (WithdrawalInquiryRuntime.sourceIndex model final) original (WithdrawalInquiryRuntime.depth model final+2)
      history.state.current.history = history.state.generated.events) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next model
    ((NativeCommandCompiler.after model start state receipt.ready).current model start)
  exact ⟨(LocalCommandRun.every_step_retains_the_literal_attempt_and_its_actual_stage model start state _).1,
    List.prefix_append _ _,List.prefix_append _ _,(NativeCommandCompiler.after model start state receipt.ready).row_exact,
    rooted.2.1,rooted.2.2.2.1,rooted.2.2.2.2⟩

theorem the_service_keeps_every_incident_and_receiver_receipt
    (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
    (receipt : NativeCommandService.Receipt model start state) :
    StageAccountability.ledger start vocabulary encoding law state.stages <+:
      StageAccountability.ledger start vocabulary encoding law (NativeCommandCompiler.after model start state receipt.ready).stages ∧
    (∀ receiver, (StageReception.run vocabulary encoding law start state.stages receiver state.stages.length).receipts <+:
      (StageReception.run vocabulary encoding law start (NativeCommandCompiler.after model start state receipt.ready).stages
        receiver (NativeCommandCompiler.after model start state receipt.ready).stages.length).receipts) := by
  constructor
  · rw [NativeCommandCompiler.the_compiled_command_keeps_the_literal_native_history,
      NativeCommandCompiler.full,NativeReviewHistory.full,StageAccountability.ledger_extends_by_its_generated_next]
    exact List.prefix_append _ _
  · intro receiver
    rw [NativeCommandCompiler.the_compiled_command_keeps_the_literal_native_history]
    exact StagePrefix.receipts_survive_actual_extension start state.stages
      [(NativeReview.protocol model start state.stages receipt.ready,EventStep.fixed none)] vocabulary encoding law receiver

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeCommandConsumer
