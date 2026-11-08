import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginReceptionMaterial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open PaidOriginQueueMemo PaidOriginQueueChecks PaidOriginReceptionMaterial
open RenewedDispatchTrace
attribute [local irreducible] PaidOriginQueueMemo.past HeaderReception.run CachedWorkDispatch.run CachedWorkDispatch.wires CachedWorkDispatch.affected ActorStageEnvelope.affected PaidOriginHeader.observed

abbrev previousLaw := RenewedDispatchSource.law RenewedDispatchTrace.point
abbrev recipient := RenewedDispatchSource.one RenewedDispatchTrace.point
abbrev scope := RenewedDispatchSource.scope RenewedDispatchTrace.point
abbrev observed := PaidOriginHeader.observed contract vocabulary law origin past previousLaw ready recipient
abbrev produce := PaidOriginHeader.produce contract vocabulary law origin past previousLaw ready recipient scope 2
def forged := {wire with ballot := {wire.ballot with actor := true}}

theorem original_authentication_is_the_incremental_source (candidate : HeaderTransport.Wire (code := old)) :
 HeaderTransport.verify vocabulary origin past candidate = decide (candidate ∈ CachedWorkDispatch.wires vocabulary cache.rows) :=
 congrArg (fun wires => decide (candidate ∈ wires))
  ((CachedWorkDispatch.wires_eq vocabulary origin past).symm.trans
   (congrArg (CachedWorkDispatch.wires vocabulary) rows_are_the_actual_incremental_history))

theorem original_wire_table_is_the_incremental_source :
 HeaderTransport.wires vocabulary origin past = CachedWorkDispatch.wires vocabulary cache.rows :=
 (CachedWorkDispatch.wires_eq vocabulary origin past).symm.trans
  (congrArg (CachedWorkDispatch.wires vocabulary) rows_are_the_actual_incremental_history)

private theorem empty_wire_table (start : Cursor old) : HeaderTransport.wires vocabulary start [] = [] := rfl

theorem the_pending_packet_keeps_its_original_identity_scope_and_send_time :
 wire.serial = 7 ∧ wire.sendCut = 84 ∧ wire.ballot.cut = 76 ∧ wire.ballot.actor = false ∧
 wire.ballot.scope = scope ∧ HeaderTransport.verify vocabulary origin past wire = true := by
 rw [original_authentication_is_the_incremental_source]
 have checked := packet_source_checked
 simpa only [packetCheck,wire,cache,scope,vocabulary,decide_eq_true_eq] using checked

theorem a_real_successor_delivery_accepts_only_the_original_context :
 PaidOriginHeader.check contract vocabulary law origin past recipient row [] wire = .accepted wire ∧
 PaidOriginHeader.check contract vocabulary shortLaw origin past recipient row [] wire = .rejected .late ∧
 PaidOriginHeader.check contract vocabulary newPhaseLaw origin past recipient row [] wire = .rejected .staleScope ∧
 PaidOriginHeader.check contract vocabulary law origin past recipient (ready.row 0) [] wire = .rejected .missingDelivery ∧
 PaidOriginHeader.check contract vocabulary law origin past recipient row [(wire.ballot.cut,wire.ballot.position)] wire = .rejected .duplicate ∧
 PaidOriginHeader.check contract vocabulary law origin past recipient row [] forged = .rejected .unauthenticated ∧
 PaidOriginHeader.check contract vocabulary law origin [] recipient row [] wire = .rejected .unauthenticated := by
 have checked := context_source_checked
 simp only [PaidOriginHeader.check,original_wire_table_is_the_incremental_source,empty_wire_table,
  row,actual_first_is_the_incremental_row,actual_second_is_the_incremental_row]
 simpa only [contextCheck,decide_eq_true_eq,wire,forged,cache,law,shortLaw,newPhaseLaw,recipient,vocabulary] using checked

theorem the_accepted_delivery_is_in_the_same_final_native_inventory :
 StageReception.delivered row wire.serial = true ∧
 ((Financial.inventoryAt final.source.input
   (ProgrammeHistory.visitAt final.source.input (EventStep.boundary row.cursor))).filterMap
   (Financial.InstructionOrigin.instruction? final.source.input)) = StageTrace.items row :=
 PaidOriginHeader.an_accepted_generated_delivery_is_in_the_actual_final_native_inventory
  contract vocabulary law origin past ready recipient 1
  (by rw [the_original_queue_generates_two_actual_steps_and_delivers_only_the_pending_packet.2.1];decide)
  [] wire a_real_successor_delivery_accepts_only_the_original_context.1

private theorem initial_is_the_original_reception :
 HeaderReception.run vocabulary previousLaw origin past recipient past.length = initialAt point := by
 unfold initialAt
 have length : past.length = cache.rows.length := by
  rw [← rows_are_the_actual_incremental_history,StageTrace.record_count]
 have first := (CachedWorkDispatch.run_eq vocabulary previousLaw origin past recipient past.length).symm
 have second := congrArg₂ (fun rows count => CachedWorkDispatch.run vocabulary previousLaw rows recipient count)
  rows_are_the_actual_incremental_history length
 exact first.trans second

private theorem runIssued_two
 (issued : List (HeaderTransport.Wire (code := old))) (receiver : Fin old.sites)
 (initial : HeaderReception.Receiver (code := old))
 (rows : Nat → StageTrace.Record (code := code)) :
 PaidOriginHeader.runIssued contract law issued receiver initial rows 2 =
 PaidOriginHeader.receiveIssued contract law issued receiver 1 (rows 1)
  (PaidOriginHeader.receiveIssued contract law issued receiver 0 (rows 0) initial) := rfl

private theorem replayed_is_the_actual_generated_reception : observed = replayedAt point := by
 unfold observed PaidOriginHeader.observed
 rw [the_original_queue_generates_two_actual_steps_and_delivers_only_the_pending_packet.2.1,
  PaidOriginHeader.runIssued_is_the_original_generated_receiver,runIssued_two,
  original_wire_table_is_the_incremental_source,initial_is_the_original_reception,
  actual_first_is_the_incremental_row,actual_second_is_the_incremental_row]
 simp only [replayedAt,law,recipient,vocabulary,cache]

private def budgetReadout (roster affected threshold : Nat) (readout : Quorum.ReadoutData Bool) : ProspectiveQuorum.Result :=
 if ¬ roster+affected < threshold+threshold then .blocked .unsafeSourceBudget
 else match readout with
  | .blocked => .blocked .missingQuorum
  | .decided value => .decided value

private theorem original_producer_factors
 {source : Code Bool Bool ProductiveMandateSource.Port (Mandate.State Bool Bool) Unit}
 (vocab : OwnedAttestation.Vocabulary (Party := Bool) (Good := Bool)
  (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit))
 (deliveryLaw : StageReception.Law (PaidInvocationSource.code source contract))
 (issuer : Cursor source) (stages : List (EventHistory.Stage (code := source)))
 (priorLaw : StageReception.Law source)
 (answer : PaidOriginQueue.Ready source contract issuer stages true true)
 (receiver : Fin source.sites) (voteScope : Scope) :
 PaidOriginHeader.produce contract vocab deliveryLaw issuer stages priorLaw answer receiver voteScope 2 =
 budgetReadout (ActorEnvelope.roster issuer.source).card
  (ActorStageEnvelope.budget issuer vocab stages voteScope) 2
  (ActorQuorum.readout (PaidOriginHeader.observed contract vocab deliveryLaw issuer stages priorLaw answer receiver) voteScope 2) := rfl

private theorem producedAt_factors (p : Cursor DispatchWindowSource.code) :
 producedAt p = budgetReadout (ActorEnvelope.roster (RenewedDispatchSource.start p).source).card
  (CachedWorkDispatch.affected (RenewedDispatchSource.vocabulary p)
    (RenewedDispatchSource.start p) (traceAt p).rows (RenewedDispatchSource.scope p)).card 2
  (ActorQuorum.readout (replayedAt p) (RenewedDispatchSource.scope p) 2) := by
 unfold producedAt budgetReadout
 rfl

private theorem produced_is_the_actual_source_budget_readout : produce = producedAt point := by
 have affected := (CachedWorkDispatch.affected_eq vocabulary origin past scope).symm.trans
  (congrArg (fun rows => CachedWorkDispatch.affected vocabulary origin rows scope)
   rows_are_the_actual_incremental_history)
 have budget := congrArg Finset.card affected
 have readout := congrArg (fun receiver => ActorQuorum.readout receiver scope 2)
  replayed_is_the_actual_generated_reception
 exact (original_producer_factors vocabulary law origin past previousLaw ready recipient scope).trans
  ((congrArg₂ (fun budget readout => budgetReadout (ActorEnvelope.roster origin.source).card budget 2 readout)
   budget readout).trans (producedAt_factors point).symm)

theorem the_generated_recovery_restores_the_original_identity_quorum :
 (HeaderReception.run vocabulary previousLaw origin past recipient past.length).receipts.length = 1 ∧
 ActorQuorum.readout (HeaderReception.run vocabulary previousLaw origin past recipient past.length) scope 2 = .blocked ∧
 observed.receipts.length = 2 ∧ ActorQuorum.support observed scope true = {false,true} ∧
 produce = .decided true := by
 rw [initial_is_the_original_reception,replayed_is_the_actual_generated_reception,produced_is_the_actual_source_budget_readout]
 have checked := quorum_source_checked
 simpa only [quorumCheck,scope,decide_eq_true_eq] using checked

def model : Native.Authority.Bound (Party := Bool) (Good := Bool)
 (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit) :=
 ⟨ProductiveMandateSource.base,ProductiveMandateSource.scope,start.source,rfl,rfl⟩

def NativeContinuation
 (model : Native.Authority.Bound (Party := Bool) (Good := Bool)
  (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit))
 (endpoint : Cursor model.source.code) : Prop :=
 let runtime := WithdrawalInquiryRuntime.runtime model endpoint
 HEq runtime.tick.generated.wholeLedgerWriteBack
  (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
 runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model endpoint).process.stateAt
  ((WithdrawalInquiryRuntime.facade model endpoint).process.successor runtime.state)

private theorem actual_native_continuation
 (model : Native.Authority.Bound (Party := Bool) (Good := Bool)
  (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit))
 (endpoint : Cursor model.source.code) : NativeContinuation model endpoint := by
 unfold NativeContinuation
 exact (WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next model endpoint).2.2.2

theorem recovery_keeps_the_same_whole_ledger_and_generated_next : NativeContinuation model final :=
 actual_native_continuation model final

def wrongContract := {contract with acceptance := {contract.acceptance with signer := true}}
theorem a_wrong_provider_signature_cannot_generate_a_recovery :
 PaidOriginQueue.plan old wrongContract origin past true true = .blocked .unpaid := by
 have rejected := PaidInvocationSource.a_wrong_signer_cannot_open_any_window old wrongContract saved true true (by decide)
 have original : origin.side = .original := rfl
 unfold PaidOriginQueue.plan
 split
 · simp only [rejected,Bool.false_eq_true,dif_neg,not_false_eq_true]
 · rename_i replaced
   have impossible : Side.original = Side.replacement := original.symm.trans replaced
   cases impossible

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueConsumer
