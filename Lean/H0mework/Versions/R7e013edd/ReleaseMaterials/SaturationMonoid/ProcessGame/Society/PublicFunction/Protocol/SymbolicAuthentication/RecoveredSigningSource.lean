import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceContinuationTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredSigningSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws contract)
open RecoveredProductiveSource (recycling feeding)
noncomputable section

def suppliedModel := SourceWindowCache.modelAfter feeding true true
 (SourceWindowCache.modelAfter recycling false true RecoveredWindowSource.model
  RecoveredWindowSource.origin RecoveredWindowSource.before)
 RecoveredWindowSource.donatedPoint RecoveredWindowSource.donated
def production := SourceContinuationTrace.fixed suppliedModel RecoveredWindowSource.suppliedPoint
 RecoveredWindowSource.supplied [.command 2,.idle]
def signingPoint := SourceWindowCache.point suppliedModel.source.code contract production.cursor production.before true true
def signingSeed := SourceWindowCache.after suppliedModel.source.code contract production.cursor production.before true true
def signingModel := SourceWindowCache.modelAfter contract true true suppliedModel production.cursor production.before
def vocabulary := SuccessorSigningSource.vocabulary signingModel signingPoint base
def reception : StageReception.Law signingModel.source.code :=
 ⟨fun receiver current => {(laws signingModel).scope receiver current with phase := signingPoint.cut},
  (laws signingModel).maxDelay⟩
def scope := {ConcreteProductiveSource.scope with phase := signingPoint.cut}
def trace := SourceContinuationTrace.dynamic signingModel signingPoint signingSeed.frame.sent.length
 base (laws signingModel) ConcreteProductiveSource.request.work signingSeed ConcreteProductiveSource.request.beats
def observed (recipient : Fin signingModel.source.code.sites) :=
 CachedWorkDispatch.run vocabulary reception trace.rows recipient trace.rows.length
def decision (recipient : Fin signingModel.source.code.sites) (threshold : Nat) :=
 CachedWorkDispatch.produce vocabulary signingPoint reception trace.rows recipient scope threshold
def receiver : Fin signingModel.source.code.sites := ⟨2,by change 2<3;decide⟩

theorem the_original_work_and_new_payment_really_open_the_signing_window :
 SourceWindowCache.admitted suppliedModel.source.code contract production.cursor production.before true true=true := by
 decide +kernel

theorem the_new_phase_has_an_actual_authenticated_receiver_quorum : decision receiver 1=.decided true := by
 decide +kernel

theorem the_generated_phase_contains_new_source_signatures :
 (CachedWorkDispatch.ledger vocabulary trace.rows).isEmpty=false ∧
 (CachedWorkDispatch.wires vocabulary trace.rows).isEmpty=false ∧
 (observed receiver).receipts.isEmpty=false := by
 and_intros <;> decide +kernel

theorem the_new_actual_endpoint_retains_claims_and_grows_total_service :
 (∀ instrument debtor creditor,trace.before.current.claims instrument debtor creditor=
  RecoveredWindowSource.before.current.claims instrument debtor creditor) ∧
 (∑ party, RecoveredWindowSource.before.current.stock party .service)+3≤
  ∑ party,trace.before.current.stock party .service := by
 and_intros <;> decide +kernel

theorem missing_distinct_actor_quorum_is_blocked : decision receiver 2=.blocked .missingQuorum := by decide +kernel

def undeliveredRows := match (CachedWorkDispatch.wires vocabulary trace.rows).head? with
 | none => []
 | some wire => trace.rows.take (wire.sendCut-signingPoint.cut+1)

theorem a_real_send_without_its_future_delivery_cannot_decide :
 (CachedWorkDispatch.wires vocabulary undeliveredRows).isEmpty=false ∧
 CachedWorkDispatch.produce vocabulary signingPoint reception undeliveredRows receiver scope 1=.blocked .missingQuorum := by
 and_intros <;> decide +kernel

theorem forbidding_actual_delivery_latency_cannot_decide :
 CachedWorkDispatch.produce vocabulary signingPoint {reception with maxDelay := 0}
  trace.rows receiver scope 1=.blocked .missingQuorum := by decide +kernel

inductive ReceiptAttempt where
 | authentic | duplicate | wrongActor | stale
 deriving DecidableEq

def receiptCheck (attempt : ReceiptAttempt) : Option (HeaderReception.Verdict (code := signingModel.source.code)) :=
 match (observed receiver).receipts.head? with
 | none => none
 | some receipt => match trace.rows[receipt.index]? with
   | none => none
   | some row =>
     let wire := match attempt with
      | .wrongActor => {receipt.wire with ballot := {receipt.wire.ballot with actor := 2}}
      | .stale => {receipt.wire with ballot := {receipt.wire.ballot with cut := 0}}
      | _ => receipt.wire
     let seen := if attempt=.duplicate then [(receipt.wire.ballot.cut,receipt.wire.ballot.position)] else []
     some (CachedWorkDispatch.check vocabulary reception trace.rows receiver row seen wire)

theorem an_actual_receipt_survives_independent_rechecking :
 (match receiptCheck .authentic with | some (.accepted _) => true | _ => false)=true := by decide +kernel

theorem a_duplicate_actual_receipt_is_rejected : receiptCheck .duplicate=some (.rejected .duplicate) := by decide +kernel
theorem changing_the_actual_signer_is_rejected : receiptCheck .wrongActor=some (.rejected .unauthenticated) := by decide +kernel
theorem replaying_a_stale_signature_is_rejected : receiptCheck .stale=some (.rejected .unauthenticated) := by decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredSigningSource
