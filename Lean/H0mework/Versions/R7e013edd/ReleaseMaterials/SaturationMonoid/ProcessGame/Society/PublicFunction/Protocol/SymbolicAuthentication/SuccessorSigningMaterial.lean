import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueChecks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningMaterial
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open PaidOriginQueueMemo PaidOriginQueueChecks RenewedDispatchTrace

def recoveredAt (p : Cursor DispatchWindowSource.code) :=
 (secondCursorAt p).after SilentWindow.quiet (queueEnvironmentAt p)
def beforeAt (p : Cursor DispatchWindowSource.code) := (secondAt p).after
abbrev parentAt (p : Cursor DispatchWindowSource.code) := paidModel p
abbrev freshStartAt (p : Cursor DispatchWindowSource.code) := SuccessorSigningSource.start (parentAt p) (recoveredAt p)
abbrev freshModelAt (p : Cursor DispatchWindowSource.code) := SuccessorSigningSource.model (parentAt p) (recoveredAt p)
def freshBeforeAt (p : Cursor DispatchWindowSource.code) :=
 Extension.state (parentAt p).source.code
  (CatalogueHandoffSource.supply (parentAt p).source.code (SuccessorSigningSource.catalogue (parentAt p) (recoveredAt p))) (beforeAt p)
abbrev freshVocabulary (p : Cursor DispatchWindowSource.code) :=
 SuccessorSigningSource.vocabulary (parentAt p) (recoveredAt p) (RenewedDispatchSource.vocabulary p)
def freshScope (p : Cursor DispatchWindowSource.code) := {RenewedDispatchSource.scope p with phase := (recoveredAt p).cut}
def freshLaw (p : Cursor DispatchWindowSource.code) : StageReception.Law (freshModelAt p).source.code :=
 ⟨fun _ _ => freshScope p,1⟩
@[irreducible] def generatedAt (p : Cursor DispatchWindowSource.code) :=
 SuccessorSigningSource.Material.generate (freshModelAt p)
  (OriginQueue.baseline (RenewedDispatchSource.start p))
  (freshVocabulary p) (freshLaw p) (ProductiveMandateSource.body.take 4) 24
  (freshStartAt p,freshBeforeAt p,[])

private theorem a_ready_two_step_endpoint_is_its_actual_last_cursor
 (emitter : Code Bool Bool ProductiveMandateSource.Port (Mandate.State Bool Bool) Unit)
 (origin : Cursor emitter) (past : List (EventHistory.Stage (code := emitter)))
 (answer : PaidOriginQueue.Ready emitter contract origin past true true) (count : answer.count = 2) :
 answer.final = (answer.start.after SilentWindow.quiet (OriginQueue.environment (PaidOriginQueue.lifted emitter contract origin))).after
  SilentWindow.quiet (OriginQueue.environment (PaidOriginQueue.lifted emitter contract origin)) := by
 change EventHistory.execute answer.start (OriginQueue.stages _ _ answer.count) = _
 rw [count,OriginQueue.executed_stages_are_the_actual_cursor]
 rfl

theorem recovered_is_the_same_actual_endpoint : final = recoveredAt point := by
 have same := a_ready_two_step_endpoint_is_its_actual_last_cursor old origin past ready
  the_original_queue_generates_two_actual_steps_and_delivers_only_the_pending_packet.2.1
 change final = (start.after SilentWindow.quiet (OriginQueue.environment (PaidOriginQueue.lifted old contract origin))).after
  SilentWindow.quiet (OriginQueue.environment (PaidOriginQueue.lifted old contract origin)) at same
 rw [start_is_the_original_incremental_payment_endpoint] at same
 change final = ((fundedAt point).after SilentWindow.quiet (OriginQueue.environment (liftedAt point))).after
  SilentWindow.quiet (OriginQueue.environment (liftedAt point)) at same
 rw [← queue_environment_is_the_original_environment] at same
 exact same

theorem before_is_the_same_actual_seed : beforeAt point = EventStep.seed (recoveredAt point) :=
 (congrArg (fun row : StageTrace.Record (code := code) => row.after)
  (CachedCommandRun.materialAt_eq (paidModel point) (secondCursorAt point) (firstAt point).after
   first_after_is_the_original_seed SilentWindow.quiet (queueEnvironmentAt point))).trans
  (StageTrace.material_is_the_actual_step _ _ _).1

private theorem executed_side {emitter : Code Bool Bool ProductiveMandateSource.Port (Mandate.State Bool Bool) Unit}
 (cursor : Cursor emitter) (protocol : Rule emitter) (rival : Opponent emitter) :
 (cursor.after protocol rival).side = cursor.side := rfl

theorem recovered_is_original : (recoveredAt point).side = .original := by
 change (traceAt point).cursor.side = .original
 exact incremental_cursor_is_original

theorem fresh_seed_is_the_same_actual_state : freshBeforeAt point = EventStep.seed (freshStartAt point) :=
 (congrArg (Extension.state (parentAt point).source.code
  (CatalogueHandoffSource.supply (parentAt point).source.code (SuccessorSigningSource.catalogue (parentAt point) (recoveredAt point))))
  before_is_the_same_actual_seed).trans
   (SuccessorSigningSource.start_keeps_the_entire_actual_state (parentAt point) (recoveredAt point) recovered_is_original).symm

def zeroAt (p : Cursor DispatchWindowSource.code) : Fin (freshModelAt p).source.code.sites := ⟨0,by change 0<2;decide⟩
def oneAt (p : Cursor DispatchWindowSource.code) : Fin (freshModelAt p).source.code.sites := ⟨1,by change 1<2;decide⟩
@[irreducible] def successCheck (p : Cursor DispatchWindowSource.code) : Bool :=
 let result := generatedAt p
 let rows := result.1.2.2
 let zero := CachedWorkDispatch.run (freshVocabulary p) (freshLaw p) rows (zeroAt p) rows.length
 let one := CachedWorkDispatch.run (freshVocabulary p) (freshLaw p) rows (oneAt p) rows.length
 decide (rows.length=24 ∧ (freshBeforeAt p).remaining=46 ∧ result.1.2.1.remaining=22 ∧
  result.1.2.1.frame.sent.length=12 ∧ (CachedWorkDispatch.wires (freshVocabulary p) rows).length=4 ∧
  (freshScope p).phase=90 ∧ zero.receipts.length=2 ∧ one.receipts.length=2 ∧
  ActorQuorum.readout zero (freshScope p) 2 = .decided true ∧
  ActorQuorum.readout one (freshScope p) 2 = .decided true)

theorem generated_new_signing_and_two_receivers_pass_the_same_source_check : successCheck point = true :=
 (congrArg successCheck point_is_the_incrementally_computed_paid_successor).trans (by decide +kernel)

@[irreducible] def controlCheck (p : Cursor DispatchWindowSource.code) : Bool :=
 let data := (generatedAt p).1
 let rows := data.2.2
 let vocab := freshVocabulary p
 let law := freshLaw p
 let wires := CachedWorkDispatch.wires vocab rows
 let short : StageReception.Law (freshModelAt p).source.code := ⟨law.scope,0⟩
 let stale : StageReception.Law (freshModelAt p).source.code := ⟨fun _ _ => RenewedDispatchSource.scope p,1⟩
 let first := (SuccessorSigningSource.Material.generate (freshModelAt p)
  (OriginQueue.baseline (RenewedDispatchSource.start p)) vocab law (ProductiveMandateSource.body.take 4) 2
  (freshStartAt p,freshBeforeAt p,[])).1.2.2
 let reset := (SuccessorSigningSource.Material.generate (freshModelAt p) (freshBeforeAt p).past.length
  vocab law (ProductiveMandateSource.body.take 4) 2 (freshStartAt p,freshBeforeAt p,[])).1.2.2
 decide ((CachedWorkDispatch.affected vocab (freshStartAt p) rows (freshScope p)).card=0 ∧
  (ActorEnvelope.roster (freshStartAt p).source).card=2 ∧
  first.all (fun row => !HeaderReception.delivered row 0) = true ∧
  reset.any (fun row => HeaderReception.delivered row 0) = true ∧
  rows.all (fun row => (List.range 8).all (fun serial => !HeaderReception.delivered row serial)) = true ∧
  wires.all (fun wire => rows.any (fun row => decide (
   CachedWorkDispatch.check vocab law rows wire.recipient row [] wire = .accepted wire ∧
   CachedWorkDispatch.check vocab law rows wire.recipient row [(wire.ballot.cut,wire.ballot.position)] wire = .rejected .duplicate ∧
   CachedWorkDispatch.check vocab short rows wire.recipient row [] wire = .rejected .late ∧
   CachedWorkDispatch.check vocab stale rows wire.recipient row [] wire = .rejected .staleScope ∧
   CachedWorkDispatch.check vocab law [] wire.recipient row [] wire = .rejected .unauthenticated ∧
   CachedWorkDispatch.check vocab law rows wire.recipient row []
    {wire with ballot := {wire.ballot with actor := !wire.ballot.actor}} = .rejected .unauthenticated))) = true)

theorem retained_attempts_and_all_new_wire_refusals_pass_the_same_source_check : controlCheck point = true :=
 (congrArg controlCheck point_is_the_incrementally_computed_paid_successor).trans (by decide +kernel)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningMaterial
