import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceOpportunityHandoff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceOpportunitySource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws)
noncomputable section

def predecessorModel := RecoveredSigningSource.signingModel
def predecessorPoint := RecoveredSigningSource.trace.cursor
def predecessorSeed := RecoveredSigningSource.trace.before
def missingAddress := ((List.range (predecessorModel.source.code.sites*predecessorModel.source.code.sites)).map
 fun offset => predecessorSeed.frame.sent.length+offset).find?
  (fun serial => decide (.deliver serial∉predecessorModel.source.code.eventAlphabet))
def target := missingAddress.getD predecessorSeed.frame.sent.length
def model := SourceOpportunityHandoff.modelAfter predecessorModel predecessorPoint predecessorSeed
def origin := SourceOpportunityHandoff.point predecessorModel predecessorPoint predecessorSeed
def before := SourceOpportunityHandoff.after predecessorModel predecessorSeed
def vocabulary := SuccessorSigningSource.vocabulary model origin base
def reception : StageReception.Law model.source.code :=
 ⟨fun receiver current => {(laws model).scope receiver current with phase := origin.cut},(laws model).maxDelay⟩
def scope := {ConcreteProductiveSource.scope with phase := origin.cut}

-- The actual packet must exist before this source-selected missing address can be delivered.
def control (bound : FreshSigningReplay.Model (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit))
 (start : Cursor bound.source.code) (trace : SourceContinuationTrace.Trace bound) : LocalCommandSource.Input :=
 if (CachedCommandRun.ownerAt bound trace.cursor trace.before).isSome then
  if target<trace.before.frame.sent.length then .idle
  else SourceContinuationTrace.choose bound start predecessorSeed.frame.sent.length base (laws bound)
    [RecycledQuorumSource.fee false] trace
 else if target<trace.before.frame.sent.length ∧ !(trace.rows.any fun row => HeaderReception.delivered row target) then
  match (List.range bound.source.code.eventAlphabet.length).find?
   (fun index => decide (bound.source.code.eventAlphabet[index]?=some (.deliver target))) with
  | none => .idle
  | some index => .event index
 else .idle

def trace := SourceOpportunityHandoff.controlled model origin before (control model origin) 36
def withoutRegistration := SourceOpportunityHandoff.controlled predecessorModel predecessorPoint predecessorSeed
 (control predecessorModel predecessorPoint) 36
def receiver : Fin model.source.code.sites := ⟨2,by change 2<3;decide⟩
def previousReceiver : Fin predecessorModel.source.code.sites := ⟨2,by change 2<3;decide⟩
def observed := CachedWorkDispatch.run vocabulary reception trace.rows receiver trace.rows.length
def decision := CachedWorkDispatch.produce vocabulary origin reception trace.rows receiver scope 1
def previousVocabulary := SuccessorSigningSource.vocabulary predecessorModel predecessorPoint base
def previousReception : StageReception.Law predecessorModel.source.code :=
 ⟨fun receiver current => {(laws predecessorModel).scope receiver current with phase := predecessorPoint.cut},64⟩

theorem the_actual_predecessor_has_spent_production_inputs_but_paid_execution_capacity :
 predecessorSeed.current.stock 1 .energy=0 ∧ predecessorSeed.current.stock 1 .labor=0 ∧
 predecessorSeed.current.stock 1 .service=6 ∧ predecessorSeed.frame.sent.length=2 ∧ predecessorSeed.remaining=100 := by
 and_intros <;> decide +kernel

theorem the_new_delivery_address_is_generated_from_the_actual_source_gap :
 missingAddress=some 4 ∧ .deliver target∉predecessorModel.source.code.eventAlphabet ∧
 .deliver target∈model.source.code.eventAlphabet := by and_intros <;> decide +kernel

theorem registration_generates_an_actual_new_packet_delivery_and_authenticated_decision :
 decision=.decided true ∧ (observed.receipts.any fun receipt => receipt.wire.serial=target)=true := by
 and_intros <;> decide +kernel

theorem the_same_actual_control_without_registration_sends_but_cannot_decide :
 (CachedWorkDispatch.wires previousVocabulary withoutRegistration.rows).isEmpty=false ∧
 CachedWorkDispatch.produce previousVocabulary predecessorPoint previousReception withoutRegistration.rows
  previousReceiver scope 1=.blocked .missingQuorum := by
 and_intros <;> decide +kernel

theorem successful_communication_preserves_the_actual_production_obstruction :
 decision=.decided true ∧ ¬model.source.code.law.Valid trace.before.current RecycledQuorumMaterial.production ∧
 trace.before.current.stock 1 .energy=0 ∧ trace.before.current.stock 1 .labor=0 := by
 and_intros <;> decide +kernel

theorem actual_communication_spends_its_original_service_and_execution_budget :
 trace.before.current.stock 1 .service=1 ∧ trace.before.remaining=64 ∧
 (∀ instrument debtor creditor,trace.before.current.claims instrument debtor creditor=
  predecessorSeed.current.claims instrument debtor creditor) := by
 and_intros <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceOpportunitySource
