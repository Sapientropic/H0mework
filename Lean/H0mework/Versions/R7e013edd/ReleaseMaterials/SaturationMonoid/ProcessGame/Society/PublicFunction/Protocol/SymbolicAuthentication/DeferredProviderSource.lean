import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCreditConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeferredProviderSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws)
noncomputable section

def model := SourceCreditSource.model false
def saved := SourceCreditSource.origin false
def retained := SourceCreditSource.before false

-- A later provider participates through the original registered acceptance event.
def provider (allow : Bool) (trace : SourceContinuationTrace.Trace model) : LocalCommandSource.Input :=
 if (CachedCommandRun.ownerAt model trace.cursor trace.before).isSome then .idle
 else if allow && decide (model.source.code.law.Valid trace.before.current SourceCreditSource.exchange.acceptance) then
  match (List.range model.source.code.eventAlphabet.length).find?
   (fun index => decide (model.source.code.eventAlphabet[index]?=some (.adversary SourceCreditSource.exchange.acceptance))) with
  | none => .idle
  | some index => .event index
 else .idle

def recovery (allow : Bool) := SourceOpportunityHandoff.controlled model saved retained (provider allow) 2
def origin (allow : Bool) := (recovery allow).cursor
def before (allow : Bool) := (recovery allow).before
def vocabulary (allow : Bool) := SuccessorSigningSource.vocabulary model (origin allow) base
def reception (allow : Bool) : StageReception.Law model.source.code :=
 ⟨fun receiver current => {(laws model).scope receiver current with phase := (origin allow).cut},64⟩
def scope (allow : Bool) := {ConcreteProductiveSource.scope with phase := (origin allow).cut}

def transport (allow : Bool) (trace : SourceContinuationTrace.Trace model) : LocalCommandSource.Input :=
 let target := (before allow).frame.sent.length
 if (CachedCommandRun.ownerAt model trace.cursor trace.before).isSome then
  if target<trace.before.frame.sent.length then .idle
  else SourceContinuationTrace.choose model (origin allow) target base (laws model) [RecycledQuorumSource.fee false] trace
 else if target<trace.before.frame.sent.length ∧ !(trace.rows.any fun row => HeaderReception.delivered row target) then
  match (List.range model.source.code.eventAlphabet.length).find?
   (fun index => decide (model.source.code.eventAlphabet[index]?=some (.deliver target))) with
  | none => .idle
  | some index => .event index
 else .idle

def trace (allow : Bool) := SourceOpportunityHandoff.controlled model (origin allow) (before allow) (transport allow) 18
def receiver : Fin model.source.code.sites := ⟨2,by change 2<3;decide⟩
def observed (allow : Bool) := CachedWorkDispatch.run (vocabulary allow) (reception allow) (trace allow).rows receiver (trace allow).rows.length
def decision (allow : Bool) := CachedWorkDispatch.produce (vocabulary allow) (origin allow) (reception allow)
 (trace allow).rows receiver (scope allow) 1

theorem the_actual_refusal_keeps_the_paid_waste_and_unpaid_supply :
 retained.current.claims () 1 2=10 ∧ retained.current.stock 1 .waste=0 ∧
 retained.current.stock 1 .service=1 ∧ retained.current.stock 2 .service=3 ∧ retained.remaining=60 := by
 and_intros <;> decide +kernel

theorem late_provider_service_is_actual_and_never_recharges_the_payer :
 (before true).current.stock 1 .service=4 ∧ (before true).current.stock 2 .service=0 ∧
 (before true).current.stock 1 .waste=0 ∧ (before true).remaining=58 ∧
 (∀ instrument debtor creditor,(before true).current.claims instrument debtor creditor=retained.current.claims instrument debtor creditor) ∧
 (recovery true).rows.any (fun row => decide (row.submitted=[SourceCreditSource.exchange.acceptance]))=true := by
 and_intros <;> decide +kernel

theorem the_later_actual_service_generates_a_new_authenticated_decision :
 decision true=.decided true ∧ ((observed true).receipts.any fun receipt =>
 receipt.wire.serial=(before true).frame.sent.length)=true ∧
 (trace true).before.current.stock 1 .service=1 ∧ (trace true).before.remaining=40 := by
 and_intros <;> decide +kernel

theorem continued_provider_absence_retains_the_debt_and_blocks_the_decision :
 (before false).current.stock 2 .service=3 ∧ (before false).current.claims () 1 2=10 ∧
 decision false=.blocked .missingQuorum := by and_intros <;> decide +kernel

theorem late_success_does_not_erase_debt_or_create_material_inputs :
 (∀ instrument debtor creditor,(trace true).before.current.claims instrument debtor creditor=retained.current.claims instrument debtor creditor) ∧
 ¬model.source.code.law.Valid (trace true).before.current RecycledQuorumMaterial.production ∧
 ¬model.source.code.law.Valid (trace true).before.current SourceCreditSource.exchange.acceptance := by
 and_intros <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeferredProviderSource
