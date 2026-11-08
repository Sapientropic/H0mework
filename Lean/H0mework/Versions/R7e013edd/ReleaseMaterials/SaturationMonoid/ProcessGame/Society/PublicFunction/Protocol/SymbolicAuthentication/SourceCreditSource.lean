import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCreditHandoff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCreditSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws)
noncomputable section

def predecessorModel := SourceOpportunitySource.model
def predecessorPoint := SourceOpportunitySource.trace.cursor
def predecessorSeed := SourceOpportunitySource.trace.before
def creditModel := SourceCreditHandoff.modelAfter predecessorModel predecessorPoint predecessorSeed
def creditPoint := SourceCreditHandoff.point predecessorModel predecessorPoint predecessorSeed
def creditSeed := SourceCreditHandoff.after predecessorModel predecessorSeed

def borrower (bound : SourceCreditHandoff.Model) (trace : SourceContinuationTrace.Trace bound) : LocalCommandSource.Input :=
 if trace.before.current.claims () 1 2=7 then
  match (List.range bound.source.code.actions.length).find?
   (fun index => decide (bound.source.code.actions[index]?=some SourceCreditHandoff.issue)) with
  | none => .idle
  | some index => .command index
 else .idle

def issued := SourceOpportunityHandoff.controlled creditModel creditPoint creditSeed (borrower creditModel) 2
-- The old payer transfers real waste; the original provider supplies the service payout.
def exchange : PaidInvocationSource.Contract (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit) :=
 ⟨1,2,.waste,1,36,RecycledQuorumMaterial.waste,SourceCreditHandoff.payout⟩
def model (accept : Bool) := SourceWindowCache.modelAfter exchange true accept creditModel issued.cursor issued.before
def origin (accept : Bool) := SourceWindowCache.point creditModel.source.code exchange issued.cursor issued.before true accept
def before (accept : Bool) := SourceWindowCache.after creditModel.source.code exchange issued.cursor issued.before true accept
def vocabulary (accept : Bool) := SuccessorSigningSource.vocabulary (model accept) (origin accept) base
def reception (accept : Bool) : StageReception.Law (model accept).source.code :=
 ⟨fun receiver current => {(laws (model accept)).scope receiver current with phase := (origin accept).cut},64⟩
def scope (accept : Bool) := {ConcreteProductiveSource.scope with phase := (origin accept).cut}

def control (accept : Bool) (trace : SourceContinuationTrace.Trace (model accept)) : LocalCommandSource.Input :=
 let target := (before accept).frame.sent.length
 if (CachedCommandRun.ownerAt (model accept) trace.cursor trace.before).isSome then
  if target<trace.before.frame.sent.length then .idle
  else SourceContinuationTrace.choose (model accept) (origin accept) target base (laws (model accept))
    [RecycledQuorumSource.fee false] trace
 else if target<trace.before.frame.sent.length ∧ !(trace.rows.any fun row => HeaderReception.delivered row target) then
  match (List.range (model accept).source.code.eventAlphabet.length).find?
   (fun index => decide ((model accept).source.code.eventAlphabet[index]?=some (.deliver target))) with
  | none => .idle
  | some index => .event index
 else .idle

def trace (accept : Bool) := SourceOpportunityHandoff.controlled (model accept) (origin accept) (before accept) (control accept) 18
def receiver (accept : Bool) : Fin (model accept).source.code.sites := ⟨2,by change 2<3;decide⟩
def observed (accept : Bool) := CachedWorkDispatch.run (vocabulary accept) (reception accept)
 (trace accept).rows (receiver accept) (trace accept).rows.length
def decision (accept : Bool) := CachedWorkDispatch.produce (vocabulary accept) (origin accept) (reception accept)
 (trace accept).rows (receiver accept) (scope accept) 1

theorem actual_source_admission_generates_the_original_second_credit :
 SourceCreditHandoff.offered predecessorModel predecessorSeed=true ∧
 issued.before.current.claims () 1 2=10 ∧ issued.before.current.stock 1 .service=1 ∧
 issued.before.current.stock 2 .service=3 := by and_intros <;> decide +kernel

theorem real_waste_and_provider_payout_open_the_actual_new_window :
 SourceWindowCache.admitted creditModel.source.code exchange issued.cursor issued.before true true=true ∧
 (before true).current.stock 1 .service=4 ∧ (before true).current.stock 2 .service=0 ∧
 (before true).current.stock 1 .waste=0 ∧ (before true).current.claims () 1 2=10 ∧
 (before true).remaining=96 := by and_intros <;> decide +kernel

theorem missing_provider_retains_new_debt_but_cannot_open_the_window_or_decide :
 SourceWindowCache.admitted creditModel.source.code exchange issued.cursor issued.before true false=false ∧
 (before false).current.claims () 1 2=10 ∧ (before false).current.stock 2 .service=3 ∧
 (before false).remaining=60 ∧ decision false=.blocked .missingQuorum := by and_intros <;> decide +kernel

theorem the_financed_phase_generates_a_new_actual_authenticated_decision :
 decision true=.decided true ∧ ((observed true).receipts.any fun receipt =>
 receipt.wire.serial=(before true).frame.sent.length)=true ∧
 (trace true).before.current.stock 1 .service=1 ∧ (trace true).before.remaining=78 := by
 and_intros <;> decide +kernel

theorem successful_communication_keeps_the_actual_new_debt_and_material_obstruction :
 (∀ instrument debtor creditor,(trace true).before.current.claims instrument debtor creditor=
 predecessorSeed.current.claims instrument debtor creditor+(if debtor=1 ∧ creditor=2 then 3 else 0)) ∧
 ¬(model true).source.code.law.Valid (trace true).before.current RecycledQuorumMaterial.production := by
 and_intros <;> decide +kernel

theorem the_same_credit_and_payout_cannot_be_paid_twice :
 ¬(model true).source.code.law.Valid (trace true).before.current SourceCreditHandoff.issue ∧
 ¬(model true).source.code.law.Valid (trace true).before.current SourceCreditHandoff.payout ∧
 ¬creditModel.source.code.law.Valid issued.before.current {SourceCreditHandoff.payout with signer := 1} := by
 and_intros <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCreditSource
