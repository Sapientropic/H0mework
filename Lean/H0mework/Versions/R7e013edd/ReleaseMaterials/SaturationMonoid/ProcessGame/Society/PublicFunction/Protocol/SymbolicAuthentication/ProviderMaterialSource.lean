import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionReviewConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProviderMaterialSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
noncomputable section

def model := CompletionReviewSource.model
def origin := CompletionReviewSource.trace.cursor
def before := CompletionReviewSource.trace.before

def affordable (units : Nat) : Prop :=
 (units : ℚ)≤before.current.stock 2 .waste ∧ (units : ℚ)≤before.current.stock 2 .energy ∧
 (units : ℚ)≤before.current.stock 2 .labor ∧ 4*units≤before.remaining
instance (units : Nat) : Decidable (affordable units) := by unfold affordable;infer_instance
-- The quota is recomputed from the actual provider inputs and actual remaining execution.
def budget := (((List.range (before.remaining+1)).filter fun units => decide (affordable units)).getLast?).getD 0

def eventFor (request : RecycledQuorumMaterial.Action) : LocalCommandSource.Input :=
 match (List.range model.source.code.eventAlphabet.length).find?
  (fun index => decide (model.source.code.eventAlphabet[index]?=some (.adversary request))) with
 | none => .idle
 | some index => .event index

def control (units : Nat) (produce deliver : Bool) (trace : SourceContinuationTrace.Trace model) : LocalCommandSource.Input :=
 if before.current.stock 1 .feedstock+(units : ℚ)≤trace.before.current.stock 1 .feedstock then .idle
 else if (CachedCommandRun.ownerAt model trace.cursor trace.before).isSome then .idle
 else if 1≤trace.before.current.stock 2 .feedstock then
  if deliver && decide (model.source.code.law.Valid trace.before.current RecycledQuorumMaterial.feed)
  then eventFor RecycledQuorumMaterial.feed else .idle
 else if produce && decide (model.source.code.law.Valid trace.before.current RecycledQuorumMaterial.recycle)
 then eventFor RecycledQuorumMaterial.recycle else .idle

def trace (units : Nat) (produce deliver : Bool) :=
 SourceOpportunityHandoff.controlled model origin before (control units produce deliver) (4*units)

inductive Obstruction where
 | executionBudget | providerWithheld | deliveryWithheld | materialInputs | boundedOpportunity
 deriving DecidableEq
inductive Status where
 | supplied | blocked (reason : Obstruction)
 deriving DecidableEq

def status (units : Nat) (produce deliver : Bool) : Status :=
 let after := (trace units produce deliver).before
 if before.current.stock 1 .feedstock+(units : ℚ)≤after.current.stock 1 .feedstock then .supplied
 else if after.remaining=0 then .blocked .executionBudget
 else if !produce then .blocked .providerWithheld
 else if 1≤after.current.stock 2 .feedstock ∧ !deliver then .blocked .deliveryWithheld
 else if ¬model.source.code.law.Valid after.current RecycledQuorumMaterial.recycle then .blocked .materialInputs
 else .blocked .boundedOpportunity

theorem the_actual_provider_has_three_units_of_each_real_input :
 before.current.stock 2 .waste=3 ∧ before.current.stock 2 .energy=3 ∧ before.current.stock 2 .labor=3 ∧
 before.current.stock 1 .feedstock=0 ∧ before.current.stock 2 .feedstock=0 ∧ before.remaining=38 ∧
 model.source.code.law.Valid before.current RecycledQuorumMaterial.recycle ∧
 .adversary RecycledQuorumMaterial.recycle∈model.source.code.eventAlphabet ∧
 .adversary RecycledQuorumMaterial.feed∈model.source.code.eventAlphabet := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem the_source_computes_its_material_execution_budget : budget=3 := by decide +kernel

theorem three_actual_productions_and_transfers_generate_three_new_feedstock_units :
 status 3 true true=.supplied ∧ (trace 3 true true).before.current.stock 1 .feedstock=3 ∧
 (trace 3 true true).before.current.stock 2 .feedstock=0 ∧ (trace 3 true true).before.current.stock 2 .waste=0 ∧
 (trace 3 true true).before.current.stock 2 .energy=0 ∧ (trace 3 true true).before.current.stock 2 .labor=0 ∧
 (trace 3 true true).before.remaining=26 := by and_intros <;> decide +kernel

theorem production_and_delivery_are_independently_controlled :
 status 3 false true=.blocked .providerWithheld ∧ (trace 3 false true).before.current.stock 1 .feedstock=0 ∧
 status 3 true false=.blocked .deliveryWithheld ∧ (trace 3 true false).before.current.stock 1 .feedstock=0 ∧
 (trace 3 true false).before.current.stock 2 .feedstock=1 := by and_intros <;> decide +kernel

theorem a_fourth_unit_is_blocked_by_the_actual_spent_material_inputs :
 status 4 true true=.blocked .materialInputs ∧ (trace 4 true true).before.current.stock 1 .feedstock=3 ∧
 ¬model.source.code.law.Valid (trace 3 true true).before.current RecycledQuorumMaterial.recycle := by and_intros <;> decide +kernel

theorem material_progress_keeps_all_debt_native_epoch_and_zero_service :
 (∀ instrument debtor creditor,(trace 3 true true).before.current.claims instrument debtor creditor=before.current.claims instrument debtor creditor) ∧
 (trace 3 true true).before.current.technology.version=1 ∧
 (trace 3 true true).before.current.stock 1 .service=0 ∧ (trace 3 true true).before.current.stock 2 .service=0 ∧
 ¬model.source.code.law.Valid (trace 3 true true).before.current RecycledQuorumMaterial.production := by and_intros <;> decide +kernel

theorem wrong_provider_and_a_bare_transfer_cannot_manufacture_input :
 ¬model.source.code.law.Valid before.current {RecycledQuorumMaterial.recycle with signer := 1} ∧
 ¬model.source.code.law.Valid before.current RecycledQuorumMaterial.feed := by and_intros <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProviderMaterialSource
