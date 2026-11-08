import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProviderMaterialSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProviderMaterialCapacity
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ProviderMaterialSource
noncomputable section

theorem the_source_budget_exactly_matches_actual_input_and_execution_capacity (units : Nat) :
 units≤budget ↔ affordable units := by
 have stocks := the_actual_provider_has_three_units_of_each_real_input
 rw [the_source_computes_its_material_execution_budget]
 unfold affordable
 rw [stocks.1,stocks.2.1,stocks.2.2.1,stocks.2.2.2.2.2.1]
 constructor
 · intro bounded
   refine ⟨?_,?_,?_,by omega⟩ <;> exact_mod_cast bounded
 · intro enough
   exact_mod_cast enough.1

theorem every_source_affordable_request_is_actually_supplied
 (units : Nat) (bounded : units≤budget) :
 status units true true=.supplied ∧ (trace units true true).before.current.stock 1 .feedstock=(units : ℚ) := by
 rw [the_source_computes_its_material_execution_budget] at bounded
 interval_cases units <;> constructor <;> decide +kernel

def vocabulary := SuccessorSigningSource.vocabulary model origin ConcreteProductiveSource.base
def reception : StageReception.Law model.source.code :=
 ⟨fun _ _ => {ConcreteProductiveSource.scope with phase := origin.cut},64⟩
def scope := {ConcreteProductiveSource.scope with phase := origin.cut}
def receiver : Fin model.source.code.sites := ⟨2,by change 2<3;decide⟩
def decision := CachedWorkDispatch.produce vocabulary origin reception (trace 3 true true).rows receiver scope 1

theorem real_material_output_does_not_fabricate_signatures_packets_or_quorum :
 (CachedWorkDispatch.ledger vocabulary (trace 3 true true).rows).isEmpty=true ∧
 (CachedWorkDispatch.wires vocabulary (trace 3 true true).rows).isEmpty=true ∧
 decision=.blocked .missingQuorum := by and_intros <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProviderMaterialCapacity
