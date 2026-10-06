import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.History.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace PaidRelationActionDefect
universe c b
variable {C : Type c} {B : Type b} [AddCommGroup C] [Module ℤ C] [AddCommGroup B] [Module ℤ B]
variable (action : C →ₗ[ℤ] C) (observation : C →ₗ[ℤ] B)
def read := (LinearMap.range observation).subtype.comp (SourceGeneratedScalarDifferentialResidual.residualToRange observation)
theorem read_defect (direction : LinearMap.ker observation) :
 read observation (SourceGeneratedObservationAction.actionDefect action observation direction)=observation (action direction.val) := rfl
section Trace
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {Value Var : S → Type u} [∀ s,AddCommGroup (Value s)] {s : S}
variable (environment : Env Value Var) (binding : ∀ slot,Var slot → Expr Value Var slot)
variable {before after : Expr Value Var s} (trace : Trace environment before after)
theorem trace_action_value : evaluation (R:=ℤ) environment
    (substitution (R:=ℤ) binding (relationMap (R:=ℤ) environment (trace.relationWords (R:=ℤ))))=
    before.eval (SourceSubstitution.sourceEnvironment binding environment)-after.eval (SourceSubstitution.sourceEnvironment binding environment) := by
 have generated := LinearMap.congr_fun (evaluation_substitution (R:=ℤ) (s:=s) binding environment)
   (relationMap (R:=ℤ) environment (trace.relationWords (R:=ℤ)))
 exact generated.trans (by
   rw [trace.relation_boundary]
   simp only [map_sub,evaluation,Finsupp.linearCombination_single,one_smul]
   rfl)
theorem boundary_value (expression : Expr Value Var s) (value : Value s) :
 evaluation (R:=ℤ) environment (substitution (R:=ℤ) binding
  (Finsupp.single expression 1-Finsupp.single (.const value) 1))=
 expression.eval (SourceSubstitution.sourceEnvironment binding environment)-value := by
 have square := LinearMap.congr_fun (evaluation_substitution (R:=ℤ) (s:=s) binding environment)
  (Finsupp.single expression 1-Finsupp.single (.const value) 1)
 exact square.trans (by
  simp only [map_sub,evaluation,Finsupp.linearCombination_single,one_smul,Expr.eval]
  rfl)
end Trace
theorem history_difference (stage : Nat) : SourceGeneratedLineageInventory.history (stage+1)-
    SourceGeneratedLineageInventory.history stage=Finsupp.single (stage+1) 1 := by
 rw [SourceGeneratedLineageInventory.history_inventory,SourceGeneratedLineageInventory.history_inventory,Finset.sum_range_succ]
 abel
open SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
theorem history_word_difference (stage : Nat) :
    PaidSourceMacroHistory.historyWord.{u} (stage+1)-PaidSourceMacroHistory.historyWord.{u} stage=
      PaidSourceMacroLineage.actualWord.{u} (stage+1) := by
 change PaidSourceMacroLineage.raiseWord.{u} (SourceGeneratedLineageInventory.history (stage+1))-
   PaidSourceMacroLineage.raiseWord.{u} (SourceGeneratedLineageInventory.history stage)=_
 rw [← map_sub,history_difference]
 simp only [PaidSourceMacroLineage.raiseWord,PaidSourceMacroLineage.actualWord,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
end PaidRelationActionDefect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
