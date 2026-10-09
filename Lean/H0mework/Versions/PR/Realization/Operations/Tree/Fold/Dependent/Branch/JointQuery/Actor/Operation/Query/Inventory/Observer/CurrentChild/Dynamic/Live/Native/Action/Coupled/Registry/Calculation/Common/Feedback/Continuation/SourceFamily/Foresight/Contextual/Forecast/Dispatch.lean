import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Generated
import H0mework.Realization.Logic.SourceScope
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (history)
end J
namespace R
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (pairInventory)
end R
namespace L
export SaturationMonoid.SourceOperationLogic (Scope q q_surjective)
end L
variable {S : Type u} {V X : S → Type u} [∀ t,AddCommGroup (V t)] {s : S}
variable {D : Type u} [AddCommGroup D] [Module ℤ D]
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr V X s)))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=V) (Var:=X) (sort:=s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
variable (source : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue V) (Var:=X) (sort:=s))
variable (e : Formal ℤ (PairValue V) X s →ₗ[ℤ] D)
def evaluator := RootedAccountedUnfolding.zero (fun term : Expr (PairValue V) X s=>L.q e (Finsupp.single term 1))
abbrev face := generate (history:=J.history seed frame occurrence) (evaluatorOccurrence:=evaluator e)
abbrev selected := (face seed frame occurrence e).settleWithResidual

def pointWord (point : L.Scope e) : Formal ℤ (PairValue V) X s := Classical.choose (L.q_surjective e point)
theorem point_word (point : L.Scope e) : L.q e (pointWord e point)=point :=Classical.choose_spec (L.q_surjective e point)
def kernelWord (sound : GeneratedRelationSoundnessAt (face seed frame occurrence e))
 (point : GeneratedKernelResidualCoordinateAt (face seed frame occurrence e) sound) :=
 Classical.choose (Submodule.Quotient.mk_surjective (J.history seed frame occurrence).relationInGeneratorClosure point.coordinate.val)

def queryRaw (outcome : ResidualDispositionOutcome (face seed frame occurrence e)) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue V) (Var:=X) (sort:=s) :=
 match outcome with
 | .faithful _ _ _ =>source
 | .unsound _ point =>⟨source.environment,Coefficients.expression point.relation⟩
 | .kernelResidual sound _ point =>⟨source.environment,Coefficients.expression (kernelWord seed frame occurrence e sound point).val⟩
 | .coverageResidual _ _ point =>⟨source.environment,Coefficients.expression (pointWord e point.representative)⟩

def written (outcome : ResidualDispositionOutcome (face seed frame occurrence e)) :=
 match outcome with
 | .kernelResidual sound _ point =>SourceHistoryCommon.seed (R.pairInventory seed frame occurrence)
  (.zero (.relation (kernelWord seed frame occurrence e sound point).val))
 | .faithful _ _ _ | .unsound _ _ | .coverageResidual _ _ _ =>R.pairInventory seed frame occurrence

theorem query_environment (outcome : ResidualDispositionOutcome (face seed frame occurrence e)) :
 (queryRaw seed frame occurrence source e outcome).environment=source.environment :=by cases outcome <;>rfl

theorem written_preserves (outcome : ResidualDispositionOutcome (face seed frame occurrence e)) :
 ∀ event ∈ (R.pairInventory seed frame occurrence).trace,event ∈ (written seed frame occurrence e outcome).trace :=by
 cases outcome with
 | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ =>exact fun _ present=>present
 | kernelResidual _ _ _ =>exact (SourceHistoryCommon.parallel_left _ _ _).1

theorem free_evaluation (word : Formal ℤ (PairValue V) X s) :
 (face seed frame occurrence e).freeEvaluation word=L.q e word :=by
 classical
 induction word using Finsupp.induction with
 | zero =>exact (face seed frame occurrence e).freeEvaluation.map_zero
 | @single_add term integer rest absent nonzero prior =>
  rw [map_add,map_add,freeEvaluation_single,prior]
  change integer • L.q e (Finsupp.single term 1)+_=L.q e (Finsupp.single term integer)+_
  congr 1
  rw [←map_smul]
  simp only [Finsupp.smul_single,smul_eq_mul,mul_one]

end Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
