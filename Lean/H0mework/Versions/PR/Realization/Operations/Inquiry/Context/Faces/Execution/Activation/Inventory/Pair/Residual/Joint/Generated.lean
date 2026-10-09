import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.History
set_option autoImplicit false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Generated
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace Mother
export SourceOperationInquiry.Context.Faces.Execution.Mother (baseState)
end Mother
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
  (history)
end J
namespace R
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
  (raw pairInventory)
end R
variable {S : Type u} {V X : S → Type u} [∀ t,AddCommGroup (V t)] {s : S}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr V X s)))
variable (frame : M.Frame (Value:=V) (Var:=X) (sort:=s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
variable (sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue V) (Var:=X) (sort:=s))

abbrev face := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.generate
  (history:=J.history seed frame occurrence)
  (evaluatorOccurrence:=SourceOperationPaidRelations.evaluator (sort:=s) sourceRaw.environment)
abbrev disposition := (face seed frame occurrence sourceRaw).settleWithResidual
def kernelWord (sound : GeneratedRelationSoundnessAt (face seed frame occurrence sourceRaw))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence sourceRaw) sound) :
    (J.history seed frame occurrence).generatorClosure :=
  Classical.choose (Submodule.Quotient.mk_surjective (J.history seed frame occurrence).relationInGeneratorClosure
    coordinate.coordinate.val)

def queryRaw (selected : ResidualDispositionOutcome (face seed frame occurrence sourceRaw)) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue V) (Var:=X) (sort:=s) :=
  match selected with
  | .faithful _ _ _ => sourceRaw
  | .unsound _ coordinate => ⟨sourceRaw.environment,SourceOperationExecution.Coefficients.expression coordinate.relation⟩
  | .kernelResidual sound _ coordinate => ⟨sourceRaw.environment,
      SourceOperationExecution.Coefficients.expression (kernelWord seed frame occurrence sourceRaw sound coordinate).val⟩
  | .coverageResidual _ _ coordinate => ⟨sourceRaw.environment,.const coordinate.representative⟩

def writtenInventory (selected : ResidualDispositionOutcome (face seed frame occurrence sourceRaw)) :=
  match selected with
  | .kernelResidual sound _ coordinate => SourceHistoryCommon.seed (R.pairInventory seed frame occurrence)
      (.zero (.relation (kernelWord seed frame occurrence sourceRaw sound coordinate).val))
  | .faithful _ _ _ | .unsound _ _ | .coverageResidual _ _ _ => R.pairInventory seed frame occurrence

theorem query_environment (selected : ResidualDispositionOutcome (face seed frame occurrence sourceRaw)) :
    (queryRaw seed frame occurrence sourceRaw selected).environment = sourceRaw.environment := by
  cases selected <;> rfl

theorem written_preserves (selected : ResidualDispositionOutcome (face seed frame occurrence sourceRaw)) :
    ∀ event ∈ (R.pairInventory seed frame occurrence).trace,
      event ∈ (writtenInventory seed frame occurrence sourceRaw selected).trace := by
  cases selected with
  | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ => exact fun _ belongs => belongs
  | kernelResidual _ _ _ => exact (SourceHistoryCommon.parallel_left _ _ _).1

variable (rawAt : {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered} →
  SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current) →
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue V) (Var:=X) (sort:=s))

def queryReader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :=
  queryRaw seed frame supplied (rawAt supplied) (disposition seed frame supplied (rawAt supplied))
abbrev queryResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (Mother.baseState {frame with depth:=0}).root.toAuthoritativeRoot (queryReader seed frame rawAt) occurrence
def completeWrittenInventory := SourceHistoryCommon.seed
  (writtenInventory seed frame occurrence (rawAt occurrence) (disposition seed frame occurrence (rawAt occurrence)))
  (SourceOperationPaidRelations.exposure (queryResult seed frame occurrence rawAt).2.1.2)

theorem complete_preserves : ∀ event ∈ (R.pairInventory seed frame occurrence).trace,
    event ∈ (completeWrittenInventory seed frame occurrence rawAt).trace := by
  intro event belongs
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event
    (written_preserves seed frame occurrence (rawAt occurrence) _ event belongs)

theorem complete_paid_trace :
    ∀ event ∈ (SourceOperationPaidRelations.exposure (queryResult seed frame occurrence rawAt).2.1.2).trace,
      event ∈ (completeWrittenInventory seed frame occurrence rawAt).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Generated

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
