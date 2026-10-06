import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Runtime
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.RawState
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
abbrev history := RootGeneratedCofinalHistoryAt.generate
  (rootOccurrence:=RootedAccountedUnfolding.zero occurrence)
  (seedOccurrence:=pairInventory seed frame occurrence)
  (continuationOccurrence:=SourceOperationPaidRelations.continuation
    (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev evaluator := SourceOperationPaidRelations.evaluator (sort:=sort) (raw seed frame occurrence).environment
abbrev face := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.generate
  (history:=history seed frame occurrence) (evaluatorOccurrence:=evaluator seed frame occurrence)
abbrev disposition := (face seed frame occurrence).settleWithResidual
def kernelWord (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    (history seed frame occurrence).generatorClosure :=
  Classical.choose (Submodule.Quotient.mk_surjective (history seed frame occurrence).relationInGeneratorClosure
    coordinate.coordinate.val)
def queryRaw (selected : ResidualDispositionOutcome (face seed frame occurrence)) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) :=
  match selected with
  | .faithful _ _ _ => raw seed frame occurrence
  | .unsound _ coordinate => ⟨(raw seed frame occurrence).environment,
      SourceOperationExecution.Coefficients.expression coordinate.relation⟩
  | .kernelResidual sound _ coordinate => ⟨(raw seed frame occurrence).environment,
      SourceOperationExecution.Coefficients.expression (kernelWord seed frame occurrence sound coordinate).val⟩
  | .coverageResidual _ _ coordinate => ⟨(raw seed frame occurrence).environment,.const coordinate.representative⟩
def writtenInventory (selected : ResidualDispositionOutcome (face seed frame occurrence)) :=
  match selected with
  | .kernelResidual sound _ coordinate => SourceHistoryCommon.seed (pairInventory seed frame occurrence)
      (.zero (.relation (kernelWord seed frame occurrence sound coordinate).val))
  | .faithful _ _ _ | .unsound _ _ | .coverageResidual _ _ _ => pairInventory seed frame occurrence
def queryReader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :=
  queryRaw seed frame supplied (disposition seed frame supplied)
abbrev queryResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (Mother.baseState {frame with depth:=0}).root.toAuthoritativeRoot (queryReader seed frame) occurrence
def completeWrittenInventory := SourceHistoryCommon.seed
  (writtenInventory seed frame occurrence (disposition seed frame occurrence))
  (SourceOperationPaidRelations.exposure (queryResult seed frame occurrence).2.1.2)

def material := (Residual.material seed frame occurrence,pairInventory seed frame occurrence,
  evaluator seed frame occurrence,disposition seed frame occurrence,
  queryRaw seed frame occurrence (disposition seed frame occurrence),
  completeWrittenInventory seed frame occurrence)
def component : SourceNativeProjectionLaw
    (Mother.baseState {frame with depth:=0}).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} supplied _ => type_of% (material seed frame supplied)
  project := fun _ {_current} supplied _ => material seed frame supplied

def reader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :=
  queryReader seed frame supplied

def configuration : Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort) where
  LowVar := PhysicalVar
  datum sourceFrame := { component:=some (component seed sourceFrame),reader:=reader seed sourceFrame }
  nextInventory := (programme seed).nextInventory
  nextPairInventory sourceFrame := some (((component seed {sourceFrame with depth:=0}).project PUnit.unit
    (sourceFrame.currentState.root.emitted sourceFrame.currentState.visit.current) PUnit.unit).2.2.2.2.2)
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
