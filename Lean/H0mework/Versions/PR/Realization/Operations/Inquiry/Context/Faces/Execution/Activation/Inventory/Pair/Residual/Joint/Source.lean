import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Generated
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
abbrev evaluator := SourceOperationPaidRelations.evaluator (sort:=sort) (raw seed frame occurrence).environment
abbrev face := Generated.face seed frame occurrence (raw seed frame occurrence)
abbrev disposition := Generated.disposition seed frame occurrence (raw seed frame occurrence)
def kernelWord (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    (history seed frame occurrence).generatorClosure :=
 Generated.kernelWord seed frame occurrence (raw seed frame occurrence) sound coordinate
def queryRaw (selected : ResidualDispositionOutcome (face seed frame occurrence)) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) :=
 Generated.queryRaw seed frame occurrence (raw seed frame occurrence) selected
def writtenInventory (selected : ResidualDispositionOutcome (face seed frame occurrence)) :=
 Generated.writtenInventory seed frame occurrence (raw seed frame occurrence) selected
def queryReader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :=
 Generated.queryReader seed frame (raw seed frame) supplied
abbrev queryResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (Mother.baseState {frame with depth:=0}).root.toAuthoritativeRoot (queryReader seed frame) occurrence
def completeWrittenInventory := Generated.completeWrittenInventory seed frame occurrence (raw seed frame)

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
