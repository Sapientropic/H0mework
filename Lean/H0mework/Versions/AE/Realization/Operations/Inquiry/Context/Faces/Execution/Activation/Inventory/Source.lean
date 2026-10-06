import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime
import H0mework.Realization.Operations.Execution.Relations.History.Laws
import H0mework.Realization.Operations.Execution.Coefficients.Words
import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Closure
import H0mework.Realization.Completion.FaithfulResidual
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
abbrev physical := Context.Installation.materialAt frame occurrence
def priorSeed := match frame.inventory with
  | none => seed
  | some material => SourceHistoryCommon.seed seed material
abbrev updatedSeed := SourceHistoryCommon.seed (priorSeed seed frame)
  (SourceOperationPaidRelations.exposure (physical frame occurrence).paid.state.2)
abbrev history := RootGeneratedCofinalHistoryAt.generate (rootOccurrence:=RootedAccountedUnfolding.zero occurrence)
  (seedOccurrence:=updatedSeed seed frame occurrence)
  (continuationOccurrence:=SourceOperationPaidRelations.continuation (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev evaluator := SourceOperationPaidRelations.evaluator (sort:=sort) (physical frame occurrence).raw.environment
abbrev face := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.generate
  (history:=history seed frame occurrence) (evaluatorOccurrence:=evaluator frame occurrence)
abbrev disposition := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.settleWithResidual (face seed frame occurrence)

def kernelWord (sound : GeneratedRelationSoundnessAt (face seed frame occurrence))
    (coordinate : GeneratedKernelResidualCoordinateAt (face seed frame occurrence) sound) :
    (history seed frame occurrence).generatorClosure :=
  Classical.choose (Submodule.Quotient.mk_surjective (history seed frame occurrence).relationInGeneratorClosure coordinate.coordinate.val)

def residualWord (selected : ResidualDispositionOutcome (face seed frame occurrence)) :
    Formal ℤ PhysicalValue PhysicalVar sort :=
  match selected with
  | .faithful _ _ _ => SourceOperationScalarPresentation.relationMap (R:=ℤ)
      (physical frame occurrence).raw.environment (physical frame occurrence).relations
  | .unsound _ coordinate => coordinate.relation
  | .kernelResidual sound _ coordinate => (kernelWord seed frame occurrence sound coordinate).val
  | .coverageResidual _ _ coordinate => Finsupp.single (.const coordinate.representative) 1


def ReadoutAt (selected : ResidualDispositionOutcome (face seed frame occurrence)) : Type u :=
  match selected with
  | .faithful _ _ _ => (history seed frame occurrence).CompletionCarrier ≃+ PhysicalValue sort
  | .unsound _ coordinate => type_of% coordinate
  | .kernelResidual _ _ coordinate => type_of% coordinate
  | .coverageResidual _ _ coordinate => type_of% coordinate

def readout (selected : ResidualDispositionOutcome (face seed frame occurrence)) :
    ReadoutAt seed frame occurrence selected :=
  match selected with
  | .faithful _ _ realization => realization.canonicalQuotientAddEquiv
  | .unsound _ coordinate => coordinate
  | .kernelResidual _ _ coordinate => coordinate
  | .coverageResidual _ _ coordinate => coordinate


def relationWrite (selected : ResidualDispositionOutcome (face seed frame occurrence)) :=
  match selected with
  | .kernelResidual sound _ coordinate =>
      SourceHistoryCommon.seed (updatedSeed seed frame occurrence)
        (.zero (.relation (kernelWord seed frame occurrence sound coordinate).val))
  | .faithful _ _ _ | .unsound _ _ | .coverageResidual _ _ _ => updatedSeed seed frame occurrence

abbrev writtenSeed := relationWrite seed frame occurrence (disposition seed frame occurrence)

def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) :=
  ⟨pairEnvironment (physical frame occurrence).raw.environment
    ((physical frame occurrence).nextRaw.environment-(physical frame occurrence).raw.environment),
   liftExpr (SourceOperationExecution.Coefficients.expression (residualWord seed frame occurrence (disposition seed frame occurrence)))⟩

def material := (physical frame occurrence,updatedSeed seed frame occurrence,evaluator frame occurrence,
  disposition seed frame occurrence,residualWord seed frame occurrence (disposition seed frame occurrence),raw seed frame occurrence,
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
    (Mother.baseState {frame with depth:=0}).root.toAuthoritativeRoot occurrence,writtenSeed seed frame occurrence))

def component : SourceNativeProjectionLaw
    (Mother.baseState {frame with depth:=0}).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} supplied _ => type_of% (material seed frame supplied)
  project := fun _ {_current} supplied _ => material seed frame supplied

def installedReader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (supplied : Context.Installation.Occurrence frame (current:=current)) :=
  ((component seed frame).project PUnit.unit supplied PUnit.unit).2.2.2.2.2.1

def programme : Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort) where
  LowVar := PhysicalVar
  datum sourceFrame := { component := some (component seed sourceFrame),reader := installedReader seed sourceFrame }
  nextInventory sourceFrame := some (((component seed {sourceFrame with depth:=0}).project PUnit.unit
    (sourceFrame.currentState.root.emitted sourceFrame.currentState.visit.current) PUnit.unit).2.2.2.2.2.2.2)
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
