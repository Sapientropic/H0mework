import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Completion
import H0mework.Realization.Operations.Execution.Relations.History.Laws
import H0mework.Realization.Completion.FaithfulResidual
/-! The existing facade reads relation material installed by the same source before emission. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Relations
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))
variable (runtime : Runtime old origin reader)

def sourceFace : SourceNativeRootSemanticFaceAt runtime.current.root runtime.current.visit where
  projection := (baseInstallation old origin reader).embed (.inr (.inr PUnit.unit))
  active := PUnit.unit
  classifier_eq := rfl

abbrev current := (sourceFace old origin reader runtime).rootRead.1
abbrev exposure := (sourceFace old origin reader runtime).rootRead.2.1
abbrev evaluator := (sourceFace old origin reader runtime).rootRead.2.2
abbrev history := RootGeneratedCofinalHistoryAt.generate
  (rootOccurrence:=RootedAccountedUnfolding.zero runtime.emittedOccurrence)
  (seedOccurrence:=exposure old origin reader runtime)
  (continuationOccurrence:=SourceOperationPaidRelations.continuation (Value:=Value) (Var:=Var) (sort:=sort))
abbrev evaluationFace := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.generate
  (history:=history old origin reader runtime) (evaluatorOccurrence:=evaluator old origin reader runtime)
abbrev disposition := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.settleWithResidual
  (evaluationFace old origin reader runtime)

def OutputAt (selected : ResidualDispositionOutcome (evaluationFace old origin reader runtime)) : Type u :=
  match selected with
  | .faithful _ _ _ => (history old origin reader runtime).CompletionCarrier ≃+ Value sort
  | .unsound _ _ => GeneratedRelationResidualCoordinateAt (evaluationFace old origin reader runtime)
  | .kernelResidual sound _ _ => GeneratedKernelResidualCoordinateAt (evaluationFace old origin reader runtime) sound
  | .coverageResidual sound _ _ => GeneratedCoverageResidualCoordinateAt (evaluationFace old origin reader runtime) sound

def output : OutputAt old origin reader runtime (disposition old origin reader runtime) := by
  generalize selectedEq : disposition old origin reader runtime = selected
  cases selected with
  | faithful sound coverage proof => exact proof.canonicalQuotientAddEquiv
  | unsound obstruction coordinate => exact coordinate
  | kernelResidual sound obstruction coordinate => exact coordinate
  | coverageResidual sound obstruction coordinate => exact coordinate
def atPrefix (count : Nat) := output old origin reader (Completion.runtime old origin reader count)
def endpoint := output old origin reader (Completion.completedRuntime old origin reader)
end RootGeneratedDebtActivationJointSource.OwnerFree.Relations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
