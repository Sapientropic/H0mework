import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Laws
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming
open RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects
open SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
open RootInquiryCompletion

abbrev disposition (count : Nat) := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.settleWithResidual
  (face root visit recognition count)
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

def OutputAt (count : Nat) (selected : ResidualDispositionOutcome (face root visit recognition count)) : Type u :=
  match selected with
  | .faithful _ _ _ => (combined root visit recognition count).CompletionCarrier ≃+ Value root visit recognition SourceOperationNative.Tree.Fold.Slot.result
  | .unsound _ _ => GeneratedRelationResidualCoordinateAt (face root visit recognition count)
  | .kernelResidual sound _ _ => GeneratedKernelResidualCoordinateAt (face root visit recognition count) sound
  | .coverageResidual sound _ _ => GeneratedCoverageResidualCoordinateAt (face root visit recognition count) sound

def output (count : Nat) : OutputAt root visit recognition count (disposition root visit recognition count) := by
  generalize selectedEq : disposition root visit recognition count = selected
  cases selected with
  | faithful sound coverage proof => exact proof.canonicalQuotientAddEquiv
  | unsound obstruction coordinate => exact coordinate
  | kernelResidual sound obstruction coordinate => exact coordinate
  | coverageResidual sound obstruction coordinate => exact coordinate
end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
