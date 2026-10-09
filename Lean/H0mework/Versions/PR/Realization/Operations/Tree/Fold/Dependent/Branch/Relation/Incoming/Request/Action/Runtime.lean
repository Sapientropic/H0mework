import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Action.Continuation.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Action
open RootInquiryCompletion RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (count : Nat)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
abbrev generated (word : Word root visit recognition) :=
  (runtime root visit recognition count U7 calculus word,
    Continuation.generated root visit recognition count U7 calculus word)

def RunAt (selected : ResidualDispositionOutcome (face root visit recognition count)) : Type (u+15) :=
  match selected with
  | .faithful _ _ _ => ULift.{u+15} ((combined root visit recognition count).CompletionCarrier ≃+
      Value root visit recognition SourceOperationNative.Tree.Fold.Slot.result)
  | .unsound _ coordinate => ULift.{u+15} (type_of% (generated root visit recognition count U7 calculus coordinate.relation))
  | .kernelResidual sound _ coordinate => ULift.{u+15} (type_of% (generated root visit recognition count U7 calculus
      (kernelWord root visit recognition count sound coordinate).val))
  | .coverageResidual sound _ coordinate => ULift.{u+15} (type_of% (generated root visit recognition count U7 calculus
      (coverageWord root visit recognition count sound coordinate)))

def run : RunAt root visit recognition count U7 calculus (disposition root visit recognition count) := by
  generalize selectedEq : disposition root visit recognition count = selected
  cases selected with
  | faithful sound coverage realization => exact ⟨realization.canonicalQuotientAddEquiv⟩
  | unsound obstruction coordinate => exact ⟨generated root visit recognition count U7 calculus coordinate.relation⟩
  | kernelResidual sound obstruction coordinate => exact ⟨generated root visit recognition count U7 calculus
      (kernelWord root visit recognition count sound coordinate).val⟩
  | coverageResidual sound obstruction coordinate => exact ⟨generated root visit recognition count U7 calculus
      (coverageWord root visit recognition count sound coordinate)⟩

end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
