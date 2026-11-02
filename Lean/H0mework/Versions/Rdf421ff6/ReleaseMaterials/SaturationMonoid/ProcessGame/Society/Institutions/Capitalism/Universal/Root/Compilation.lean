import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.FreshPayment

/-!
# Exact source-program seam at the original Society inquiry face

This module is an installer interface.  Its revision argument is the
outstanding material-source producer obligation, not a completed domain
result.  The named material producer will supply that value before generating
the program token.  No existing canonical runtime is replaced here.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Compilation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open M9ProofCarryingRenewalInquiryRoot
open M14SourceGeneratedContributionMergeActionSource

variable (oldVisit : OldVisit) (sourceIndex boundary : Nat)

abbrev Revision := FieldGroundedTypedSemanticWorldNetworkRevisionAt
  (FreshPayment.frontier oldVisit sourceIndex boundary).rooted

def core (revision : Revision oldVisit sourceIndex boundary) :
    SourceGeneratedInquiryU8RevisionCoreAt
      jointRoot (FreshPayment.visit oldVisit sourceIndex boundary)
      RootInquiryU8CompletionRegression.U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory ()
      (ULift.up.{1, 0} (jointRoot.emitted
        (FreshPayment.visit oldVisit sourceIndex boundary).current))
      M9ProofCarryingRenewalU8Failure.entry
      (FreshPayment.authority oldVisit sourceIndex boundary)
      RootInquiryU8CompletionRegression.obstruction
      RootInquiryU8CompletionRegression.u7Gate
      RootInquiryU8CompletionRegression.failure :=
  ⟨FreshPayment.frontier oldVisit sourceIndex boundary, revision⟩

def output (revision : Revision oldVisit sourceIndex boundary) :
    SourceNativeInquiryCompilationAt
      jointRoot (FreshPayment.visit oldVisit sourceIndex boundary)
      RootInquiryU8CompletionRegression.U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory ()
      (ULift.up.{1, 0} (jointRoot.emitted
        (FreshPayment.visit oldVisit sourceIndex boundary).current))
      M9ProofCarryingRenewalU8Failure.entry
      (FreshPayment.authority oldVisit sourceIndex boundary) :=
  .requiresU8 RootInquiryU8CompletionRegression.obstruction
    RootInquiryU8CompletionRegression.u7Gate
    RootInquiryU8CompletionRegression.failure
    (core oldVisit sourceIndex boundary revision)

def program (revision : Revision oldVisit sourceIndex boundary) :
    SourceNativeInquiryCompilationProgramAt
      jointRoot (FreshPayment.visit oldVisit sourceIndex boundary)
      RootInquiryU8CompletionRegression.U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory ()
      (ULift.up.{1, 0} (jointRoot.emitted
        (FreshPayment.visit oldVisit sourceIndex boundary).current))
      M9ProofCarryingRenewalU8Failure.entry
      (FreshPayment.authority oldVisit sourceIndex boundary) where
  compile := fun _exactEvent => output oldVisit sourceIndex boundary revision

def installedFace (revision : Revision oldVisit sourceIndex boundary) :
    SourceNativeRootInquiryCompilationFaceCoreAt
      jointRoot (FreshPayment.visit oldVisit sourceIndex boundary) ()
      (ULift.up.{1, 0} (jointRoot.emitted
        (FreshPayment.visit oldVisit sourceIndex boundary).current))
      M9ProofCarryingRenewalU8Failure.entry
      (FreshPayment.authority oldVisit sourceIndex boundary)
      (program oldVisit sourceIndex boundary revision).generate.output where
  projection := jointInquiryProjection
  active := ()
  classifier_eq := rfl
  project_heq := HEq.rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Compilation
