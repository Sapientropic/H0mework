import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Revision.Producer.SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision

/-!
# Installed pair-intent U8 compilation

The exact active target occurrence compiles the already generated coface core
through its installed inquiry projection.  The program stores no alternative
core or completed output table: its single generated token is recomputed from
the same occurrence, bearer authority, U7 gate and rooted failure.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compilation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory
open M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision

def representationIntentRequiresU8Compilation
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryCompilationAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
      (representationIntentU7At oldVisit sourceIndex boundary)
      (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary)
      (representationPairIntentTheoryAt oldVisit sourceIndex boundary) ()
      (representationIntentFailureInquiryEvent oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
        ).target.targetAuthority :=
  .requiresU8
    (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)
    (representationIntentU7GateAt oldVisit sourceIndex boundary)
    (representationPairIntentFailureAt oldVisit sourceIndex boundary)
    (representationIntentGeneratedU8Core oldVisit sourceIndex boundary)

def representationIntentRequiresU8CompilationProgram
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryCompilationProgramAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
      (representationIntentU7At oldVisit sourceIndex boundary)
      (representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary)
      (representationPairIntentTheoryAt oldVisit sourceIndex boundary) ()
      (representationIntentFailureInquiryEvent oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
        ).target.targetAuthority where
  compile := fun _ =>
    representationIntentRequiresU8Compilation oldVisit sourceIndex boundary

def representationIntentGeneratedU8Compilation
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (representationIntentRequiresU8CompilationProgram oldVisit sourceIndex
    boundary).generate

def representationIntentU8CompilationFace
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRootInquiryCompilationFaceCoreAt
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary) ()
      (representationIntentFailureInquiryEvent oldVisit sourceIndex boundary)
      (representationResidualBearerAt oldVisit sourceIndex boundary)
      (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
        ).target.targetAuthority
      (representationIntentGeneratedU8Compilation oldVisit sourceIndex
        boundary).output where
  projection := .inherited RepresentationIntentProjection.inquiry
  active := representationIntentInquiryActiveAt oldVisit sourceIndex boundary
  classifier_eq :=
    representationIntentClassifier_inquiry_true oldVisit sourceIndex boundary
  project_heq := HEq.rfl

def representationIntentU8InquiryState
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RootInquiryStateAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      (RepresentationIntentVAt oldVisit sourceIndex boundary) where
  root := InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
  visit := InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary
  U7 := representationIntentU7At oldVisit sourceIndex boundary
  calculus :=
    representationIntentTheoryAuditCalculusAt oldVisit sourceIndex boundary
  Query := Unit
  entryAt := fun _ =>
    representationResidualBearerAt oldVisit sourceIndex boundary
  authorityAt := fun _ =>
    (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
      ).target.targetAuthority
  compilationProgramAt := fun _ =>
    representationIntentRequiresU8CompilationProgram oldVisit sourceIndex
      boundary
  compilationFaceAt := fun _ =>
    representationIntentU8CompilationFace oldVisit sourceIndex boundary
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq
    exact representationIntentFailureRootDispositionCommutesAt oldVisit
      sourceIndex boundary

def representationIntentU8EngineState
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  RootInquiryEngineStateAt.create
    (representationIntentU8InquiryState oldVisit sourceIndex boundary)

def representationIntentU8SourcePresentation
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RootInquiryStatePresentation where
  N := RepresentationIntentNAt oldVisit sourceIndex boundary
  V := RepresentationIntentVAt oldVisit sourceIndex boundary
  state := representationIntentU8EngineState oldVisit sourceIndex boundary

@[simp] theorem representationIntentGeneratedU8Compilation_output_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentGeneratedU8Compilation oldVisit sourceIndex boundary
      ).output =
      representationIntentRequiresU8Compilation oldVisit sourceIndex
        boundary :=
  rfl

theorem representationIntentInstalledU8Compilation_factorizes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let generated :=
      (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
    HEq
      ((InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.source.projectionLaw.project
          (representationIntentU8CompilationFace oldVisit sourceIndex
            boundary).projection generated.occurrence
          (representationIntentU8CompilationFace oldVisit sourceIndex
            boundary).active)
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := representationResidualBearerAt oldVisit sourceIndex boundary)
        (query := ())
        (event := representationIntentFailureInquiryEvent oldVisit sourceIndex
          boundary)
        (audit := (representationIntentRequiresU8Compilation oldVisit
          sourceIndex boundary).audit)
        (representationIntentRequiresU8Compilation oldVisit sourceIndex
          boundary).answerReadout) := by
  dsimp only
  exact (representationIntentU8CompilationFace oldVisit sourceIndex boundary
    ).project_heq

theorem representationIntentU8Compilation_output_unique
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (other : SourceGeneratedInquiryCompilationAt
      (representationIntentRequiresU8CompilationProgram oldVisit sourceIndex
        boundary)) :
    other.output =
      (representationIntentGeneratedU8Compilation oldVisit sourceIndex
        boundary).output :=
  other.output_eq _

theorem representationIntentU8Compilation_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentGeneratedU8Compilation oldVisit sourceIndex boundary
      ).output =
        .requiresU8
          (generatedRepresentationObstructionAt oldVisit sourceIndex boundary)
          (representationIntentU7GateAt oldVisit sourceIndex boundary)
          (representationPairIntentFailureAt oldVisit sourceIndex boundary)
          (representationIntentGeneratedU8Core oldVisit sourceIndex boundary) ∧
      Nonempty
        (SourceNativeRootInquiryCompilationFaceCoreAt
          (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary)
          (InstalledRepresentationIntentVisitAt oldVisit sourceIndex boundary)
          ()
          (representationIntentFailureInquiryEvent oldVisit sourceIndex
            boundary)
          (representationResidualBearerAt oldVisit sourceIndex boundary)
          (InstalledRepresentationIntentActionAt oldVisit sourceIndex boundary
            ).target.targetAuthority
          (representationIntentGeneratedU8Compilation oldVisit sourceIndex
            boundary).output) :=
  ⟨rfl, ⟨representationIntentU8CompilationFace oldVisit sourceIndex boundary⟩⟩

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compilation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compilation.representationIntentGeneratedU8Compilation_output_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compilation.representationIntentInstalledU8Compilation_factorizes
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compilation.representationIntentU8Compilation_output_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compilation.representationIntentU8Compilation_directConsumer
