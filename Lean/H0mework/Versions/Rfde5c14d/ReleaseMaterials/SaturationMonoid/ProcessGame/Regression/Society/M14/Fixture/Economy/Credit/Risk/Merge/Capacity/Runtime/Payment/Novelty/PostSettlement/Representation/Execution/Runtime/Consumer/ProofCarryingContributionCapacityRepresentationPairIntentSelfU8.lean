import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Execution.Runtime.Producer.SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Theory.Revision.SourceGeneratedReflexiveSelfU8

/-!
# Proof-carrying pair-intent reflexive self-U8

The target root's pre-emitter proof-carrying renewal coordinate and the unique
pair-intent runtime meet at the same active occurrence.  Proof-carrying
legislation therefore consumes the runtime-selected revolutionary branch and
generates the reflexive self-U8 seal.  No failure, coface, core, first write or
next is accepted independently at this mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityRepresentationPairIntentSelfU8

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8Lifecycle
open ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery
open Renewal Legislation Theory.Revision
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Revision
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8TargetState
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Runtime

theorem representationIntentU8RuntimeSplice
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceInstalledRenewalRuntimeSpliceAt
      (representationIntentInstalledProofCarryingRenewalAt oldVisit sourceIndex
        boundary)
      (representationIntentU8Runtime oldVisit sourceIndex boundary) 0 where
  sameRoot := HEq.rfl
  sameVisit := HEq.rfl
  sameRow := HEq.rfl
  sameOccurrence := HEq.rfl

def representationIntentProofCarryingLegislation
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ProofCarryingLegislationAt
      (representationIntentInstalledProofCarryingRenewalAt oldVisit sourceIndex
        boundary)
      (representationIntentU8Runtime oldVisit sourceIndex boundary) 0
      (representationIntentU8RuntimeSplice oldVisit sourceIndex boundary) :=
  sourceGeneratedProofCarryingLegislation
    (representationIntentInstalledProofCarryingRenewalAt oldVisit sourceIndex
      boundary)
    (representationIntentU8Runtime oldVisit sourceIndex boundary) 0
    (representationIntentU8RuntimeSplice oldVisit sourceIndex boundary)

def representationIntentExactRevolutionaryConsumption
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (representationIntentProofCarryingLegislation oldVisit sourceIndex boundary
    ).revolutionaryConsumption?.get (by rfl)

def representationIntentExactRevolution
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (representationIntentExactRevolutionaryConsumption oldVisit sourceIndex
    boundary).1

def representationIntentExactConsumption
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (representationIntentExactRevolutionaryConsumption oldVisit sourceIndex
    boundary).2

def representationIntentReflexiveSelfU8
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedReflexiveSelfU8At
      (representationIntentProofCarryingLegislation oldVisit sourceIndex
        boundary)
      (representationIntentExactRevolution oldVisit sourceIndex boundary)
      (representationIntentExactConsumption oldVisit sourceIndex boundary) :=
  SourceGeneratedReflexiveSelfU8At.generate
    (representationIntentExactConsumption oldVisit sourceIndex boundary)

@[simp] theorem representationIntentExactRevolution_core_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentExactRevolution oldVisit sourceIndex boundary).core =
      representationIntentGeneratedU8Core oldVisit sourceIndex boundary :=
  rfl

@[simp] theorem representationIntentReflexiveSelfU8_failure_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
      ).failure =
      representationPairIntentFailureAt oldVisit sourceIndex boundary :=
  rfl

@[simp] theorem representationIntentReflexiveSelfU8_rooted_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
      ).rooted =
      representationIntentRootedFailureAt oldVisit sourceIndex boundary :=
  rfl

@[simp] theorem representationIntentReflexiveSelfU8_coface_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
      ).minimalCoface =
      RepresentationIntentCofaceAt oldVisit sourceIndex boundary :=
  rfl

theorem representationIntentReflexiveSelfU8_runtimeConsumesExactCore
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      (representationIntentGeneratedU8Core oldVisit sourceIndex boundary)
      (representationIntentU8Runtime oldVisit sourceIndex boundary) 0 :=
  (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
    ).runtime_consumes_core

@[simp] theorem representationIntentReflexiveSelfU8_firstWrite_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
      ).firstWrite =
      (representationIntentGeneratedU8Core oldVisit sourceIndex boundary
        ).cofaceFactorization.2.firstWrite :=
  rfl

theorem representationIntentReflexiveSelfU8_firstWriteConsumes_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
        ).firstWriteConsumes
      (representationIntentGeneratedU8Core oldVisit sourceIndex boundary
        ).cofaceFactorization.2.firstWriteConsumes :=
  HEq.rfl

theorem representationIntentReflexiveSelfU8_rowsShareGeneratedNext
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
      ).oldRowAnswerAndNext.nextCurrent =
      (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
        ).newRowAnswerAndNext.nextCurrent :=
  (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
    ).revised_rows_share_generatedNext

theorem representationIntentReflexiveSelfU8_sameRoot
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (sourceGeneratedRuntimeInquiryCoordinateAt
        (representationIntentU8Runtime oldVisit sourceIndex boundary) 0
        ).1.state.base.root
      (representationIntentLivingRootAt oldVisit sourceIndex boundary) :=
  (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary).sameRoot

theorem representationIntentReflexiveSelfU8_sameVisit
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      (sourceGeneratedRuntimeInquiryCoordinateAt
        (representationIntentU8Runtime oldVisit sourceIndex boundary) 0
        ).1.state.base.visit
      (representationIntentActiveVisitAt oldVisit sourceIndex boundary) :=
  (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary).sameVisit

theorem representationIntentReflexiveSelfU8_sameRow
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      ((sourceGeneratedRuntimeInquiryCoordinateAt
        (representationIntentU8Runtime oldVisit sourceIndex boundary) 0
        ).1.state.base.entryAt
          (sourceGeneratedRuntimeInquiryCoordinateAt
            (representationIntentU8Runtime oldVisit sourceIndex boundary) 0).2)
      (representationIntentInstalledProofCarryingRenewalAt oldVisit sourceIndex
        boundary).payload.sourceEntry :=
  (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary).sameRow

theorem representationIntentReflexiveSelfU8_sameOccurrence
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    HEq
      ((sourceGeneratedRuntimeInquiryCoordinateAt
        (representationIntentU8Runtime oldVisit sourceIndex boundary) 0
        ).1.state.base.root.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt
            (sourceGeneratedRuntimeInquiryCoordinateAt
              (representationIntentU8Runtime oldVisit sourceIndex boundary) 0
              ).1.state.base.visit)
      ((representationIntentLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (representationIntentActiveVisitAt oldVisit sourceIndex boundary)) :=
  (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
    ).sameOccurrence

theorem representationIntentReflexiveSelfU8_rootFactorization
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentInstalledProofCarryingRenewalAt oldVisit sourceIndex
      boundary).RootAnswerAndNextFactorizes :=
  (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
    ).rootAnswerAndNext_factorizes

theorem representationIntentReflexiveSelfU8_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentExactRevolution oldVisit sourceIndex boundary).core =
        representationIntentGeneratedU8Core oldVisit sourceIndex boundary ∧
      (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
        ).rooted =
        representationIntentRootedFailureAt oldVisit sourceIndex boundary ∧
      (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
        ).minimalCoface =
        RepresentationIntentCofaceAt oldVisit sourceIndex boundary ∧
      (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
        ).oldRowAnswerAndNext.nextCurrent =
        (representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary
          ).newRowAnswerAndNext.nextCurrent ∧
      Nonempty
        (SourceGeneratedReflexiveSelfU8At
          (representationIntentProofCarryingLegislation oldVisit sourceIndex
            boundary)
          (representationIntentExactRevolution oldVisit sourceIndex boundary)
          (representationIntentExactConsumption oldVisit sourceIndex boundary)) :=
  ⟨rfl, rfl, rfl,
    representationIntentReflexiveSelfU8_rowsShareGeneratedNext oldVisit
      sourceIndex boundary,
    ⟨representationIntentReflexiveSelfU8 oldVisit sourceIndex boundary⟩⟩

end
end M14ProofCarryingContributionCapacityRepresentationPairIntentSelfU8
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityRepresentationPairIntentSelfU8.representationIntentU8RuntimeSplice
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityRepresentationPairIntentSelfU8.representationIntentReflexiveSelfU8
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityRepresentationPairIntentSelfU8.representationIntentReflexiveSelfU8_sameOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityRepresentationPairIntentSelfU8.representationIntentReflexiveSelfU8_rowsShareGeneratedNext
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityRepresentationPairIntentSelfU8.representationIntentReflexiveSelfU8_directConsumer
