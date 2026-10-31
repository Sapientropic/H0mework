import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Root.SourceGeneratedContributionCapacityRepresentationPairIntentRoot

/-!
# Sequential installation of the representation pair-intent root

One fixed action program consumes current `1` of the existing augmented
revised-Q root.  It installs the already fixed pair-intent target source at
Bool current `false`; the target root's first whole-ledger write is the unique
transition to `true`, where intent, failure, and inquiry projections become
active.

The initial target ledger is exactly the claim translation of the source
ledger and is surjective: no row is fresh at ingress.  The action receipt
retains the private P→Q breaking material, the exact intent projection payload,
the semantic-change bearer, and the first generated successor.  It stores no
second root, ledger, runtime, registry, U8 result or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialContributionCapacityRepresentationPairIntent

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedLossAllocationCompiler
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentTheory
open M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot
open M14SourceGeneratedPostSettlementObserverSubmissionU8

def representationIntentOccurrencePresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructivePresentation
      ((representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
          (representationIntentActionSourceVisitAt oldVisit sourceIndex
            boundary).current)
      ((representationIntentLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toRoot.actual.OccurrenceAt false) where
  forward := fun _ =>
    representationIntentEmitted oldVisit sourceIndex boundary false
  backward := fun _ =>
    (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
      ).emitted 1
  backward_forward := by
    intro occurrence
    exact
      (lossAllocationOccurrence_eq_emitted
        (rootedFailureAt oldVisit sourceIndex boundary) occurrence).symm
  forward_backward := by
    intro occurrence
    exact (representationIntentOccurrence_eq_emitted oldVisit sourceIndex
      boundary occurrence).symm

@[simp] theorem representationIntentOccurrencePresentation_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)) :
    (representationIntentOccurrencePresentationAt oldVisit sourceIndex
      boundary).forward exactSource.occurrence =
      (representationIntentLivingRootAt oldVisit sourceIndex boundary
        ).emitted false :=
  rfl

def representationIntentFirstSuccessorAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLedgerGeneratedSuccessorAt
      (representationIntentInitialGeneratedAt oldVisit sourceIndex boundary
        ).occurrence
      (representationIntentInitialGeneratedAt oldVisit sourceIndex boundary
        ).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (representationIntentInitialGeneratedAt oldVisit sourceIndex boundary
      ).wholeLedgerWriteBack).get (by rfl)

@[simp] theorem representationIntentFirstSuccessor_targetCurrent_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentFirstSuccessorAt oldVisit sourceIndex boundary
      ).targetCurrent = true :=
  rfl

structure RepresentationIntentActionMaterialReceiptAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary))
    (material : SourceGeneratedRepresentationIntentActionMaterialAt oldVisit
      sourceIndex boundary exactSource) : Prop where
  materialExact : material =
    sourceGeneratedRepresentationIntentActionMaterialAt oldVisit sourceIndex
      boundary exactSource
  targetLawSurfaceExact :
    (representationIntentLivingRootAt oldVisit sourceIndex boundary
      ).source.base.lawSurface =
      representationPairIntentTheoryAt oldVisit sourceIndex boundary
  firstTargetCurrentExact :
    (representationIntentFirstSuccessorAt oldVisit sourceIndex boundary
      ).targetCurrent = true
  intentProjectionExact : HEq
    ((representationIntentProjectionLawAt oldVisit sourceIndex boundary
      ).project .intent
        (representationIntentEmitted oldVisit sourceIndex boundary true)
        ⟨rfl⟩)
    (sourceGeneratedRepresentationIntentPayloadAt oldVisit sourceIndex boundary)

abbrev RepresentationIntentActionReceiptCoreAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)) :
    Prop :=
  ∃ material : SourceGeneratedRepresentationIntentActionMaterialAt oldVisit
      sourceIndex boundary exactSource,
    RepresentationIntentActionMaterialReceiptAt oldVisit sourceIndex boundary
      exactSource material

theorem representationIntentActionReceiptCoreAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)) :
    RepresentationIntentActionReceiptCoreAt oldVisit sourceIndex boundary
      exactSource := by
  let material := sourceGeneratedRepresentationIntentActionMaterialAt oldVisit
    sourceIndex boundary exactSource
  exact
    ⟨material,
      ⟨rfl, rfl,
        representationIntentFirstSuccessor_targetCurrent_exact oldVisit
          sourceIndex boundary,
        HEq.rfl⟩⟩

def ExactRepresentationIntentActionReceiptAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary))
    (_answer : PUnit) : Type 3 :=
  ULift.{3, 0}
    (PLift
      (RepresentationIntentActionReceiptCoreAt oldVisit sourceIndex boundary
        exactSource))

def representationIntentActionTargetAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)) :
    SourceNativeSequentialActualActionTargetAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary)
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)
      exactSource
      (representationIntentActionSourceEntryAt oldVisit sourceIndex boundary)
      (representationIntentActionSourceAuthorityAt oldVisit sourceIndex
        boundary) where
  TargetN := RepresentationIntentNAt oldVisit sourceIndex boundary
  translation := representationClaimTranslation oldVisit sourceIndex boundary
  TargetV := RepresentationIntentVAt oldVisit sourceIndex boundary
  targetRoot := representationIntentLivingRootAt oldVisit sourceIndex boundary
  targetTheory :=
    representationPairIntentTheoryAt oldVisit sourceIndex boundary
  lawSurface_heq := HEq.rfl
  targetTheory_rootSemantic :=
    representationPairIntentTheory_rootSemantic oldVisit sourceIndex boundary
  occurrencePresentation :=
    representationIntentOccurrencePresentationAt oldVisit sourceIndex boundary
  occurrence_commutes :=
    representationIntentOccurrencePresentation_commutes oldVisit sourceIndex
      boundary exactSource
  initialSupport_heq := HEq.rfl
  initialOpenLedger :=
    (representationClaimTranslation oldVisit sourceIndex boundary
      ).oldOpenLedger
        ((representationIntentActionSourceRootAt oldVisit sourceIndex boundary
          ).toAuthoritativeRoot.toRoot.supportAt
            (representationIntentActionSourceVisitAt oldVisit sourceIndex
              boundary).current)
  initialOpenLedger_heq := HEq.rfl
  initialLedger_responsibility_commutes := fun _ => rfl
  initialLedger_claim_commutes := fun _ => rfl
  initialLedger_budget_conservative := fun _ => Nat.le_refl _
  initialLedgerNoFresh := fun targetEntry =>
    ⟨⟨⟨targetEntry.1, targetEntry.2⟩, PLift.up rfl⟩⟩
  translatedSourceEntryRow :=
    representationIntentInitialBearerRowAt oldVisit sourceIndex boundary
  firstSuccessor :=
    representationIntentFirstSuccessorAt oldVisit sourceIndex boundary
  canonical_targetNextVisit_eq := rfl
  Answer := PUnit
  answer := PUnit.unit
  Receipt := ExactRepresentationIntentActionReceiptAt oldVisit sourceIndex
    boundary exactSource
  receipt := ULift.up
    (PLift.up
      (representationIntentActionReceiptCoreAt oldVisit sourceIndex boundary
        exactSource))

def representationIntentActionProgramAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeSequentialActualActionProgramAt
      (representationIntentActionSourceRootAt oldVisit sourceIndex boundary)
      (representationIntentActionSourceVisitAt oldVisit sourceIndex boundary)
      (representationIntentActionSourceEntryAt oldVisit sourceIndex boundary)
      (representationIntentActionSourceAuthorityAt oldVisit sourceIndex
        boundary) where
  targetAt :=
    representationIntentActionTargetAt oldVisit sourceIndex boundary

def generatedRepresentationIntentActionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedSequentialActualActionAt
      (representationIntentActionProgramAt oldVisit sourceIndex boundary)
      (representationIntentActionExactSourceEventAt oldVisit sourceIndex
        boundary) :=
  (representationIntentActionProgramAt oldVisit sourceIndex boundary).generate
    (representationIntentActionExactSourceEventAt oldVisit sourceIndex boundary)

@[simp] theorem generatedRepresentationIntentAction_targetRoot_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (generatedRepresentationIntentActionAt oldVisit sourceIndex boundary
      ).target.targetRoot =
      representationIntentLivingRootAt oldVisit sourceIndex boundary :=
  rfl

@[simp] theorem generatedRepresentationIntentAction_targetTheory_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (generatedRepresentationIntentActionAt oldVisit sourceIndex boundary
      ).target.targetTheory =
      representationPairIntentTheoryAt oldVisit sourceIndex boundary :=
  rfl

@[simp] theorem generatedRepresentationIntentAction_targetVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (generatedRepresentationIntentActionAt oldVisit sourceIndex boundary
      ).target.targetVisit.current = true :=
  rfl

theorem generatedRepresentationIntentAction_receiptCore_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RepresentationIntentActionReceiptCoreAt oldVisit sourceIndex boundary
      (representationIntentActionExactSourceEventAt oldVisit sourceIndex
        boundary) :=
  (generatedRepresentationIntentActionAt oldVisit sourceIndex boundary
    ).target.receipt.down.down

theorem generatedRepresentationIntentAction_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let action := generatedRepresentationIntentActionAt oldVisit sourceIndex
      boundary
    let material := sourceGeneratedRepresentationIntentActionMaterialAt
      oldVisit sourceIndex boundary
      (representationIntentActionExactSourceEventAt oldVisit sourceIndex
        boundary)
    type_of% material.sourceOccurrenceExact ∧
      type_of% material.breakingGenerated.sameInstalledVisibleDifferentK ∧
      type_of% material.breakingGenerated.exactQOccurrenceAndEntry ∧
      type_of% material.breakingGenerated.independentConsumerOwnsAndConsumes ∧
      action.target.targetRoot =
        representationIntentLivingRootAt oldVisit sourceIndex boundary ∧
      action.target.targetTheory =
        representationPairIntentTheoryAt oldVisit sourceIndex boundary ∧
      action.target.targetVisit.current = true ∧
      HEq action.target.translatedSourceEntryRow
        (representationIntentInitialBearerRowAt oldVisit sourceIndex boundary) ∧
      action.target.firstSuccessor =
        representationIntentFirstSuccessorAt oldVisit sourceIndex boundary ∧
      RepresentationIntentActionReceiptCoreAt oldVisit sourceIndex boundary
        (representationIntentActionExactSourceEventAt oldVisit sourceIndex
          boundary) ∧
      (∀ targetEntry : OpenResponsibilityAt action.target.TargetN
          (action.target.targetRoot.toAuthoritativeRoot.toRoot.supportAt false),
        Nonempty
          (Sigma fun oldEntry : OpenResponsibilityAt
              (ActionSourceNAt oldVisit sourceIndex boundary)
              ((representationIntentActionSourceRootAt oldVisit sourceIndex
                boundary).toAuthoritativeRoot.toRoot.supportAt 1) =>
            PLift
              (action.target.initialOpenLedger.forward oldEntry =
                targetEntry))) ∧
      Nonempty
        ((RepresentationIntentNAt oldVisit sourceIndex boundary).SemanticChangeAt
          (representationIntentSupportAt oldVisit sourceIndex boundary)
          (representationResidualBearerAt oldVisit sourceIndex boundary).claim
          (generatedRepresentationClaimAt oldVisit sourceIndex boundary)) ∧
      HEq
        ((representationIntentProjectionLawAt oldVisit sourceIndex boundary
          ).project .intent
            (representationIntentEmitted oldVisit sourceIndex boundary true)
            ⟨rfl⟩)
        (sourceGeneratedRepresentationIntentPayloadAt oldVisit sourceIndex
          boundary) := by
  dsimp
  let material := sourceGeneratedRepresentationIntentActionMaterialAt oldVisit
    sourceIndex boundary
    (representationIntentActionExactSourceEventAt oldVisit sourceIndex boundary)
  exact
    ⟨material.sourceOccurrenceExact,
      material.breakingGenerated.sameInstalledVisibleDifferentK,
      material.breakingGenerated.exactQOccurrenceAndEntry,
      material.breakingGenerated.independentConsumerOwnsAndConsumes,
      rfl, rfl, rfl, HEq.rfl, rfl,
      generatedRepresentationIntentAction_receiptCore_exact oldVisit
        sourceIndex boundary,
      (generatedRepresentationIntentActionAt oldVisit sourceIndex boundary
        ).target.initialLedgerNoFresh,
      ⟨sourceGeneratedRepresentationSemanticChangeAt oldVisit sourceIndex
        boundary⟩,
      HEq.rfl⟩

end
end M14SourceGeneratedSequentialContributionCapacityRepresentationPairIntent
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityRepresentationPairIntent.representationIntentActionTargetAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityRepresentationPairIntent.generatedRepresentationIntentActionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityRepresentationPairIntent.generatedRepresentationIntentAction_receiptCore_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityRepresentationPairIntent.generatedRepresentationIntentAction_directConsumer
