import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Failure.SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Lifecycle.SourceGeneratedLossAllocationLifecycle

/-!
# Pair-intent U8 lifecycle

The canonical minimal coface retains the target root's exact three rows and
adds one generated obstruction row.  Old rows reuse the existing
loss-allocation bearer compiler; the new row uses the already registered
parent bearer.  Responsibility content plus that bearer remains injective,
including the proof-relevant child-A/child-B witnesses.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ComplementObservation Lifecycle Universal Relations Exchange
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationRestructuring
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationIntentActionMaterial
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure
open M14SourceGeneratedPostSettlementObserverSubmissionU8

abbrev RepresentationIntentRootedAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  representationIntentRootedFailureAt oldVisit sourceIndex boundary

def RepresentationIntentCofaceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    GeneratedMinimalCofaceAt
      (RepresentationIntentRootedAt oldVisit sourceIndex boundary) :=
  representationIntentGeneratedMinimalCofaceAt oldVisit sourceIndex boundary

abbrev RepresentationIntentU8NAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (RepresentationIntentCofaceAt oldVisit sourceIndex boundary).worldNetwork

abbrev RepresentationIntentU8LifecycleSourceEventAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support ×
    ExactSourceGeneratedLossAllocationMaterialWitness

def representationIntentBaseBearerAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {support : (RepresentationIntentNAt oldVisit sourceIndex boundary).Support}
    (entry : OpenResponsibilityAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary) support) :
    Lifecycle.ActorBearer :=
  lossAllocationBearerAt (rootedFailureAt oldVisit sourceIndex boundary)
    materialWitness ⟨entry.1, entry.2⟩

/-- The exact old entry key remains injective after the claim-carrier lift. -/
theorem representationIntentBaseEntryKey_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport :
      (RepresentationIntentNAt oldVisit sourceIndex boundary).Support} :
    Function.Injective
      (fun entry : OpenResponsibilityAt
          (RepresentationIntentNAt oldVisit sourceIndex boundary)
          indexedSupport =>
        (entry.1,
          representationIntentBaseBearerAt oldVisit sourceIndex boundary
            materialWitness entry)) := by
  rintro ⟨leftResponsibility, leftOpen⟩
    ⟨rightResponsibility, rightOpen⟩ key_eq
  have responsibility_eq : leftResponsibility = rightResponsibility :=
    congrArg Prod.fst key_eq
  have exactBearerEq := congrArg Prod.snd key_eq
  cases responsibility_eq
  rcases indexedSupport with ⟨worldSupport, phase⟩
  cases phase with
  | false =>
      cases worldSupport with
      | inl oldSupport =>
          cases leftResponsibility with
          | inl oldResponsibility =>
              cases oldSupport <;> cases oldResponsibility
              · cases leftOpen
                cases rightOpen
                rfl
              · cases leftOpen
                cases rightOpen
                rfl
          | inr direction => exact nomatch leftOpen
      | inr supportDirection =>
          cases leftResponsibility with
          | inl oldResponsibility =>
              cases oldResponsibility
              cases leftOpen
              cases rightOpen
              rfl
          | inr responsibilityDirection =>
              cases leftOpen
              cases rightOpen
              rfl
  | true =>
      cases worldSupport with
      | inl oldSupport =>
          cases leftResponsibility with
          | inl oldResponsibility =>
              cases oldSupport <;> cases oldResponsibility <;>
                cases leftOpen <;> cases rightOpen <;> rfl
          | inr direction => exact nomatch leftOpen
      | inr supportDirection =>
          cases leftResponsibility with
          | inl oldResponsibility =>
              cases oldResponsibility
              rcases leftOpen with ⟨leftLeg, leftAdmitted⟩
              rcases rightOpen with ⟨rightLeg, rightAdmitted⟩
              have bearer_eq :
                  sourceGeneratedLossAllocationMaterial.childBearerAt leftLeg =
                    sourceGeneratedLossAllocationMaterial.childBearerAt
                      rightLeg := by
                change
                  sourceGeneratedLossAllocationMaterial.childBearerAt leftLeg =
                    sourceGeneratedLossAllocationMaterial.childBearerAt
                      rightLeg at exactBearerEq
                exact exactBearerEq
              rcases leftAdmitted with leftAdmitted | leftAdmitted <;>
                rcases rightAdmitted with rightAdmitted | rightAdmitted
              · cases leftAdmitted
                cases rightAdmitted
                rfl
              · cases leftAdmitted
                cases rightAdmitted
                exact False.elim
                  (sourceGeneratedLossAllocationMaterial.childBearersDistinct
                    bearer_eq)
              · cases leftAdmitted
                cases rightAdmitted
                exact False.elim
                  (sourceGeneratedLossAllocationMaterial.childBearersDistinct
                    bearer_eq.symm)
              · cases leftAdmitted
                cases rightAdmitted
                rfl
          | inr responsibilityDirection =>
              cases leftOpen
              cases rightOpen
              rfl

def representationIntentU8BearerAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness) :
    {support : (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support} →
      OpenResponsibilityAt
        (RepresentationIntentU8NAt oldVisit sourceIndex boundary) support →
        Lifecycle.ActorBearer
  | .inl oldSupport, ⟨.inl oldResponsibility, isOpen⟩ =>
      representationIntentBaseBearerAt oldVisit sourceIndex boundary
        materialWitness
        (⟨oldResponsibility, isOpen⟩ : OpenResponsibilityAt
          (RepresentationIntentNAt oldVisit sourceIndex boundary) oldSupport)
  | .inl _oldSupport, ⟨.inr _direction, impossible⟩ =>
      PEmpty.elim impossible
  | .inr _supportDirection, ⟨.inl oldResponsibility, isOpen⟩ =>
      representationIntentBaseBearerAt oldVisit sourceIndex boundary
        materialWitness
        (⟨oldResponsibility, isOpen⟩ : OpenResponsibilityAt
          (RepresentationIntentNAt oldVisit sourceIndex boundary)
          (representationIntentSupportAt oldVisit sourceIndex boundary))
  | .inr _supportDirection,
      ⟨.inr _responsibilityDirection, _isOpen⟩ =>
      sourceGeneratedLossAllocationMaterial.parentBearer

def representationIntentU8LifecycleVocabulary
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ResponsibilityLifecycle.Vocabulary where
  SourceEvent :=
    RepresentationIntentU8LifecycleSourceEventAt oldVisit sourceIndex boundary
  Content := (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Responsibility
  Residual := Nat
  Bearer := Lifecycle.ActorBearer
  ProtectedInterest :=
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Claim
  Scope := PUnit
  Lineage := (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Lineage
  Incidence :=
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Incidence
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun sourceEvent =>
    MinimalRegistrableSourceAnchor.canonical PUnit.unit
      ((RepresentationIntentU8NAt oldVisit sourceIndex boundary).lineageAt
        sourceEvent.1)
  sourceIncidence := fun sourceEvent =>
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).incidenceAt
      sourceEvent.1
  ObstructionAt := fun _ => PEmpty
  demandContent := fun {_} obstruction => nomatch obstruction
  demandResidual := fun {_} obstruction => nomatch obstruction
  CommitmentAt := fun sourceEvent responsibility =>
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).OpenAt
      sourceEvent.1 responsibility
  MandateOriginAt := fun _ _ => PEmpty
  AcceptedTaskAt := fun _ _ => PEmpty
  ActiveDependencyAt := fun _ _ => PEmpty
  ProtectedRiskAt := fun _ _ => PEmpty
  AdmissionAuthorityAt := fun _ _ => PUnit
  AcceptedAt := fun _ _ _ => PUnit
  StandingMandateAt := fun _ _ _ => PEmpty
  DischargeJurisdiction := fun _ _ => PUnit
  ProgressAt := fun _ _ _ _ => PEmpty
  MaintenanceAt := fun _ _ _ => PEmpty
  TypedDeferAt := fun _ _ _ => PEmpty
  ScopeNarrowingAt := fun _ _ _ => PEmpty
  TransferAcceptedAt := fun _ _ _ _ => PEmpty
  FulfilledAt := fun _ _ _ => PEmpty
  WaivedAt := fun _ _ _ => PEmpty
  InvalidatedAt := fun _ _ _ => PEmpty
  AbandonedAt := fun _ _ _ => PEmpty
  ImpossibleResidueAcceptedAt := fun _ _ _ => PEmpty
  SupersessionAt := fun _ _ _ _ _ _ _ => PEmpty
  ReopenAt := fun _ _ _ _ _ _ _ => PEmpty
  JurisdictionEndedAt := fun _ _ _ => PEmpty
  ConsentRevokedAt := fun _ _ _ => PEmpty
  CapacityReleasedAt := fun _ _ _ => PEmpty
  UpperRouteAt := fun _ _ _ => PEmpty
  NextActorSignal := PEmpty
  AgeSignal := PEmpty
  TransferOfferSignal := PEmpty

abbrev RepresentationIntentU8LifecycleV
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  representationIntentU8LifecycleVocabulary oldVisit sourceIndex boundary

def representationIntentU8AdmissionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {support : (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support}
    (entry : OpenResponsibilityAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary) support) :
    NativeAdmissionPayload
      (RepresentationIntentU8LifecycleV oldVisit sourceIndex boundary) where
  sourceEvent := (support, materialWitness)
  content := entry.1
  residual := entry.progressBudget
  bearer := representationIntentU8BearerAt oldVisit sourceIndex boundary
    materialWitness entry
  beneficiary := entry.claim
  scope := PUnit.unit
  lineage :=
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).lineageAt support
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment entry.2
  authority := PUnit.unit
  assumption := .accepted PUnit.unit
  dischargeJurisdiction := PUnit.unit

def representationIntentU8ObligationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {support : (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support}
    (entry : OpenResponsibilityAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary) support) :
    AdmittedObligation
      (RepresentationIntentU8LifecycleV oldVisit sourceIndex boundary) :=
  (representationIntentU8AdmissionAt oldVisit sourceIndex boundary
    materialWitness entry).toObligation

theorem representationIntentU8EntryKey_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {support : (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support} :
    Function.Injective
      (fun entry : OpenResponsibilityAt
          (RepresentationIntentU8NAt oldVisit sourceIndex boundary) support =>
        (entry.1,
          representationIntentU8BearerAt oldVisit sourceIndex boundary
            materialWitness entry)) := by
  rintro ⟨leftResponsibility, leftOpen⟩
    ⟨rightResponsibility, rightOpen⟩ key_eq
  have responsibility_eq : leftResponsibility = rightResponsibility :=
    congrArg Prod.fst key_eq
  have bearer_eq := congrArg Prod.snd key_eq
  cases responsibility_eq
  cases support with
  | inl oldSupport =>
      cases leftResponsibility with
      | inl oldResponsibility =>
          let leftEntry : OpenResponsibilityAt
              (RepresentationIntentNAt oldVisit sourceIndex boundary)
              oldSupport := ⟨oldResponsibility, leftOpen⟩
          let rightEntry : OpenResponsibilityAt
              (RepresentationIntentNAt oldVisit sourceIndex boundary)
              oldSupport := ⟨oldResponsibility, rightOpen⟩
          have oldKeyEq :
              (leftEntry.1,
                representationIntentBaseBearerAt oldVisit sourceIndex boundary
                  materialWitness leftEntry) =
              (rightEntry.1,
                representationIntentBaseBearerAt oldVisit sourceIndex boundary
                  materialWitness rightEntry) :=
            Prod.ext rfl bearer_eq
          have entry_eq := representationIntentBaseEntryKey_injective oldVisit
            sourceIndex boundary materialWitness oldKeyEq
          have open_eq : leftOpen = rightOpen :=
            HEq.eq (Sigma.mk.inj_iff.mp entry_eq).2
          cases open_eq
          rfl
      | inr direction => exact nomatch leftOpen
  | inr supportDirection =>
      cases supportDirection
      cases leftResponsibility with
      | inl oldResponsibility =>
          let leftEntry : OpenResponsibilityAt
              (RepresentationIntentNAt oldVisit sourceIndex boundary)
              (representationIntentSupportAt oldVisit sourceIndex boundary) :=
            ⟨oldResponsibility, leftOpen⟩
          let rightEntry : OpenResponsibilityAt
              (RepresentationIntentNAt oldVisit sourceIndex boundary)
              (representationIntentSupportAt oldVisit sourceIndex boundary) :=
            ⟨oldResponsibility, rightOpen⟩
          have oldKeyEq :
              (leftEntry.1,
                representationIntentBaseBearerAt oldVisit sourceIndex boundary
                  materialWitness leftEntry) =
              (rightEntry.1,
                representationIntentBaseBearerAt oldVisit sourceIndex boundary
                  materialWitness rightEntry) :=
            Prod.ext rfl bearer_eq
          have entry_eq := representationIntentBaseEntryKey_injective oldVisit
            sourceIndex boundary materialWitness oldKeyEq
          have open_eq : leftOpen = rightOpen :=
            HEq.eq (Sigma.mk.inj_iff.mp entry_eq).2
          cases open_eq
          rfl
      | inr responsibilityDirection =>
          cases responsibilityDirection
          cases leftOpen
          cases rightOpen
          rfl

theorem representationIntentU8ObligationAt_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {support : (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support} :
    Function.Injective
      (representationIntentU8ObligationAt oldVisit sourceIndex boundary
        materialWitness (support := support)) := by
  intro left right obligation_eq
  apply representationIntentU8EntryKey_injective oldVisit sourceIndex boundary
    materialWitness
  apply Prod.ext
  · exact congrArg AdmittedObligation.content obligation_eq
  · exact congrArg AdmittedObligation.bearer obligation_eq

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle.representationIntentBaseEntryKey_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle.representationIntentU8ObligationAt_injective
