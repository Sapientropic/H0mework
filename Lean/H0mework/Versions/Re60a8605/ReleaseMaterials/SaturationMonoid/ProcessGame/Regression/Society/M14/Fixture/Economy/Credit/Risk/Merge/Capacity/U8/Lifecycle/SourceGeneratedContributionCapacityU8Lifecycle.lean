import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Failure.SourceGeneratedContributionCapacityFailure

/-!
# Source-generated contribution-capacity U8 lifecycle

The obstruction-generated minimal coface retains every capacity-target row
and adds exactly one addressable residual row.  Inherited rows keep their
existing bearers; the generated residual is borne by the same already
registered parent bearer as the obstruction-continuity row.  Responsibility
content, not a new actor or identity registry, distinguishes the two rows.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityU8Lifecycle

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open ComplementObservation Lifecycle Universal Relations Exchange
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutLifecycle
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityFailure

abbrev CapacityRootedAt (oldVisit : OldVisit) :=
  capacityRootedFailureAt oldVisit

def CapacityCofaceAt (oldVisit : OldVisit) :
    GeneratedMinimalCofaceAt (CapacityRootedAt oldVisit) :=
  capacityGeneratedMinimalCofaceAt oldVisit

abbrev CapacityU8NAt (oldVisit : OldVisit) :=
  (CapacityCofaceAt oldVisit).worldNetwork

abbrev CapacityU8LifecycleSourceEventAt (oldVisit : OldVisit) :=
  (CapacityU8NAt oldVisit).Support ×
    ExactSourceGeneratedLossAllocationMaterialWitness

def contributionCapacityU8BearerAt
    (oldVisit : OldVisit)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness) :
    {indexedSupport : (CapacityU8NAt oldVisit).Support} →
      OpenResponsibilityAt (CapacityU8NAt oldVisit) indexedSupport →
        Lifecycle.ActorBearer
  | .inl oldSupport, ⟨.inl oldResponsibility, isOpen⟩ =>
      contributionCapacityCutBearerAt (capacityActionRootedAt oldVisit)
        materialWitness
        (⟨oldResponsibility, isOpen⟩ : OpenResponsibilityAt
          (CutN (capacityActionRootedAt oldVisit)) oldSupport)
  | .inl _oldSupport, ⟨.inr _direction, impossible⟩ =>
      PEmpty.elim impossible
  | .inr _supportDirection, ⟨.inl oldResponsibility, isOpen⟩ =>
      contributionCapacityCutBearerAt (capacityActionRootedAt oldVisit)
        materialWitness
        (⟨oldResponsibility, isOpen⟩ : OpenResponsibilityAt
          (CutN (capacityActionRootedAt oldVisit))
          (contributionCapacityCutTargetSupport
            (capacityActionRootedAt oldVisit)))
  | .inr _supportDirection, ⟨.inr _responsibilityDirection, _isOpen⟩ =>
      sourceGeneratedLossAllocationMaterial.parentBearer

def contributionCapacityU8LifecycleVocabulary
    (oldVisit : OldVisit) : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := CapacityU8LifecycleSourceEventAt oldVisit
  Content := (CapacityU8NAt oldVisit).Responsibility
  Residual := Nat
  Bearer := Lifecycle.ActorBearer
  ProtectedInterest := (CapacityU8NAt oldVisit).Claim
  Scope := PUnit
  Lineage := (CapacityU8NAt oldVisit).Lineage
  Incidence := (CapacityU8NAt oldVisit).Incidence
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun sourceEvent =>
    MinimalRegistrableSourceAnchor.canonical PUnit.unit
      ((CapacityU8NAt oldVisit).lineageAt sourceEvent.1)
  sourceIncidence := fun sourceEvent =>
    (CapacityU8NAt oldVisit).incidenceAt sourceEvent.1
  ObstructionAt := fun _ => PEmpty
  demandContent := fun {_} obstruction => nomatch obstruction
  demandResidual := fun {_} obstruction => nomatch obstruction
  CommitmentAt := fun sourceEvent responsibility =>
    (CapacityU8NAt oldVisit).OpenAt sourceEvent.1 responsibility
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

abbrev ContributionCapacityU8LifecycleV (oldVisit : OldVisit) :=
  contributionCapacityU8LifecycleVocabulary oldVisit

def contributionCapacityU8AdmissionAt
    (oldVisit : OldVisit)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CapacityU8NAt oldVisit).Support}
    (entry : OpenResponsibilityAt (CapacityU8NAt oldVisit) indexedSupport) :
    NativeAdmissionPayload (ContributionCapacityU8LifecycleV oldVisit) where
  sourceEvent := (indexedSupport, materialWitness)
  content := entry.1
  residual := entry.progressBudget
  bearer := contributionCapacityU8BearerAt oldVisit materialWitness entry
  beneficiary := entry.claim
  scope := PUnit.unit
  lineage := (CapacityU8NAt oldVisit).lineageAt indexedSupport
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment entry.2
  authority := PUnit.unit
  assumption := .accepted PUnit.unit
  dischargeJurisdiction := PUnit.unit

def contributionCapacityU8ObligationAt
    (oldVisit : OldVisit)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CapacityU8NAt oldVisit).Support}
    (entry : OpenResponsibilityAt (CapacityU8NAt oldVisit) indexedSupport) :
    AdmittedObligation (ContributionCapacityU8LifecycleV oldVisit) :=
  (contributionCapacityU8AdmissionAt oldVisit materialWitness entry).toObligation

@[simp] theorem contributionCapacityU8Obligation_content
    (oldVisit : OldVisit)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CapacityU8NAt oldVisit).Support}
    (entry : OpenResponsibilityAt (CapacityU8NAt oldVisit) indexedSupport) :
    (contributionCapacityU8ObligationAt oldVisit materialWitness entry).content =
      entry.1 :=
  rfl

@[simp] theorem contributionCapacityU8Obligation_budget
    (oldVisit : OldVisit)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CapacityU8NAt oldVisit).Support}
    (entry : OpenResponsibilityAt (CapacityU8NAt oldVisit) indexedSupport) :
    (contributionCapacityU8ObligationAt oldVisit materialWitness entry).residual =
      entry.progressBudget :=
  rfl

theorem contributionCapacityU8EntryKey_injective
    (oldVisit : OldVisit)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CapacityU8NAt oldVisit).Support} :
    Function.Injective
      (fun entry : OpenResponsibilityAt
          (CapacityU8NAt oldVisit) indexedSupport =>
        (entry.1,
          contributionCapacityU8BearerAt oldVisit materialWitness entry)) := by
  rintro ⟨leftResponsibility, leftOpen⟩
    ⟨rightResponsibility, rightOpen⟩ key_eq
  have responsibility_eq : leftResponsibility = rightResponsibility :=
    congrArg Prod.fst key_eq
  have bearer_eq := congrArg Prod.snd key_eq
  cases responsibility_eq
  cases indexedSupport with
  | inl oldSupport =>
      cases leftResponsibility with
      | inl oldResponsibility =>
          let leftEntry : OpenResponsibilityAt
              (CutN (capacityActionRootedAt oldVisit)) oldSupport :=
            ⟨oldResponsibility, leftOpen⟩
          let rightEntry : OpenResponsibilityAt
              (CutN (capacityActionRootedAt oldVisit)) oldSupport :=
            ⟨oldResponsibility, rightOpen⟩
          have oldKeyEq :
              (leftEntry.1,
                contributionCapacityCutBearerAt
                  (capacityActionRootedAt oldVisit) materialWitness leftEntry) =
              (rightEntry.1,
                contributionCapacityCutBearerAt
                  (capacityActionRootedAt oldVisit) materialWitness rightEntry) :=
            Prod.ext rfl bearer_eq
          have entry_eq :=
            contributionCapacityCutEntryKey_injective
              (capacityActionRootedAt oldVisit) materialWitness oldKeyEq
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
              (CutN (capacityActionRootedAt oldVisit))
              (contributionCapacityCutTargetSupport
                (capacityActionRootedAt oldVisit)) :=
            ⟨oldResponsibility, leftOpen⟩
          let rightEntry : OpenResponsibilityAt
              (CutN (capacityActionRootedAt oldVisit))
              (contributionCapacityCutTargetSupport
                (capacityActionRootedAt oldVisit)) :=
            ⟨oldResponsibility, rightOpen⟩
          have oldKeyEq :
              (leftEntry.1,
                contributionCapacityCutBearerAt
                  (capacityActionRootedAt oldVisit) materialWitness leftEntry) =
              (rightEntry.1,
                contributionCapacityCutBearerAt
                  (capacityActionRootedAt oldVisit) materialWitness rightEntry) :=
            Prod.ext rfl bearer_eq
          have entry_eq :=
            contributionCapacityCutEntryKey_injective
              (capacityActionRootedAt oldVisit) materialWitness oldKeyEq
          have open_eq : leftOpen = rightOpen :=
            HEq.eq (Sigma.mk.inj_iff.mp entry_eq).2
          cases open_eq
          rfl
      | inr responsibilityDirection =>
          cases responsibilityDirection
          cases leftOpen
          cases rightOpen
          rfl

theorem contributionCapacityU8ObligationAt_injective
    (oldVisit : OldVisit)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CapacityU8NAt oldVisit).Support} :
    Function.Injective
      (contributionCapacityU8ObligationAt oldVisit materialWitness
        (indexedSupport := indexedSupport)) := by
  intro left right obligation_eq
  apply contributionCapacityU8EntryKey_injective oldVisit materialWitness
  apply Prod.ext
  · exact congrArg AdmittedObligation.content obligation_eq
  · exact congrArg AdmittedObligation.bearer obligation_eq

@[simp] theorem contributionCapacityU8_generatedBearer_is_existingParent
    (oldVisit : OldVisit) :
    contributionCapacityU8BearerAt oldVisit
        exactSourceGeneratedLossAllocationMaterialWitness
        (CapacityCofaceAt oldVisit).obstructionEntry =
      sourceGeneratedLossAllocationMaterial.parentBearer :=
  rfl

end
end M14SourceGeneratedContributionCapacityU8Lifecycle
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Lifecycle.contributionCapacityU8ObligationAt_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Lifecycle.contributionCapacityU8_generatedBearer_is_existingParent
