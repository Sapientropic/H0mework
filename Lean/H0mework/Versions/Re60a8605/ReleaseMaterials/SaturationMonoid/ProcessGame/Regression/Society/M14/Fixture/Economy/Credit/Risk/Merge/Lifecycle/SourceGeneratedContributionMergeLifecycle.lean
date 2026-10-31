import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.SourceGeneratedContributionMergeWorld
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Lifecycle.SourceGeneratedLossAllocationLifecycle

/-!
# M14 source-generated contribution-merge lifecycle

The conservative contribution-merge world is presented to the existing
responsibility lifecycle.  Its source event is exactly the target support
together with the existing loss-allocation material witness.  Phase-false
rows retain their old bearer pointwise.  At phase true, the merged
contribution reads the existing `Leg.a` bearer and the obstruction continuity
reads the existing parent bearer.

This layer creates no bearer, participant, share or pool registry, and no
merge receipt, compiler, root, occurrence or runtime.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionMergeLifecycle

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open ComplementObservation Lifecycle Universal Relations Exchange
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationRestructuring
open M14SourceGeneratedContributionMergeWorld

variable
    {OldV : ConstructiveRoot.Vocabulary}
    {oldWorld : SourceNativeAuthoritativeRootClosure
      M14SourceGeneratedLossAllocationWorld.OldN OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus M14SourceGeneratedLossAllocationWorld.OldN}
    {oldTheory : TheoryState M14SourceGeneratedLossAllocationWorld.OldN}
    {support : M14SourceGeneratedLossAllocationWorld.OldN.Support}
    {obstruction :
      M14SourceGeneratedLossAllocationWorld.OldN.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

local notation "RootedFailure" => RootedActualExpressibilityFailureAt
  oldWorld oldVisit U7 failure

/-- No second source event: the exact merge-world support is paired with the
already existing zero-choice loss-allocation material witness. -/
abbrev ContributionMergeLifecycleSourceEvent (rooted : RootedFailure) :=
  (TargetN rooted).Support ×
    ExactSourceGeneratedLossAllocationMaterialWitness

/-- Generic phase-false row adapter. -/
def contributionMergePhaseFalseEntry
    (rooted : RootedFailure)
    {oldSupport : (OldN rooted).Support}
    (entry : OpenResponsibilityAt (OldN rooted) oldSupport) :
    OpenResponsibilityAt (TargetN rooted) (oldSupport, false) :=
  ⟨entry.1, entry.2⟩

/-- Bearers are restrictions of the existing loss-allocation bearer readout.
The target face adds no bearer constructor. -/
def contributionMergeBearerAt
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support}
    (entry : OpenResponsibilityAt (TargetN rooted) indexedSupport) :
    Lifecycle.ActorBearer := by
  rcases indexedSupport with ⟨⟨worldSupport, lossPhase⟩, mergePhase⟩
  rcases entry with ⟨responsibility, isOpen⟩
  cases mergePhase with
  | false =>
      exact lossAllocationBearerAt rooted materialWitness
        (⟨responsibility, isOpen⟩ :
          OpenResponsibilityAt (OldN rooted) (worldSupport, lossPhase))
  | true =>
      cases worldSupport with
      | inl oldSupport =>
          exact lossAllocationBearerAt rooted materialWitness
            (⟨responsibility, isOpen⟩ :
              OpenResponsibilityAt (OldN rooted)
                (.inl oldSupport, lossPhase))
      | inr direction =>
          cases lossPhase with
          | false =>
              exact lossAllocationBearerAt rooted materialWitness
                (⟨responsibility, isOpen⟩ :
                  OpenResponsibilityAt (OldN rooted)
                    (.inr direction, false))
          | true =>
              rcases isOpen with merged | obstruction
              · exact lossAllocationBearerAt rooted materialWitness
                  (lossAllocationTargetChildA rooted)
              · exact lossAllocationBearerAt rooted materialWitness
                  (lossAllocationTargetObstruction rooted)

@[simp] theorem contributionMergeBearerAt_phaseFalse
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {oldSupport : (OldN rooted).Support}
    (entry : OpenResponsibilityAt (OldN rooted) oldSupport) :
    contributionMergeBearerAt rooted materialWitness
        (contributionMergePhaseFalseEntry rooted entry) =
      lossAllocationBearerAt rooted materialWitness entry :=
  rfl

@[simp] theorem mergedContribution_bearer_is_existing_legA
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness) :
    contributionMergeBearerAt rooted materialWitness
        (mergedContributionEntry rooted) =
      sourceGeneratedLossAllocationMaterial.childBearerAt .a :=
  rfl

@[simp] theorem mergedObstruction_bearer_is_existing_parent
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness) :
    contributionMergeBearerAt rooted materialWitness
        (mergedObstructionEntry rooted) =
      sourceGeneratedLossAllocationMaterial.parentBearer :=
  rfl

/-! ## Exact lifecycle vocabulary and admission -/

def contributionMergeLifecycleVocabulary (rooted : RootedFailure) :
    ResponsibilityLifecycle.Vocabulary where
  SourceEvent := ContributionMergeLifecycleSourceEvent rooted
  Content := (TargetN rooted).Responsibility
  Residual := Nat
  Bearer := Lifecycle.ActorBearer
  ProtectedInterest := (TargetN rooted).Claim
  Scope := PUnit
  Lineage := (TargetN rooted).Lineage
  Incidence := (TargetN rooted).Incidence
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun sourceEvent =>
    MinimalRegistrableSourceAnchor.canonical PUnit.unit
      ((TargetN rooted).lineageAt sourceEvent.1)
  sourceIncidence := fun sourceEvent =>
    (TargetN rooted).incidenceAt sourceEvent.1
  ObstructionAt := fun _ => PEmpty
  demandContent := fun {_} obstruction => nomatch obstruction
  demandResidual := fun {_} obstruction => nomatch obstruction
  CommitmentAt := fun sourceEvent responsibility =>
    (TargetN rooted).OpenAt sourceEvent.1 responsibility
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

abbrev ContributionMergeLifecycleV (rooted : RootedFailure) :=
  contributionMergeLifecycleVocabulary rooted

def contributionMergeAdmissionAt
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support}
    (entry : OpenResponsibilityAt (TargetN rooted) indexedSupport) :
    NativeAdmissionPayload (ContributionMergeLifecycleV rooted) where
  sourceEvent := (indexedSupport, materialWitness)
  content := entry.1
  residual := entry.progressBudget
  bearer := contributionMergeBearerAt rooted materialWitness entry
  beneficiary := entry.claim
  scope := PUnit.unit
  lineage := (TargetN rooted).lineageAt indexedSupport
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment entry.2
  authority := PUnit.unit
  assumption := .accepted PUnit.unit
  dischargeJurisdiction := PUnit.unit

def contributionMergeObligationAt
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support}
    (entry : OpenResponsibilityAt (TargetN rooted) indexedSupport) :
    AdmittedObligation (ContributionMergeLifecycleV rooted) :=
  (contributionMergeAdmissionAt rooted materialWitness entry).toObligation

@[simp] theorem contributionMergeObligation_sourceEvent
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support}
    (entry : OpenResponsibilityAt (TargetN rooted) indexedSupport) :
    (contributionMergeObligationAt rooted materialWitness entry).admission.sourceEvent =
      (indexedSupport, materialWitness) :=
  rfl

@[simp] theorem contributionMergeObligation_content
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support}
    (entry : OpenResponsibilityAt (TargetN rooted) indexedSupport) :
    (contributionMergeObligationAt rooted materialWitness entry).content =
      entry.1 :=
  rfl

@[simp] theorem contributionMergeObligation_claim
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support}
    (entry : OpenResponsibilityAt (TargetN rooted) indexedSupport) :
    (contributionMergeObligationAt rooted materialWitness entry).beneficiary =
      entry.claim :=
  rfl

@[simp] theorem contributionMergeObligation_lineage
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support}
    (entry : OpenResponsibilityAt (TargetN rooted) indexedSupport) :
    (contributionMergeObligationAt rooted materialWitness entry).admission.lineage =
      (TargetN rooted).lineageAt indexedSupport :=
  rfl

@[simp] theorem contributionMergeObligation_budget
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support}
    (entry : OpenResponsibilityAt (TargetN rooted) indexedSupport) :
    (contributionMergeObligationAt rooted materialWitness entry).residual =
      entry.progressBudget :=
  rfl

@[simp] theorem contributionMergeObligation_bearer
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support}
    (entry : OpenResponsibilityAt (TargetN rooted) indexedSupport) :
    (contributionMergeObligationAt rooted materialWitness entry).bearer =
      contributionMergeBearerAt rooted materialWitness entry :=
  rfl

/-! ## Injective entry presentation -/

theorem contributionMergeObligationAt_injective
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (TargetN rooted).Support} :
    Function.Injective
      (contributionMergeObligationAt rooted materialWitness
        (indexedSupport := indexedSupport)) := by
  rintro ⟨leftResponsibility, leftOpen⟩
    ⟨rightResponsibility, rightOpen⟩ obligation_eq
  have responsibility_eq : leftResponsibility = rightResponsibility :=
    congrArg AdmittedObligation.content obligation_eq
  cases responsibility_eq
  rcases indexedSupport with ⟨oldSupport, mergePhase⟩
  cases mergePhase with
  | false =>
      rcases oldSupport with ⟨worldSupport, lossPhase⟩
      cases lossPhase with
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
                      sourceGeneratedLossAllocationMaterial.childBearerAt
                          leftLeg =
                        sourceGeneratedLossAllocationMaterial.childBearerAt
                          rightLeg := by
                    have exactBearerEq :=
                      congrArg AdmittedObligation.bearer obligation_eq
                    change
                      sourceGeneratedLossAllocationMaterial.childBearerAt
                          leftLeg =
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
  | true =>
      rcases oldSupport with ⟨worldSupport, lossPhase⟩
      cases worldSupport with
      | inl oldSupport =>
          cases lossPhase with
          | false =>
              cases leftResponsibility with
              | inl oldResponsibility =>
                  cases oldSupport <;> cases oldResponsibility <;>
                    cases leftOpen <;> cases rightOpen <;> rfl
              | inr direction => exact nomatch leftOpen
          | true =>
              cases leftResponsibility with
              | inl oldResponsibility =>
                  cases oldSupport <;> cases oldResponsibility <;>
                    cases leftOpen <;> cases rightOpen <;> rfl
              | inr direction => exact nomatch leftOpen
      | inr supportDirection =>
          cases lossPhase with
          | false =>
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
              cases supportDirection
              rcases leftOpen with leftMerged | leftObstruction <;>
                rcases rightOpen with rightMerged | rightObstruction
              · have lifted_eq : leftMerged = rightMerged := by
                  rcases leftMerged with ⟨leftProof⟩
                  rcases rightMerged with ⟨rightProof⟩
                  congr
                cases lifted_eq
                rfl
              · have impossible : contributionResponsibility rooted =
                    contributionObstructionResponsibility rooted :=
                  leftMerged.down.2.symm.trans rightObstruction.down.2
                exact nomatch impossible
              · have impossible : contributionObstructionResponsibility rooted =
                    contributionResponsibility rooted :=
                  leftObstruction.down.2.symm.trans rightMerged.down.2
                exact nomatch impossible
              · have lifted_eq : leftObstruction = rightObstruction := by
                  rcases leftObstruction with ⟨leftProof⟩
                  rcases rightObstruction with ⟨rightProof⟩
                  congr
                cases lifted_eq
                rfl

end
end M14SourceGeneratedContributionMergeLifecycle
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeLifecycle.contributionMergeBearerAt_phaseFalse
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeLifecycle.mergedContribution_bearer_is_existing_legA
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeLifecycle.contributionMergeObligationAt_injective
