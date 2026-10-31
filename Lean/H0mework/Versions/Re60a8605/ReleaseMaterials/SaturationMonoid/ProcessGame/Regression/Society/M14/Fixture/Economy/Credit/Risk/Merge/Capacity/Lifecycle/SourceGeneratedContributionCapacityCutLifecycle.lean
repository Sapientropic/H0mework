import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.World.SourceGeneratedContributionCapacityCutWorld
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Lifecycle.SourceGeneratedContributionMergeLifecycle

/-!
# Source-generated contribution-capacity cut lifecycle

Every capacity-world row reuses the already generated contribution-merge
bearer.  At the unique cut target, contribution keeps the existing `Leg.a`
bearer and obstruction keeps the existing parent bearer; only the live
progress budget changes.  No bearer, actor, pool or participant is created.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCutLifecycle

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open ComplementObservation Lifecycle Universal Relations Exchange
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeLifecycle
open M14SourceGeneratedContributionCapacityCutWorld

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

abbrev ContributionCapacityCutLifecycleSourceEvent
    (rooted : RootedFailure) :=
  (CutN rooted).Support × ExactSourceGeneratedLossAllocationMaterialWitness

def contributionCapacityCutBearerAt
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness) :
    {indexedSupport : (CutN rooted).Support} →
    OpenResponsibilityAt (CutN rooted) indexedSupport →
      Lifecycle.ActorBearer
  | (oldSupport, false), entry =>
      contributionMergeBearerAt rooted materialWitness
        (⟨entry.1, entry.2⟩ : OpenResponsibilityAt
          (M14SourceGeneratedContributionMergeWorld.TargetN rooted)
          oldSupport)
  | (((.inl oldSupport, lossPhase), mergePhase), true), entry =>
      contributionMergeBearerAt rooted materialWitness
        (⟨entry.1, entry.2⟩ : OpenResponsibilityAt
          (M14SourceGeneratedContributionMergeWorld.TargetN rooted)
          ((.inl oldSupport, lossPhase), mergePhase))
  | (((.inr direction, false), mergePhase), true), entry =>
      contributionMergeBearerAt rooted materialWitness
        (⟨entry.1, entry.2⟩ : OpenResponsibilityAt
          (M14SourceGeneratedContributionMergeWorld.TargetN rooted)
          ((.inr direction, false), mergePhase))
  | (((.inr direction, true), false), true), entry =>
      contributionMergeBearerAt rooted materialWitness
        (⟨entry.1, entry.2⟩ : OpenResponsibilityAt
          (M14SourceGeneratedContributionMergeWorld.TargetN rooted)
          ((.inr direction, true), false))
  | (((.inr direction, true), true), true), ⟨_responsibility, isOpen⟩ => by
      cases direction
      rcases isOpen with contribution | obstruction
      · exact sourceGeneratedLossAllocationMaterial.childBearerAt .a
      · exact sourceGeneratedLossAllocationMaterial.parentBearer

@[simp] theorem contributionCapacityCutBearer_initialContribution
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness) :
    contributionCapacityCutBearerAt rooted materialWitness
        (contributionCapacityCutInitialEntry rooted
          (mergedContributionEntry rooted)) =
      sourceGeneratedLossAllocationMaterial.childBearerAt .a :=
  rfl

@[simp] theorem contributionCapacityCutBearer_targetContribution
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness) :
    contributionCapacityCutBearerAt rooted materialWitness
        (contributionCapacityCutTargetContribution rooted) =
      sourceGeneratedLossAllocationMaterial.childBearerAt .a :=
  rfl

@[simp] theorem contributionCapacityCutBearer_targetObstruction
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness) :
    contributionCapacityCutBearerAt rooted materialWitness
        (contributionCapacityCutTargetObstruction rooted) =
      sourceGeneratedLossAllocationMaterial.parentBearer :=
  rfl

def contributionCapacityCutLifecycleVocabulary
    (rooted : RootedFailure) : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := ContributionCapacityCutLifecycleSourceEvent rooted
  Content := (CutN rooted).Responsibility
  Residual := Nat
  Bearer := Lifecycle.ActorBearer
  ProtectedInterest := (CutN rooted).Claim
  Scope := PUnit
  Lineage := (CutN rooted).Lineage
  Incidence := (CutN rooted).Incidence
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun sourceEvent =>
    MinimalRegistrableSourceAnchor.canonical PUnit.unit
      ((CutN rooted).lineageAt sourceEvent.1)
  sourceIncidence := fun sourceEvent =>
    (CutN rooted).incidenceAt sourceEvent.1
  ObstructionAt := fun _ => PEmpty
  demandContent := fun {_} obstruction => nomatch obstruction
  demandResidual := fun {_} obstruction => nomatch obstruction
  CommitmentAt := fun sourceEvent responsibility =>
    (CutN rooted).OpenAt sourceEvent.1 responsibility
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

abbrev ContributionCapacityCutLifecycleV (rooted : RootedFailure) :=
  contributionCapacityCutLifecycleVocabulary rooted

def contributionCapacityCutAdmissionAt
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CutN rooted).Support}
    (entry : OpenResponsibilityAt (CutN rooted) indexedSupport) :
    NativeAdmissionPayload (ContributionCapacityCutLifecycleV rooted) where
  sourceEvent := (indexedSupport, materialWitness)
  content := entry.1
  residual := entry.progressBudget
  bearer := contributionCapacityCutBearerAt rooted materialWitness entry
  beneficiary := entry.claim
  scope := PUnit.unit
  lineage := (CutN rooted).lineageAt indexedSupport
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment entry.2
  authority := PUnit.unit
  assumption := .accepted PUnit.unit
  dischargeJurisdiction := PUnit.unit

def contributionCapacityCutObligationAt
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CutN rooted).Support}
    (entry : OpenResponsibilityAt (CutN rooted) indexedSupport) :
    AdmittedObligation (ContributionCapacityCutLifecycleV rooted) :=
  (contributionCapacityCutAdmissionAt rooted materialWitness entry).toObligation

@[simp] theorem contributionCapacityCutObligation_content
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CutN rooted).Support}
    (entry : OpenResponsibilityAt (CutN rooted) indexedSupport) :
    (contributionCapacityCutObligationAt rooted materialWitness entry).content =
      entry.1 :=
  rfl

@[simp] theorem contributionCapacityCutObligation_budget
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CutN rooted).Support}
    (entry : OpenResponsibilityAt (CutN rooted) indexedSupport) :
    (contributionCapacityCutObligationAt rooted materialWitness entry).residual =
      entry.progressBudget :=
  rfl

@[simp] theorem contributionCapacityCutObligation_bearer
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CutN rooted).Support}
    (entry : OpenResponsibilityAt (CutN rooted) indexedSupport) :
    (contributionCapacityCutObligationAt rooted materialWitness entry).bearer =
      contributionCapacityCutBearerAt rooted materialWitness entry :=
  rfl

/-! ## Exact entry presentation -/

theorem contributionCapacityCutEntryKey_injective
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CutN rooted).Support} :
    Function.Injective
      (fun entry : OpenResponsibilityAt (CutN rooted) indexedSupport =>
        (entry.1,
          contributionCapacityCutBearerAt rooted materialWitness entry)) := by
  rintro ⟨leftResponsibility, leftOpen⟩
    ⟨rightResponsibility, rightOpen⟩ key_eq
  have responsibility_eq : leftResponsibility = rightResponsibility :=
    congrArg Prod.fst key_eq
  have bearer_eq := congrArg Prod.snd key_eq
  cases responsibility_eq
  rcases indexedSupport with ⟨oldSupport, cutPhase⟩
  cases cutPhase with
  | false =>
      exact contributionMergeObligationAt_injective rooted materialWitness
        (by
          rcases oldSupport with ⟨worldSupport, mergePhase⟩
          rcases worldSupport with ⟨cofaceSupport, lossPhase⟩
          cases cofaceSupport with
          | inl oldSupport =>
              cases mergePhase <;> cases lossPhase <;>
                cases oldSupport <;> cases leftResponsibility <;>
                cases leftOpen <;> cases rightOpen <;> rfl
          | inr direction =>
              cases direction
              cases mergePhase with
              | false =>
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
                      cases leftResponsibility with
                      | inl oldResponsibility =>
                          cases oldResponsibility
                          rcases leftOpen with ⟨leftLeg, leftAdmitted⟩
                          rcases rightOpen with ⟨rightLeg, rightAdmitted⟩
                          have exactBearerEq :
                              sourceGeneratedLossAllocationMaterial.childBearerAt
                                  leftLeg =
                                sourceGeneratedLossAllocationMaterial.childBearerAt
                                  rightLeg := by
                            change
                              sourceGeneratedLossAllocationMaterial.childBearerAt
                                  leftLeg =
                                sourceGeneratedLossAllocationMaterial.childBearerAt
                                  rightLeg at bearer_eq
                            exact bearer_eq
                          rcases leftAdmitted with leftAdmitted | leftAdmitted <;>
                            rcases rightAdmitted with rightAdmitted | rightAdmitted
                          · cases leftAdmitted
                            cases rightAdmitted
                            rfl
                          · cases leftAdmitted
                            cases rightAdmitted
                            exact False.elim
                              (sourceGeneratedLossAllocationMaterial.childBearersDistinct
                                exactBearerEq)
                          · cases leftAdmitted
                            cases rightAdmitted
                            exact False.elim
                              (sourceGeneratedLossAllocationMaterial.childBearersDistinct
                                exactBearerEq.symm)
                          · cases leftAdmitted
                            cases rightAdmitted
                            rfl
                      | inr responsibilityDirection =>
                          cases leftOpen
                          cases rightOpen
                          rfl
              | true =>
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
                      rcases leftOpen with leftMerged | leftObstruction <;>
                        rcases rightOpen with rightMerged | rightObstruction
                      · cases Subsingleton.elim leftMerged rightMerged
                        rfl
                      · exact False.elim (by
                          have impossible :=
                            leftMerged.down.2.symm.trans rightObstruction.down.2
                          exact nomatch impossible)
                      · exact False.elim (by
                          have impossible :=
                            leftObstruction.down.2.symm.trans rightMerged.down.2
                          exact nomatch impossible)
                      · cases Subsingleton.elim leftObstruction rightObstruction
                        rfl)
  | true =>
      rcases oldSupport with ⟨worldSupport, mergePhase⟩
      rcases worldSupport with ⟨cofaceSupport, lossPhase⟩
      cases cofaceSupport with
      | inl oldSupport =>
          cases mergePhase <;> cases lossPhase <;>
            cases oldSupport <;> cases leftResponsibility <;>
            cases leftOpen <;> cases rightOpen <;> rfl
      | inr direction =>
          cases direction
          cases lossPhase with
          | false =>
              cases mergePhase <;>
                cases leftResponsibility <;>
                cases leftOpen <;> cases rightOpen <;> rfl
          | true =>
              cases mergePhase with
              | false =>
                  cases leftResponsibility with
                  | inl oldResponsibility =>
                      cases oldResponsibility
                      rcases leftOpen with ⟨leftLeg, leftAdmitted⟩
                      rcases rightOpen with ⟨rightLeg, rightAdmitted⟩
                      have exactBearerEq :
                          sourceGeneratedLossAllocationMaterial.childBearerAt
                              leftLeg =
                            sourceGeneratedLossAllocationMaterial.childBearerAt
                              rightLeg := by
                        change
                          sourceGeneratedLossAllocationMaterial.childBearerAt
                              leftLeg =
                            sourceGeneratedLossAllocationMaterial.childBearerAt
                              rightLeg at bearer_eq
                        exact bearer_eq
                      rcases leftAdmitted with leftAdmitted | leftAdmitted <;>
                        rcases rightAdmitted with rightAdmitted | rightAdmitted
                      · cases leftAdmitted
                        cases rightAdmitted
                        rfl
                      · cases leftAdmitted
                        cases rightAdmitted
                        exact False.elim
                          (sourceGeneratedLossAllocationMaterial.childBearersDistinct
                            exactBearerEq)
                      · cases leftAdmitted
                        cases rightAdmitted
                        exact False.elim
                          (sourceGeneratedLossAllocationMaterial.childBearersDistinct
                            exactBearerEq.symm)
                      · cases leftAdmitted
                        cases rightAdmitted
                        rfl
                  | inr responsibilityDirection =>
                      cases leftOpen
                      cases rightOpen
                      rfl
              | true =>
                  rcases leftOpen with leftContribution | leftObstruction <;>
                    rcases rightOpen with rightContribution | rightObstruction
                  · cases Subsingleton.elim leftContribution rightContribution
                    rfl
                  · exact False.elim (by
                      have impossible :=
                        leftContribution.down.2.symm.trans
                          rightObstruction.down.2
                      exact nomatch impossible)
                  · exact False.elim (by
                      have impossible :=
                        leftObstruction.down.2.symm.trans
                          rightContribution.down.2
                      exact nomatch impossible)
                  · cases Subsingleton.elim leftObstruction rightObstruction
                    rfl

theorem contributionCapacityCutObligationAt_injective
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (CutN rooted).Support} :
    Function.Injective
      (contributionCapacityCutObligationAt rooted materialWitness
        (indexedSupport := indexedSupport)) := by
  intro left right obligation_eq
  apply contributionCapacityCutEntryKey_injective rooted materialWitness
  apply Prod.ext
  · exact congrArg AdmittedObligation.content obligation_eq
  · exact congrArg AdmittedObligation.bearer obligation_eq

end
end M14SourceGeneratedContributionCapacityCutLifecycle
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutLifecycle.contributionCapacityCutBearer_initialContribution
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutLifecycle.contributionCapacityCutBearer_targetContribution
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutLifecycle.contributionCapacityCutObligationAt_injective
