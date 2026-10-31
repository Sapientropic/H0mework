import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Compiler.SourceGeneratedLossAllocationCompiler

/-!
# M14 source-generated loss-allocation lifecycle

The exact three-row first write is presented to the existing responsibility
lifecycle without a loss-share carrier.  Parent and children retain the same
world responsibility and claim.  The only child distinction is the existing
proof-relevant exchange `Leg` admission, whose bearer is read from the
zero-choice C4/C5 loss-allocation material.

This layer installs the occurrence-material-indexed lifecycle vocabulary,
exact obligations, bearer readout and injective entry presentation.  Split
receipts and compiler certification remain in the downstream restructuring
module.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedLossAllocationRestructuring

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open ComplementObservation Lifecycle Universal Relations Exchange
open M3FiniteExchangeFixture
open M14SourceGeneratedClearingBackstopActivation
open M14SourceClearingBackstopCreditStanding
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationCompiler

variable
    {OldV : ConstructiveRoot.Vocabulary}
    {oldWorld : SourceNativeAuthoritativeRootClosure OldN OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus OldN}
    {oldTheory : TheoryState OldN}
    {support : OldN.Support}
    {obstruction : OldN.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

local notation "RootedFailure" => RootedActualExpressibilityFailureAt
  oldWorld oldVisit U7 failure

abbrev LossLifecycleSourceEvent (rooted : RootedFailure) :=
  (LossN rooted).Support × ExactSourceGeneratedLossAllocationMaterialWitness

/-! ## Exact lifecycle presentation -/

/-- Bearer identity is read from the canonical material.  At the target
support the two admitted child witnesses select the two existing exchange
bearers; every non-child row keeps the already generated parent bearer. -/
def lossAllocationBearerAt (rooted : RootedFailure)
    (_materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (LossN rooted).Support}
    (entry : OpenResponsibilityAt (LossN rooted) indexedSupport) :
    Lifecycle.ActorBearer := by
  rcases indexedSupport with ⟨worldSupport, phase⟩
  rcases entry with ⟨responsibility, isOpen⟩
  cases phase with
  | false => exact sourceGeneratedLossAllocationMaterial.parentBearer
  | true =>
      cases worldSupport with
      | inl oldSupport =>
          exact sourceGeneratedLossAllocationMaterial.parentBearer
      | inr direction =>
          cases responsibility with
          | inl oldResponsibility =>
              change { leg : Leg // ExistingLossChildLegAt leg } at isOpen
              exact sourceGeneratedLossAllocationMaterial.childBearerAt
                isOpen.1
          | inr generatedResponsibility =>
              exact sourceGeneratedLossAllocationMaterial.parentBearer

/-- Existing world support is the lifecycle source event.  No side event or
participant registry is introduced. -/
def lossAllocationLifecycleVocabulary (rooted : RootedFailure) :
    ResponsibilityLifecycle.Vocabulary where
  SourceEvent := LossLifecycleSourceEvent rooted
  Content := (LossN rooted).Responsibility
  Residual := Nat
  Bearer := Lifecycle.ActorBearer
  ProtectedInterest := (LossN rooted).Claim
  Scope := PUnit
  Lineage := (LossN rooted).Lineage
  Incidence := (LossN rooted).Incidence
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun sourceEvent =>
    MinimalRegistrableSourceAnchor.canonical PUnit.unit
      ((LossN rooted).lineageAt sourceEvent.1)
  sourceIncidence := fun sourceEvent =>
    (LossN rooted).incidenceAt sourceEvent.1
  ObstructionAt := fun _ => PEmpty
  demandContent := fun {_} obstruction => nomatch obstruction
  demandResidual := fun {_} obstruction => nomatch obstruction
  CommitmentAt := fun sourceEvent responsibility =>
    (LossN rooted).OpenAt sourceEvent.1 responsibility
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

abbrev LossLifecycleV (rooted : RootedFailure) :=
  lossAllocationLifecycleVocabulary rooted

def lossAllocationAdmissionAt (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (LossN rooted).Support}
    (entry : OpenResponsibilityAt (LossN rooted) indexedSupport) :
    NativeAdmissionPayload (LossLifecycleV rooted) where
  sourceEvent := (indexedSupport, materialWitness)
  content := entry.1
  residual := entry.progressBudget
  bearer := lossAllocationBearerAt rooted materialWitness entry
  beneficiary := entry.claim
  scope := PUnit.unit
  lineage := (LossN rooted).lineageAt indexedSupport
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .explicitCommitment entry.2
  authority := PUnit.unit
  assumption := .accepted PUnit.unit
  dischargeJurisdiction := PUnit.unit

def lossAllocationObligationAt (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (LossN rooted).Support}
    (entry : OpenResponsibilityAt (LossN rooted) indexedSupport) :
    AdmittedObligation (LossLifecycleV rooted) :=
  (lossAllocationAdmissionAt rooted materialWitness entry).toObligation

@[simp] theorem lossAllocationObligation_content
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (LossN rooted).Support}
    (entry : OpenResponsibilityAt (LossN rooted) indexedSupport) :
    (lossAllocationObligationAt rooted materialWitness entry).content = entry.1 :=
  rfl

@[simp] theorem lossAllocationObligation_bearer
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (LossN rooted).Support}
    (entry : OpenResponsibilityAt (LossN rooted) indexedSupport) :
    (lossAllocationObligationAt rooted materialWitness entry).bearer =
      lossAllocationBearerAt rooted materialWitness entry :=
  rfl

theorem lossAllocationObligationAt_injective
    (rooted : RootedFailure)
    (materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness)
    {indexedSupport : (LossN rooted).Support} :
    Function.Injective
      (lossAllocationObligationAt rooted materialWitness
        (indexedSupport := indexedSupport)) := by
  rintro ⟨leftResponsibility, leftOpen⟩
    ⟨rightResponsibility, rightOpen⟩ obligation_eq
  have responsibility_eq : leftResponsibility = rightResponsibility :=
    congrArg AdmittedObligation.content obligation_eq
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
                      rightLeg :=
                by
                  have exactBearerEq :=
                    congrArg AdmittedObligation.bearer obligation_eq
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

end
end M14SourceGeneratedLossAllocationRestructuring
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationRestructuring.lossAllocationObligationAt_injective
