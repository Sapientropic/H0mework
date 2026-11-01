import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Birth.Producer.SourceGeneratedBirthAdmissionGateIndependentNecessity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Consumer.ProofCarryingContributionCapacityTargetOriginOrBirth

/-!
# Direct consumer of birth-admission independent necessity

One actual U8 Payment carries all three rows.  Both inherited targets retain
row, causal authority, lifecycle standing, existing bearer, and their own
entry-indexed consumer, yet have no full birth admission.  The generated
residual has the positive complete admission and no old origin.  In
particular the obstruction row and newborn share the same parent bearer, so
bearer identity cannot reconstruct birth authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingBirthAdmissionGateIndependentNecessityRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityU8RuntimePayment
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth
open M14ProofCarryingContributionCapacityTargetOriginOrBirth
open M14SourceGeneratedBirthAdmissionGateIndependentNecessity
open M14SourceGeneratedBirthAdmissionGateIndependentNecessity.SourceGeneratedBirthAdmissionGateIndependentNecessityAt

abbrev CanonicalBirthAdmissionGateCountermodelAt (oldVisit : OldVisit) :=
  SourceGeneratedBirthAdmissionGateIndependentNecessityAt oldVisit

def canonicalBirthAdmissionGateCountermodelAt
    (oldVisit : OldVisit) :
    CanonicalBirthAdmissionGateCountermodelAt oldVisit :=
  sourceGeneratedBirthAdmissionGateIndependentNecessityAt oldVisit

abbrev InheritedContributionMachineryAt (oldVisit : OldVisit) : Prop :=
  Nonempty
      ((contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
        (contributionCapacityU8InheritedContribution oldVisit)) ∧
    Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8TemporalVisitAt oldVisit 0)
      (contributionCapacityU8InheritedContribution oldVisit)) ∧
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).contributionObligation = inheritedContributionObligationAt oldVisit ∧
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).contributionObligation.content =
      (contributionCapacityU8InheritedContribution oldVisit).1 ∧
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).contributionObligation.bearer =
      sourceGeneratedLossAllocationMaterial.childBearerAt .a ∧
    Nonempty (SourceNativeInquiryAnswerConsumerAt ()
      (ULift.up.{1, 0}
        (contributionCapacityU8InitialGenerated oldVisit).occurrence)
      (contributionCapacityU8InheritedContribution oldVisit)
      (contributionCapacityU8InitialAnswerFaceAt oldVisit))

abbrev InheritedObstructionMachineryAt (oldVisit : OldVisit) : Prop :=
  Nonempty
      ((contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
        (contributionCapacityU8InheritedObstruction oldVisit)) ∧
    Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8TemporalVisitAt oldVisit 0)
      (contributionCapacityU8InheritedObstruction oldVisit)) ∧
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).obstructionObligation = inheritedObstructionObligationAt oldVisit ∧
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).obstructionObligation.content =
      (contributionCapacityU8InheritedObstruction oldVisit).1 ∧
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).obstructionObligation.bearer =
      sourceGeneratedLossAllocationMaterial.parentBearer ∧
    Nonempty (SourceNativeInquiryAnswerConsumerAt ()
      (ULift.up.{1, 0}
        (contributionCapacityU8InitialGenerated oldVisit).occurrence)
      (contributionCapacityU8InheritedObstruction oldVisit)
      (contributionCapacityU8InitialAnswerFaceAt oldVisit))

abbrev BirthProvenanceExclusiveAt (oldVisit : OldVisit) : Prop :=
  Nonempty (ExactTargetDebtOriginAt
      (contributionCapacityU8PreRevisionLedger oldVisit)
      (contributionCapacityU8InheritedContribution oldVisit)) ∧
    IsEmpty (InheritedContributionBirthAdmissionAt oldVisit) ∧
    Nonempty (ExactTargetDebtOriginAt
      (contributionCapacityU8PreRevisionLedger oldVisit)
      (contributionCapacityU8InheritedObstruction oldVisit)) ∧
    IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit) ∧
    Nonempty (ExactGeneratedContributionCapacityResidualBirthAdmissionAt
      oldVisit) ∧
    IsEmpty (ExactTargetDebtOriginAt
      (contributionCapacityU8PreRevisionLedger oldVisit)
      (contributionCapacityU8GeneratedResidual oldVisit))

theorem consumerCoordinatesDistinct :
    ContributionCapacityU8Projection.consumer 0 ≠
        ContributionCapacityU8Projection.consumer 1 ∧
      ContributionCapacityU8Projection.consumer 0 ≠
        ContributionCapacityU8Projection.consumer 2 ∧
      ContributionCapacityU8Projection.consumer 1 ≠
        ContributionCapacityU8Projection.consumer 2 := by
  constructor
  · intro equality
    have indexEquality := ContributionCapacityU8Projection.consumer.inj equality
    omega
  constructor
  · intro equality
    have indexEquality := ContributionCapacityU8Projection.consumer.inj equality
    omega
  · intro equality
    have indexEquality := ContributionCapacityU8Projection.consumer.inj equality
    omega

theorem inheritedContributionObligation_ne_generatedResidual
    (oldVisit : OldVisit) :
    inheritedContributionObligationAt oldVisit ≠
      (sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
        ).obligation := by
  intro obligationEquality
  rw [(sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
    ).obligationExact] at obligationEquality
  have entryEquality :=
    contributionCapacityU8ObligationAt_injective oldVisit
      exactSourceGeneratedLossAllocationMaterialWitness obligationEquality
  exact generatedResidual_ne_inheritedContribution oldVisit entryEquality.symm

theorem inheritedObstructionObligation_ne_generatedResidual
    (oldVisit : OldVisit) :
    inheritedObstructionObligationAt oldVisit ≠
      (sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
        ).obligation := by
  intro obligationEquality
  rw [(sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
    ).obligationExact] at obligationEquality
  have entryEquality :=
    contributionCapacityU8ObligationAt_injective oldVisit
      exactSourceGeneratedLossAllocationMaterialWitness obligationEquality
  exact generatedResidual_ne_inheritedObstruction oldVisit entryEquality.symm

theorem birthAdmissionGateCountermodelAt (oldVisit : OldVisit) :
    Nonempty (CanonicalBirthAdmissionGateCountermodelAt oldVisit) ∧
      InheritedContributionMachineryAt oldVisit ∧
      InheritedObstructionMachineryAt oldVisit ∧
      BirthProvenanceExclusiveAt oldVisit ∧
      (canonicalBirthAdmissionGateCountermodelAt oldVisit
        ).obstructionObligation.bearer =
        (canonicalBirthAdmissionGateCountermodelAt oldVisit
          ).positiveResidualBirth.obligation.bearer ∧
      IsEmpty (InheritedContributionBirthAdmissionAt oldVisit) ∧
      IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit) :=
  let countermodel := canonicalBirthAdmissionGateCountermodelAt oldVisit
  ⟨⟨countermodel⟩,
    countermodel.inheritedContributionMachineryRemains,
    countermodel.inheritedObstructionMachineryRemains,
    countermodel.provenanceExclusive,
    countermodel.obstructionAndResidualShareBearerButNotOrigin.1,
    countermodel.contributionBirthDeletedFromOldPreimage,
    countermodel.obstructionBirthDeletedFromOldPreimage⟩

structure ProofCarryingBirthAdmissionGateIndependentNecessityCertificate : Prop where
  existingOriginOrBirth :
    ProofCarryingContributionCapacityTargetOriginOrBirth
  everyOldVisitCountermodel : ∀ oldVisit : OldVisit,
    Nonempty (CanonicalBirthAdmissionGateCountermodelAt oldVisit)
  everyOldVisitContributionMachinery : ∀ oldVisit : OldVisit,
    InheritedContributionMachineryAt oldVisit
  everyOldVisitObstructionMachinery : ∀ oldVisit : OldVisit,
    InheritedObstructionMachineryAt oldVisit
  everyOldVisitOneActualPayment : ∀ oldVisit : OldVisit,
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit 0
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityU8InheritedContribution oldVisit) =
      .evolved
        (contributionCapacityU8RuntimePaymentRowEvolutionAt oldVisit 0 0) ∧
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit 0
        ).wholeLedgerWriteBack.entryDisposition
          (contributionCapacityU8InheritedObstruction oldVisit) =
        .evolved
          (contributionCapacityU8RuntimePaymentRowEvolutionAt oldVisit 0 1) ∧
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit 0
        ).wholeLedgerWriteBack.entryDisposition
          (contributionCapacityU8GeneratedResidual oldVisit) =
        .evolved
          (contributionCapacityU8RuntimePaymentRowEvolutionAt oldVisit 0 2)
  everyOldVisitSameOccurrenceAndConsumers : ∀ oldVisit : OldVisit,
    let countermodel := canonicalBirthAdmissionGateCountermodelAt oldVisit
    (contributionCapacityU8InitialGenerated oldVisit).occurrence =
        (contributionCapacityU8RuntimePaymentRootEventAt oldVisit 0
          ).occurrence ∧
      countermodel.contributionConsumer.projection =
        ContributionCapacityU8Projection.consumer 0 ∧
      countermodel.obstructionConsumer.projection =
        ContributionCapacityU8Projection.consumer 1 ∧
      countermodel.positiveResidualBirth.consumer.projection =
        ContributionCapacityU8Projection.consumer 2
  everyOldVisitExclusiveProvenance : ∀ oldVisit : OldVisit,
    BirthProvenanceExclusiveAt oldVisit
  everyOldVisitBothEmptyRoutes : ∀ oldVisit : OldVisit,
    IsEmpty (InheritedContributionBirthAdmissionAt oldVisit) ∧
      IsEmpty (InheritedContributionBirthAdmissionAt oldVisit) ∧
      IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit) ∧
      IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit)
  sameBearerStillNeedsBirthOrigin : ∀ oldVisit : OldVisit,
    let countermodel := canonicalBirthAdmissionGateCountermodelAt oldVisit
    countermodel.obstructionObligation.bearer =
        countermodel.positiveResidualBirth.obligation.bearer ∧
      IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit) ∧
      Nonempty (ExactGeneratedContributionCapacityResidualBirthAdmissionAt
        oldVisit)
  obligationsDoNotRetype : ∀ oldVisit : OldVisit,
    inheritedContributionObligationAt oldVisit ≠
        (sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
          ).obligation ∧
      inheritedObstructionObligationAt oldVisit ≠
        (sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
          ).obligation
  consumerCoordinatesDoNotCollapse :
    ContributionCapacityU8Projection.consumer 0 ≠
        ContributionCapacityU8Projection.consumer 1 ∧
      ContributionCapacityU8Projection.consumer 0 ≠
        ContributionCapacityU8Projection.consumer 2 ∧
      ContributionCapacityU8Projection.consumer 1 ≠
        ContributionCapacityU8Projection.consumer 2
  noContributionBirthReconstruction : ∀ oldVisit : OldVisit,
    IsEmpty
      (CanonicalBirthAdmissionGateCountermodelAt oldVisit →
        InheritedContributionBirthAdmissionAt oldVisit)
  noObstructionBirthReconstruction : ∀ oldVisit : OldVisit,
    IsEmpty
      (CanonicalBirthAdmissionGateCountermodelAt oldVisit →
        InheritedObstructionBirthAdmissionAt oldVisit)

theorem proofCarryingBirthAdmissionGateIndependentNecessityDirectConsumer :
    ProofCarryingBirthAdmissionGateIndependentNecessityCertificate where
  existingOriginOrBirth :=
    proofCarryingContributionCapacityTargetOriginOrBirth
  everyOldVisitCountermodel := fun oldVisit =>
    ⟨canonicalBirthAdmissionGateCountermodelAt oldVisit⟩
  everyOldVisitContributionMachinery := fun oldVisit =>
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).inheritedContributionMachineryRemains
  everyOldVisitObstructionMachinery := fun oldVisit =>
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).inheritedObstructionMachineryRemains
  everyOldVisitOneActualPayment := fun oldVisit =>
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).onePaymentCarriesEveryTarget
  everyOldVisitSameOccurrenceAndConsumers := fun oldVisit =>
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).entryConsumersAndPaymentShareCurrent
  everyOldVisitExclusiveProvenance := fun oldVisit =>
    (canonicalBirthAdmissionGateCountermodelAt oldVisit).provenanceExclusive
  everyOldVisitBothEmptyRoutes := fun oldVisit =>
    ⟨inheritedContributionBirth_isEmpty_fromFresh oldVisit,
      inheritedContributionBirth_isEmpty_fromOldPreimage oldVisit,
      inheritedObstructionBirth_isEmpty_fromFresh oldVisit,
      inheritedObstructionBirth_isEmpty_fromOldPreimage oldVisit⟩
  sameBearerStillNeedsBirthOrigin := fun oldVisit =>
    (canonicalBirthAdmissionGateCountermodelAt oldVisit
      ).obstructionAndResidualShareBearerButNotOrigin
  obligationsDoNotRetype := fun oldVisit =>
    ⟨inheritedContributionObligation_ne_generatedResidual oldVisit,
      inheritedObstructionObligation_ne_generatedResidual oldVisit⟩
  consumerCoordinatesDoNotCollapse := consumerCoordinatesDistinct
  noContributionBirthReconstruction :=
    remainingAuthorityCannotReconstructInheritedContributionBirth
  noObstructionBirthReconstruction :=
    remainingAuthorityCannotReconstructInheritedObstructionBirth

theorem birthAdmissionGateNecessity_negativeControls
    (oldVisit : OldVisit) : True := by
  let countermodel := canonicalBirthAdmissionGateCountermodelAt oldVisit
  fail_if_success exact
    (countermodel.contributionConsumer :
      InheritedObstructionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.obstructionConsumer :
      InheritedContributionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.positiveResidualBirth :
      InheritedContributionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.actualPayment :
      InheritedObstructionBirthAdmissionAt oldVisit)
  fail_if_success exact countermodel.gateKind
  fail_if_success exact countermodel.registry
  fail_if_success exact countermodel.coverage
  fail_if_success exact countermodel.history
  fail_if_success exact countermodel.future
  trivial

end
end M14ProofCarryingBirthAdmissionGateIndependentNecessityRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBirthAdmissionGateIndependentNecessityRegression.birthAdmissionGateCountermodelAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBirthAdmissionGateIndependentNecessityRegression.inheritedObstructionObligation_ne_generatedResidual
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBirthAdmissionGateIndependentNecessityRegression.proofCarryingBirthAdmissionGateIndependentNecessityDirectConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingBirthAdmissionGateIndependentNecessityRegression.birthAdmissionGateNecessity_negativeControls
