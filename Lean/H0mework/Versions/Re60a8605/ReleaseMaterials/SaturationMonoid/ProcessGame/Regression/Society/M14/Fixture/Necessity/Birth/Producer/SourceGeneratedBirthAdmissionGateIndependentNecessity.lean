import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Producer.SourceGeneratedContributionCapacityTargetOriginOrBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Payment.Producer.SourceGeneratedContributionCapacityU8RuntimePayment

/-!
# Independent necessity of target-origin birth admission

The existing capacity-U8 Fin-3 current gives both negative controls without
inventing a gate enum.  Its inherited contribution and inherited obstruction
rows each retain an exact old origin, current-0 generated row and causal
authority, lifecycle obligation and bearer, entry-indexed independent root
consumer, and the same actual Payment/whole-ledger write.  Their fresh-debt
and full target-indexed birth-admission fibres are empty by both old lineage
and explicit old preimage.

The same source generates the positive new-only residual admission with its
fresh debt, row, authority, obligation, existing parent bearer, and index-2
consumer.  Thus row, authority, standing, bearer, consumer, or Payment alone
cannot decide whether a target is inherited or genuinely born.  No second
root, ledger, occurrence, consumer coordinate, birth registry, or future is
introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedBirthAdmissionGateIndependentNecessity

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
open M14SourceGeneratedContributionCapacityU8Revision
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityU8RuntimePayment
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth

abbrev InheritedContributionBirthAdmissionAt (oldVisit : OldVisit) :=
  ExactContributionCapacityTargetBirthAdmissionAt oldVisit
    (contributionCapacityU8InheritedContribution oldVisit)

abbrev InheritedObstructionBirthAdmissionAt (oldVisit : OldVisit) :=
  ExactContributionCapacityTargetBirthAdmissionAt oldVisit
    (contributionCapacityU8InheritedObstruction oldVisit)

def contributionCapacityU8InitialInheritedContributionAuthorityAt
    (oldVisit : OldVisit) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8TemporalVisitAt oldVisit 0)
      (contributionCapacityU8InheritedContribution oldVisit) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (CapacityU8RootAt oldVisit)
    (contributionCapacityU8InheritedContribution oldVisit)
    (contributionCapacityU8InheritedContributionRow oldVisit)

def contributionCapacityU8InitialInheritedObstructionAuthorityAt
    (oldVisit : OldVisit) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8TemporalVisitAt oldVisit 0)
      (contributionCapacityU8InheritedObstruction oldVisit) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (CapacityU8RootAt oldVisit)
    (contributionCapacityU8InheritedObstruction oldVisit)
    (contributionCapacityU8InheritedObstructionRow oldVisit)

def contributionCapacityU8InitialInheritedContributionConsumerAt
    (oldVisit : OldVisit) :
    SourceNativeInquiryAnswerConsumerAt ()
      (ULift.up.{1, 0}
        (contributionCapacityU8InitialGenerated oldVisit).occurrence)
      (contributionCapacityU8InheritedContribution oldVisit)
      (contributionCapacityU8InitialAnswerFaceAt oldVisit) where
  projection := ContributionCapacityU8Projection.consumer 0
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def contributionCapacityU8InitialInheritedObstructionConsumerAt
    (oldVisit : OldVisit) :
    SourceNativeInquiryAnswerConsumerAt ()
      (ULift.up.{1, 0}
        (contributionCapacityU8InitialGenerated oldVisit).occurrence)
      (contributionCapacityU8InheritedObstruction oldVisit)
      (contributionCapacityU8InitialAnswerFaceAt oldVisit) where
  projection := ContributionCapacityU8Projection.consumer 1
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def inheritedContributionObligationAt
    (oldVisit : OldVisit) :
    AdmittedObligation (ContributionCapacityU8LifecycleV oldVisit) :=
  contributionCapacityU8ObligationAt oldVisit
    exactSourceGeneratedLossAllocationMaterialWitness
    (contributionCapacityU8InheritedContribution oldVisit)

def inheritedObstructionObligationAt
    (oldVisit : OldVisit) :
    AdmittedObligation (ContributionCapacityU8LifecycleV oldVisit) :=
  contributionCapacityU8ObligationAt oldVisit
    exactSourceGeneratedLossAllocationMaterialWitness
    (contributionCapacityU8InheritedObstruction oldVisit)

def inheritedContributionOldPreimageAt
    (oldVisit : OldVisit) :
    Sigma fun oldEntry : OpenResponsibilityAt
        (CutN (capacityActionRootedAt oldVisit))
        (contributionCapacityCutTargetSupport
          (capacityActionRootedAt oldVisit)) =>
      PLift
        ((CapacityCofaceAt oldVisit).cofaceLedgerRetract.forward oldEntry =
          contributionCapacityU8InheritedContribution oldVisit) :=
  ⟨contributionCapacityCutTargetContribution
      (capacityActionRootedAt oldVisit), PLift.up rfl⟩

def inheritedObstructionOldPreimageAt
    (oldVisit : OldVisit) :
    Sigma fun oldEntry : OpenResponsibilityAt
        (CutN (capacityActionRootedAt oldVisit))
        (contributionCapacityCutTargetSupport
          (capacityActionRootedAt oldVisit)) =>
      PLift
        ((CapacityCofaceAt oldVisit).cofaceLedgerRetract.forward oldEntry =
          contributionCapacityU8InheritedObstruction oldVisit) :=
  ⟨contributionCapacityCutTargetObstruction
      (capacityActionRootedAt oldVisit), PLift.up rfl⟩

theorem inheritedContributionBirth_isEmpty_fromFresh
    (oldVisit : OldVisit) :
    IsEmpty (InheritedContributionBirthAdmissionAt oldVisit) :=
  ⟨fun birth => PEmpty.elim
    ((contributionCapacityU8InheritedContributionOrigin oldVisit
      ).excludesFresh birth.freshDebt)⟩

theorem inheritedContributionBirth_isEmpty_fromOldPreimage
    (oldVisit : OldVisit) :
    IsEmpty (InheritedContributionBirthAdmissionAt oldVisit) :=
  ⟨fun birth =>
    birth.noOldPreimage.false (inheritedContributionOldPreimageAt oldVisit)⟩

theorem inheritedObstructionBirth_isEmpty_fromFresh
    (oldVisit : OldVisit) :
    IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit) :=
  ⟨fun birth => PEmpty.elim
    ((contributionCapacityU8InheritedObstructionOrigin oldVisit
      ).excludesFresh birth.freshDebt)⟩

theorem inheritedObstructionBirth_isEmpty_fromOldPreimage
    (oldVisit : OldVisit) :
    IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit) :=
  ⟨fun birth =>
    birth.noOldPreimage.false (inheritedObstructionOldPreimageAt oldVisit)⟩

theorem generatedResidual_ne_inheritedContribution
    (oldVisit : OldVisit) :
    contributionCapacityU8GeneratedResidual oldVisit ≠
      contributionCapacityU8InheritedContribution oldVisit := by
  intro targetEquality
  have fresh :=
    (sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
      ).freshDebt
  rw [targetEquality] at fresh
  exact PEmpty.elim
    ((contributionCapacityU8InheritedContributionOrigin oldVisit
      ).excludesFresh fresh)

theorem generatedResidual_ne_inheritedObstruction
    (oldVisit : OldVisit) :
    contributionCapacityU8GeneratedResidual oldVisit ≠
      contributionCapacityU8InheritedObstruction oldVisit := by
  intro targetEquality
  have fresh :=
    (sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
      ).freshDebt
  rw [targetEquality] at fresh
  exact PEmpty.elim
    ((contributionCapacityU8InheritedObstructionOrigin oldVisit
      ).excludesFresh fresh)

theorem generatedResidualOldOrigin_isEmpty (oldVisit : OldVisit) :
    IsEmpty (ExactTargetDebtOriginAt
      (contributionCapacityU8PreRevisionLedger oldVisit)
      (contributionCapacityU8GeneratedResidual oldVisit)) :=
  ⟨fun origin => PEmpty.elim
    ((sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
      ).freshDebt.excludesPrior origin.1 origin.2)⟩

structure SourceGeneratedBirthAdmissionGateIndependentNecessityAt
    (oldVisit : OldVisit) : Type 12 where
  private mk ::
  contributionOldOrigin : ExactTargetDebtOriginAt
    (contributionCapacityU8PreRevisionLedger oldVisit)
    (contributionCapacityU8InheritedContribution oldVisit)
  contributionRow :
    (contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
      (contributionCapacityU8InheritedContribution oldVisit)
  contributionRowExact : contributionRow =
    contributionCapacityU8InheritedContributionRow oldVisit
  contributionAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (CapacityU8RootAt oldVisit)
    (contributionCapacityU8TemporalVisitAt oldVisit 0)
    (contributionCapacityU8InheritedContribution oldVisit)
  contributionAuthorityExact : contributionAuthority =
    contributionCapacityU8InitialInheritedContributionAuthorityAt oldVisit
  contributionObligation :
    AdmittedObligation (ContributionCapacityU8LifecycleV oldVisit)
  contributionObligationExact : contributionObligation =
    inheritedContributionObligationAt oldVisit
  contributionBearerExisting : contributionObligation.bearer =
    sourceGeneratedLossAllocationMaterial.childBearerAt .a
  contributionConsumer : SourceNativeInquiryAnswerConsumerAt ()
    (ULift.up.{1, 0}
      (contributionCapacityU8InitialGenerated oldVisit).occurrence)
    (contributionCapacityU8InheritedContribution oldVisit)
    (contributionCapacityU8InitialAnswerFaceAt oldVisit)
  contributionConsumerExact : contributionConsumer =
    contributionCapacityU8InitialInheritedContributionConsumerAt oldVisit
  contributionBirthDeletedFromFresh :
    IsEmpty (InheritedContributionBirthAdmissionAt oldVisit)
  contributionBirthDeletedFromOldPreimage :
    IsEmpty (InheritedContributionBirthAdmissionAt oldVisit)
  obstructionOldOrigin : ExactTargetDebtOriginAt
    (contributionCapacityU8PreRevisionLedger oldVisit)
    (contributionCapacityU8InheritedObstruction oldVisit)
  obstructionRow :
    (contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
      (contributionCapacityU8InheritedObstruction oldVisit)
  obstructionRowExact : obstructionRow =
    contributionCapacityU8InheritedObstructionRow oldVisit
  obstructionAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (CapacityU8RootAt oldVisit)
    (contributionCapacityU8TemporalVisitAt oldVisit 0)
    (contributionCapacityU8InheritedObstruction oldVisit)
  obstructionAuthorityExact : obstructionAuthority =
    contributionCapacityU8InitialInheritedObstructionAuthorityAt oldVisit
  obstructionObligation :
    AdmittedObligation (ContributionCapacityU8LifecycleV oldVisit)
  obstructionObligationExact : obstructionObligation =
    inheritedObstructionObligationAt oldVisit
  obstructionBearerExisting : obstructionObligation.bearer =
    sourceGeneratedLossAllocationMaterial.parentBearer
  obstructionConsumer : SourceNativeInquiryAnswerConsumerAt ()
    (ULift.up.{1, 0}
      (contributionCapacityU8InitialGenerated oldVisit).occurrence)
    (contributionCapacityU8InheritedObstruction oldVisit)
    (contributionCapacityU8InitialAnswerFaceAt oldVisit)
  obstructionConsumerExact : obstructionConsumer =
    contributionCapacityU8InitialInheritedObstructionConsumerAt oldVisit
  obstructionBirthDeletedFromFresh :
    IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit)
  obstructionBirthDeletedFromOldPreimage :
    IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit)
  actualPayment :
    SourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit 0
  actualPaymentExact : actualPayment =
    sourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit 0
  positiveResidualBirth :
    ExactGeneratedContributionCapacityResidualBirthAdmissionAt oldVisit
  positiveResidualBirthExact : positiveResidualBirth =
    sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
  positiveResidualOldOriginDeleted : IsEmpty (ExactTargetDebtOriginAt
    (contributionCapacityU8PreRevisionLedger oldVisit)
    (contributionCapacityU8GeneratedResidual oldVisit))

/-- Sole producer.  `oldVisit` determines the complete Fin-3 inventory; no
target, index, origin, birth verdict, consumer, Payment, or future is supplied. -/
def sourceGeneratedBirthAdmissionGateIndependentNecessityAt
    (oldVisit : OldVisit) :
    SourceGeneratedBirthAdmissionGateIndependentNecessityAt oldVisit :=
  { contributionOldOrigin :=
      contributionCapacityU8InheritedContributionOrigin oldVisit
    contributionRow := contributionCapacityU8InheritedContributionRow oldVisit
    contributionRowExact := rfl
    contributionAuthority :=
      contributionCapacityU8InitialInheritedContributionAuthorityAt oldVisit
    contributionAuthorityExact := rfl
    contributionObligation := inheritedContributionObligationAt oldVisit
    contributionObligationExact := rfl
    contributionBearerExisting := rfl
    contributionConsumer :=
      contributionCapacityU8InitialInheritedContributionConsumerAt oldVisit
    contributionConsumerExact := rfl
    contributionBirthDeletedFromFresh :=
      inheritedContributionBirth_isEmpty_fromFresh oldVisit
    contributionBirthDeletedFromOldPreimage :=
      inheritedContributionBirth_isEmpty_fromOldPreimage oldVisit
    obstructionOldOrigin :=
      contributionCapacityU8InheritedObstructionOrigin oldVisit
    obstructionRow := contributionCapacityU8InheritedObstructionRow oldVisit
    obstructionRowExact := rfl
    obstructionAuthority :=
      contributionCapacityU8InitialInheritedObstructionAuthorityAt oldVisit
    obstructionAuthorityExact := rfl
    obstructionObligation := inheritedObstructionObligationAt oldVisit
    obstructionObligationExact := rfl
    obstructionBearerExisting := rfl
    obstructionConsumer :=
      contributionCapacityU8InitialInheritedObstructionConsumerAt oldVisit
    obstructionConsumerExact := rfl
    obstructionBirthDeletedFromFresh :=
      inheritedObstructionBirth_isEmpty_fromFresh oldVisit
    obstructionBirthDeletedFromOldPreimage :=
      inheritedObstructionBirth_isEmpty_fromOldPreimage oldVisit
    actualPayment :=
      sourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit 0
    actualPaymentExact := rfl
    positiveResidualBirth :=
      sourceGeneratedContributionCapacityResidualBirthAdmission oldVisit
    positiveResidualBirthExact := rfl
    positiveResidualOldOriginDeleted :=
      generatedResidualOldOrigin_isEmpty oldVisit }

namespace SourceGeneratedBirthAdmissionGateIndependentNecessityAt

variable {oldVisit : OldVisit}
  (countermodel :
    SourceGeneratedBirthAdmissionGateIndependentNecessityAt oldVisit)

include countermodel

theorem inheritedContributionMachineryRemains :
    Nonempty
        ((contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
          (contributionCapacityU8InheritedContribution oldVisit)) ∧
      Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt
        (CapacityU8RootAt oldVisit)
        (contributionCapacityU8TemporalVisitAt oldVisit 0)
        (contributionCapacityU8InheritedContribution oldVisit)) ∧
      countermodel.contributionObligation =
        inheritedContributionObligationAt oldVisit ∧
      countermodel.contributionObligation.content =
        (contributionCapacityU8InheritedContribution oldVisit).1 ∧
      countermodel.contributionObligation.bearer =
        sourceGeneratedLossAllocationMaterial.childBearerAt .a ∧
      Nonempty (SourceNativeInquiryAnswerConsumerAt ()
        (ULift.up.{1, 0}
          (contributionCapacityU8InitialGenerated oldVisit).occurrence)
        (contributionCapacityU8InheritedContribution oldVisit)
        (contributionCapacityU8InitialAnswerFaceAt oldVisit)) :=
  ⟨⟨countermodel.contributionRow⟩,
    ⟨countermodel.contributionAuthority⟩,
    countermodel.contributionObligationExact,
    by rw [countermodel.contributionObligationExact]; rfl,
    countermodel.contributionBearerExisting,
    ⟨countermodel.contributionConsumer⟩⟩

theorem inheritedObstructionMachineryRemains :
    Nonempty
        ((contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
          (contributionCapacityU8InheritedObstruction oldVisit)) ∧
      Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt
        (CapacityU8RootAt oldVisit)
        (contributionCapacityU8TemporalVisitAt oldVisit 0)
        (contributionCapacityU8InheritedObstruction oldVisit)) ∧
      countermodel.obstructionObligation =
        inheritedObstructionObligationAt oldVisit ∧
      countermodel.obstructionObligation.content =
        (contributionCapacityU8InheritedObstruction oldVisit).1 ∧
      countermodel.obstructionObligation.bearer =
        sourceGeneratedLossAllocationMaterial.parentBearer ∧
      Nonempty (SourceNativeInquiryAnswerConsumerAt ()
        (ULift.up.{1, 0}
          (contributionCapacityU8InitialGenerated oldVisit).occurrence)
        (contributionCapacityU8InheritedObstruction oldVisit)
        (contributionCapacityU8InitialAnswerFaceAt oldVisit)) :=
  ⟨⟨countermodel.obstructionRow⟩,
    ⟨countermodel.obstructionAuthority⟩,
    countermodel.obstructionObligationExact,
    by rw [countermodel.obstructionObligationExact]; rfl,
    countermodel.obstructionBearerExisting,
    ⟨countermodel.obstructionConsumer⟩⟩

theorem onePaymentCarriesEveryTarget :
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
          (contributionCapacityU8RuntimePaymentRowEvolutionAt oldVisit 0 2) :=
  ⟨countermodel.actualPayment.everyRowEvolved 0,
    countermodel.actualPayment.everyRowEvolved 1,
    countermodel.actualPayment.everyRowEvolved 2⟩

theorem entryConsumersAndPaymentShareCurrent :
    (contributionCapacityU8InitialGenerated oldVisit).occurrence =
        (contributionCapacityU8RuntimePaymentRootEventAt oldVisit 0
          ).occurrence ∧
      countermodel.contributionConsumer.projection =
        ContributionCapacityU8Projection.consumer 0 ∧
      countermodel.obstructionConsumer.projection =
        ContributionCapacityU8Projection.consumer 1 ∧
      countermodel.positiveResidualBirth.consumer.projection =
        ContributionCapacityU8Projection.consumer 2 := by
  rw [countermodel.contributionConsumerExact,
    countermodel.obstructionConsumerExact,
    countermodel.positiveResidualBirthExact]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem provenanceExclusive :
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
        (contributionCapacityU8GeneratedResidual oldVisit)) :=
  ⟨⟨countermodel.contributionOldOrigin⟩,
    countermodel.contributionBirthDeletedFromFresh,
    ⟨countermodel.obstructionOldOrigin⟩,
    countermodel.obstructionBirthDeletedFromFresh,
    ⟨countermodel.positiveResidualBirth⟩,
    countermodel.positiveResidualOldOriginDeleted⟩

theorem obstructionAndResidualShareBearerButNotOrigin :
    countermodel.obstructionObligation.bearer =
        countermodel.positiveResidualBirth.obligation.bearer ∧
      IsEmpty (InheritedObstructionBirthAdmissionAt oldVisit) ∧
      Nonempty (ExactGeneratedContributionCapacityResidualBirthAdmissionAt
        oldVisit) :=
  ⟨countermodel.obstructionBearerExisting.trans
      countermodel.positiveResidualBirth.bearerExisting.symm,
    countermodel.obstructionBirthDeletedFromOldPreimage,
    ⟨countermodel.positiveResidualBirth⟩⟩

end SourceGeneratedBirthAdmissionGateIndependentNecessityAt

theorem remainingAuthorityCannotReconstructInheritedContributionBirth
    (oldVisit : OldVisit) :
    IsEmpty
      (SourceGeneratedBirthAdmissionGateIndependentNecessityAt oldVisit →
        InheritedContributionBirthAdmissionAt oldVisit) :=
  ⟨fun reconstruct =>
    (inheritedContributionBirth_isEmpty_fromFresh oldVisit).false
      (reconstruct
        (sourceGeneratedBirthAdmissionGateIndependentNecessityAt oldVisit))⟩

theorem remainingAuthorityCannotReconstructInheritedObstructionBirth
    (oldVisit : OldVisit) :
    IsEmpty
      (SourceGeneratedBirthAdmissionGateIndependentNecessityAt oldVisit →
        InheritedObstructionBirthAdmissionAt oldVisit) :=
  ⟨fun reconstruct =>
    (inheritedObstructionBirth_isEmpty_fromFresh oldVisit).false
      (reconstruct
        (sourceGeneratedBirthAdmissionGateIndependentNecessityAt oldVisit))⟩

theorem birthAdmissionGate_negativeControls (oldVisit : OldVisit) : True := by
  let countermodel :=
    sourceGeneratedBirthAdmissionGateIndependentNecessityAt oldVisit
  fail_if_success exact
    (countermodel.contributionRow :
      InheritedContributionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.contributionAuthority :
      InheritedContributionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.contributionObligation :
      InheritedContributionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.contributionConsumer :
      InheritedContributionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.obstructionRow :
      InheritedObstructionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.obstructionAuthority :
      InheritedObstructionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.obstructionObligation :
      InheritedObstructionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.obstructionConsumer :
      InheritedObstructionBirthAdmissionAt oldVisit)
  fail_if_success exact
    (countermodel.positiveResidualBirth :
      InheritedObstructionBirthAdmissionAt oldVisit)
  fail_if_success exact countermodel.target
  fail_if_success exact countermodel.registry
  fail_if_success exact countermodel.coverage
  fail_if_success exact countermodel.history
  fail_if_success exact countermodel.future
  trivial

end
end M14SourceGeneratedBirthAdmissionGateIndependentNecessity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBirthAdmissionGateIndependentNecessity.sourceGeneratedBirthAdmissionGateIndependentNecessityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBirthAdmissionGateIndependentNecessity.SourceGeneratedBirthAdmissionGateIndependentNecessityAt.onePaymentCarriesEveryTarget
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBirthAdmissionGateIndependentNecessity.SourceGeneratedBirthAdmissionGateIndependentNecessityAt.entryConsumersAndPaymentShareCurrent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBirthAdmissionGateIndependentNecessity.SourceGeneratedBirthAdmissionGateIndependentNecessityAt.obstructionAndResidualShareBearerButNotOrigin
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedBirthAdmissionGateIndependentNecessity.remainingAuthorityCannotReconstructInheritedObstructionBirth
