import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Handoff.Accountability.SourceGeneratedContributionCapacitySettlementSurvivorAccountability
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Clearing.Backstop.PeriodicClearingBackstopRenewal

/-!
# Source-generated joint material for final contribution-capacity settlement

The exact survivor visit at local index `2` owns the complete two-row
accountability source.  At the same numerical depth, the original joint root
independently generates common clearing, clearing backstop, payment and the
next actionable-exit renewal.  These joint-root axes share one
`temporalVisitAt depth`; they are not retyped as the survivor occurrence.

This material is only the source of a later terminal action.  It contains no
target network, support, root, terminal label, settlement receipt, finite
patch, branch or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementMaterial

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacitySettlementSurvivorAccountability
open M9ProofCarryingRenewalInquiryRoot
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14PeriodicCommonClearingRenewal
open M14PeriodicClearingBackstopRenewal

def contributionCapacityJointSettlementSurvivorCurrentIndex : Nat := 2

/-- The joint material uses the survivor root's actual current as its global
periodic depth.  No separate scheduler coordinate is introduced. -/
def contributionCapacityJointSettlementDepthAt (sourceIndex : Nat) : Nat :=
  contributionCapacitySettlementSurvivorInitialCurrentAt sourceIndex +
    contributionCapacityJointSettlementSurvivorCurrentIndex

@[simp] theorem contributionCapacityJointSettlementDepthAt_one :
    contributionCapacityJointSettlementDepthAt 1 = 12 :=
  rfl

abbrev ContributionCapacityJointSettlementSurvivorRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  CanonicalSurvivorRootAt oldVisit sourceIndex

def contributionCapacityJointSettlementSurvivorVisitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacitySettlementSurvivorVisitAt oldVisit sourceIndex
    contributionCapacityJointSettlementSurvivorCurrentIndex

@[simp] theorem contributionCapacityJointSettlementSurvivorVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (show Nat from
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
        sourceIndex).current) =
      contributionCapacityJointSettlementDepthAt sourceIndex := by
  unfold contributionCapacityJointSettlementSurvivorVisitAt
  unfold contributionCapacityJointSettlementDepthAt
  exact contributionCapacitySettlementSurvivorVisit_current_exact oldVisit
    sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex

@[simp] theorem contributionCapacityJointSettlementSurvivorVisit_current_one
    (oldVisit : OldVisit) :
    (show Nat from
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit 1).current) =
      12 := by
  rw [contributionCapacityJointSettlementSurvivorVisit_current_exact,
    contributionCapacityJointSettlementDepthAt_one]

def contributionCapacityJointSettlementSurvivorSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ExactTemporalCausalRootEventAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
        sourceIndex) :=
  (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex
    ).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)

/-- Target-free material generated from one exact survivor occurrence and the
same-depth material axes of the original joint root.  The private constructor
and exactness fields leave one canonical public producer. -/
structure SourceGeneratedContributionCapacityJointSettlementMaterialAt
    (oldVisit : OldVisit) (sourceIndex : Nat) where
  private mk ::
  sourceEvent : ExactTemporalCausalRootEventAt
    (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex
      ).toAuthoritativeRoot.toLedgerRoot
    (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)
  sourceEventExact : sourceEvent =
    contributionCapacityJointSettlementSurvivorSourceEventAt oldVisit
      sourceIndex
  authorityAt : (entryIndex : Fin 2) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)
      (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)
  authorityAtExact : authorityAt = fun entryIndex =>
    contributionCapacitySettlementSurvivorEntryAuthorityAt oldVisit
      sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex
      entryIndex
  consumerAt : (entryIndex : Fin 2) →
    SourceNativeInquiryAnswerConsumerAt ()
      (contributionCapacitySettlementSurvivorEntryInquiryEventAt oldVisit
        sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex)
      (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)
      (contributionCapacitySettlementSurvivorEntryAnswerFaceAt oldVisit
        sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex
        entryIndex)
  consumerAtExact : consumerAt = fun entryIndex =>
    contributionCapacitySettlementSurvivorEntryAnswerConsumerAt oldVisit
      sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex
      entryIndex
  accountability :
    ContributionCapacitySettlementSurvivorAccountabilityAtCurrent oldVisit
      sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex
  consumerProjectionInjective : Function.Injective
    ContributionCapacitySettlementSurvivorProjection.consumer
  commonClearing : SourceGeneratedProofCarryingPeriodicSymmetricClearingAt
    (contributionCapacityJointSettlementDepthAt sourceIndex)
  commonClearingExact : commonClearing =
    sourceGeneratedProofCarryingPeriodicSymmetricClearingAt
      (contributionCapacityJointSettlementDepthAt sourceIndex)
  clearingBackstop : SourceGeneratedProofCarryingPeriodicClearingBackstopAt
    (contributionCapacityJointSettlementDepthAt sourceIndex)
  clearingBackstopExact : clearingBackstop =
    sourceGeneratedProofCarryingPeriodicClearingBackstopAt
      (contributionCapacityJointSettlementDepthAt sourceIndex)
  clearingBackstopCommonClearingExact :
    clearingBackstop.commonClearing = commonClearing
  sourceActualService : PeriodicActualServiceExitAt
    (contributionCapacityJointSettlementDepthAt sourceIndex)
  sourceActualServiceExact : sourceActualService =
    periodicActualServiceExitAt
      (contributionCapacityJointSettlementDepthAt sourceIndex)

/-- Sole producer.  The caller supplies neither a row nor a consumer; the
complete `Fin 2` family is recomputed from the exact survivor visit. -/
def sourceGeneratedContributionCapacityJointSettlementMaterialAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
      sourceIndex :=
  { sourceEvent :=
      contributionCapacityJointSettlementSurvivorSourceEventAt oldVisit
        sourceIndex
    sourceEventExact := rfl
    authorityAt := fun entryIndex =>
      contributionCapacitySettlementSurvivorEntryAuthorityAt oldVisit
        sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex
        entryIndex
    authorityAtExact := rfl
    consumerAt := fun entryIndex =>
      contributionCapacitySettlementSurvivorEntryAnswerConsumerAt oldVisit
        sourceIndex contributionCapacityJointSettlementSurvivorCurrentIndex
        entryIndex
    consumerAtExact := rfl
    accountability :=
      (generatedSettlementSurvivorWholeLedgerAccountability oldVisit
        sourceIndex).2 contributionCapacityJointSettlementSurvivorCurrentIndex
    consumerProjectionInjective :=
      contributionCapacitySettlementSurvivorConsumerProjections_injective
    commonClearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt
        (contributionCapacityJointSettlementDepthAt sourceIndex)
    commonClearingExact := rfl
    clearingBackstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt
        (contributionCapacityJointSettlementDepthAt sourceIndex)
    clearingBackstopExact := rfl
    clearingBackstopCommonClearingExact := rfl
    sourceActualService := periodicActualServiceExitAt
      (contributionCapacityJointSettlementDepthAt sourceIndex)
    sourceActualServiceExact := rfl }

/-- The private carrier has one source-fixed inhabitant: all data fields are
definitionally pinned to the canonical producers, while the remaining fields
are proofs. -/
theorem contributionCapacityJointSettlementMaterial_eq_canonical
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material :
      SourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
        sourceIndex) :
    material =
      sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
        sourceIndex := by
  rcases material with
    ⟨sourceEvent, sourceEventExact, authorityAt, authorityAtExact,
      consumerAt, consumerAtExact, accountability,
      consumerProjectionInjective, commonClearing, commonClearingExact,
      clearingBackstop, clearingBackstopExact,
      clearingBackstopCommonClearingExact, sourceActualService,
      sourceActualServiceExact⟩
  subst sourceEvent
  subst authorityAt
  subst consumerAt
  subst commonClearing
  subst clearingBackstop
  subst sourceActualService
  rfl

/-- Every row of the existing complete ledger is present as concrete causal
authority and an independently indexed answer consumer. -/
theorem contributionCapacityJointSettlement_everyRow_accountable
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    Nonempty
        (SourceNativeLivingTemporalCausalEntryAuthorityAt
          (ContributionCapacityJointSettlementSurvivorRootAt oldVisit
            sourceIndex)
          (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
            sourceIndex)
          (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)) ∧
      Nonempty
        (SourceNativeInquiryAnswerConsumerAt ()
          (contributionCapacitySettlementSurvivorEntryInquiryEventAt oldVisit
            sourceIndex
            contributionCapacityJointSettlementSurvivorCurrentIndex)
          (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex)
          (contributionCapacitySettlementSurvivorEntryAnswerFaceAt oldVisit
            sourceIndex
            contributionCapacityJointSettlementSurvivorCurrentIndex
            entryIndex)) := by
  let material :=
    sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
      sourceIndex
  exact ⟨⟨material.authorityAt entryIndex⟩,
    ⟨material.consumerAt entryIndex⟩⟩

/-- Common clearing, clearing backstop and the source-current actual service
are three restrictions of the original joint root's exact event at the common
numerical depth.  This service is not a stored successor renewal. -/
theorem contributionCapacityJointSettlement_jointRootAxes_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let material :=
      sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
        sourceIndex
    let depth := contributionCapacityJointSettlementDepthAt sourceIndex
    material.commonClearing.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      material.clearingBackstop.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) ∧
      material.sourceActualService.paymentOccurrence.rootOccurrence =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt depth) := by
  let material :=
    sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
      sourceIndex
  exact ⟨material.commonClearing.rootOccurrenceExact,
    material.clearingBackstop.rootOccurrenceExact,
    material.sourceActualService.paymentOccurrence.rootOccurrence_eq⟩

theorem contributionCapacityJointSettlement_jointRootAxes_shareOccurrence
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let material :=
      sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
        sourceIndex
    material.commonClearing.rootOccurrence =
        material.clearingBackstop.rootOccurrence ∧
      material.commonClearing.rootOccurrence =
        material.sourceActualService.paymentOccurrence.rootOccurrence := by
  let material :=
    sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
      sourceIndex
  have axes := contributionCapacityJointSettlement_jointRootAxes_exact
    oldVisit sourceIndex
  exact ⟨axes.1.trans axes.2.1.symm,
    axes.1.trans axes.2.2.symm⟩

/-- Sharing the numerical depth does not identify a joint-root material axis
with the exact occurrence of the later survivor root.  The standard disjoint
sum is used only as a negative readout of the two typed root origins; it is not
an occurrence carrier or registry. -/
theorem contributionCapacityJointSettlement_survivorOccurrence_ne_jointRootAxes
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let material :=
      sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
        sourceIndex
    (Sum.inl material.sourceEvent :
        ExactTemporalCausalRootEventAt
            (ContributionCapacityJointSettlementSurvivorRootAt oldVisit
              sourceIndex).toAuthoritativeRoot.toLedgerRoot
            (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
              sourceIndex) ⊕
          ExactTemporalCausalRootEventAt
            jointRoot.toAuthoritativeRoot.toLedgerRoot
            (temporalVisitAt
              (contributionCapacityJointSettlementDepthAt sourceIndex))) ≠
        Sum.inr material.commonClearing.rootOccurrence ∧
      (Sum.inl material.sourceEvent :
          ExactTemporalCausalRootEventAt
              (ContributionCapacityJointSettlementSurvivorRootAt oldVisit
                sourceIndex).toAuthoritativeRoot.toLedgerRoot
              (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
                sourceIndex) ⊕
            ExactTemporalCausalRootEventAt
              jointRoot.toAuthoritativeRoot.toLedgerRoot
              (temporalVisitAt
                (contributionCapacityJointSettlementDepthAt sourceIndex))) ≠
          Sum.inr material.clearingBackstop.rootOccurrence ∧
      (Sum.inl material.sourceEvent :
          ExactTemporalCausalRootEventAt
              (ContributionCapacityJointSettlementSurvivorRootAt oldVisit
                sourceIndex).toAuthoritativeRoot.toLedgerRoot
              (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
                sourceIndex) ⊕
            ExactTemporalCausalRootEventAt
              jointRoot.toAuthoritativeRoot.toLedgerRoot
              (temporalVisitAt
                (contributionCapacityJointSettlementDepthAt sourceIndex))) ≠
          Sum.inr
            material.sourceActualService.paymentOccurrence.rootOccurrence := by
  constructor
  · intro equality
    cases equality
  constructor
  · intro equality
    cases equality
  · intro equality
    cases equality

/-- The public material API has no partial-row input and no downstream
terminal or target output. -/
theorem contributionCapacityJointSettlement_material_negativeControls
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let material :=
    sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
      sourceIndex
  fail_if_success exact material.submittedEntry
  fail_if_success exact material.submittedConsumer
  fail_if_success exact material.TargetN
  fail_if_success exact material.targetSupport
  fail_if_success exact material.targetRoot
  fail_if_success exact material.terminal
  fail_if_success exact material.receipt
  fail_if_success exact material.patch
  fail_if_success exact material.branch
  fail_if_success exact material.future
  trivial

end
end M14SourceGeneratedContributionCapacityJointSettlementMaterial
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementMaterial.sourceGeneratedContributionCapacityJointSettlementMaterialAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementMaterial.contributionCapacityJointSettlement_jointRootAxes_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementMaterial.contributionCapacityJointSettlement_survivorOccurrence_ne_jointRootAxes
