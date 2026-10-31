import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Gate.Producer.SourceGeneratedContributionCapacityJointSettlementGateFrontier
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Payment.Action.Producer.SourceGeneratedContributionCapacityJointSettlementCrossRootPayment

/-!
# Paid contribution-capacity death field

The current-twelve survivor occurrence already owns the finite death-field
demand in its pre-emitter projection inventory.  The exact joint-settlement
action Payment at that same occurrence consumes the demand and generates the
`Bool true` terminal current.  The existing complete gate frontier proves that
the generated two-section field has no substantive death at section zero and
has substantive death at section one.

The local first locus is therefore generated, not supplied.  Its `Nat` value
is only an observer chart.  The Payment stores neither that value nor its
target; `NextPaidBy` remains the dependent projection of existing action
authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPaidDeathField

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRoot
open M14SourceGeneratedContributionCapacityJointSettlementGateFrontier
open M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment
open M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment.SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
open M14SourceGeneratedContributionCapacityDeathFieldDemand
open M14SourceGeneratedContributionCapacityDeathFieldDemand.SourceGeneratedContributionCapacityDeathFieldDemandAt
open M14UBIPeriodicActualServiceCapacity

/-! ## Installed source demand -/

def contributionCapacityJointSettlementDeathFieldFaceAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex)
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
        sourceIndex) :=
  contributionCapacitySettlementSurvivorDeathFieldFaceAt oldVisit sourceIndex
    (CanonicalContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)

def contributionCapacityJointSettlementDeathFieldDemandAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  (contributionCapacityJointSettlementDeathFieldFaceAt oldVisit sourceIndex
    ).rootRead

def contributionCapacityJointSettlementDeathFieldRootEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ExactTemporalCausalRootEventAt
      (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit
        sourceIndex) :=
  (ContributionCapacityJointSettlementSurvivorRootAt oldVisit sourceIndex
    ).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (contributionCapacityJointSettlementSurvivorVisitAt oldVisit sourceIndex)

@[simp] theorem contributionCapacityJointSettlementDeathFieldRootEvent_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    contributionCapacityJointSettlementDeathFieldRootEventAt oldVisit
        sourceIndex =
      ContributionCapacityJointSettlementPaidSourceEventAt oldVisit
        sourceIndex :=
  rfl

@[simp] theorem contributionCapacityJointSettlementDeathField_sourceRead
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityJointSettlementDeathFieldDemandAt oldVisit sourceIndex
      ).finiteSection ⟨0, by decide⟩ = false :=
  sourceRead_eq_false _

@[simp] theorem contributionCapacityJointSettlementDeathField_targetRead
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityJointSettlementDeathFieldDemandAt oldVisit sourceIndex
      ).finiteSection ⟨1, by decide⟩ = true :=
  targetRead_eq_true _

/-! ## Complete current-relative death frontier -/

abbrev ContributionCapacityJointSettlementDeathAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Fin 2 → Type
  | ⟨0, _⟩ =>
      (contributionCapacityJointSettlementInitialFrontierAt oldVisit
        sourceIndex).SubstantiveDeathAt
  | ⟨1, _⟩ =>
      (contributionCapacityJointSettlementTerminalFrontierAt oldVisit
        sourceIndex).SubstantiveDeathAt

theorem contributionCapacityJointSettlementInitialSubstantiveDeath_isEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    IsEmpty
      (contributionCapacityJointSettlementInitialFrontierAt oldVisit
        sourceIndex).SubstantiveDeathAt := by
  constructor
  rintro ⟨entry, death⟩
  let entryIndex :=
    (contributionCapacityJointSettlementLiveEntryEquiv oldVisit).symm entry
  have entry_eq :
      contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex =
        entry :=
    (contributionCapacityJointSettlementLiveEntryEquiv oldVisit
      ).apply_symm_apply entry
  rw [← entry_eq] at death
  exact
    (contributionCapacityJointSettlementInitialDeath_isEmpty oldVisit
      sourceIndex entryIndex).false death

theorem contributionCapacityJointSettlementDeathAt_zero_isEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    IsEmpty
      (ContributionCapacityJointSettlementDeathAt oldVisit sourceIndex
        (0 : Fin 2)) :=
  contributionCapacityJointSettlementInitialSubstantiveDeath_isEmpty
    oldVisit sourceIndex

theorem contributionCapacityJointSettlementDeathAt_one_nonempty
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Nonempty
      (ContributionCapacityJointSettlementDeathAt oldVisit sourceIndex
        (1 : Fin 2)) :=
  contributionCapacityJointSettlementTerminalDeath_substantive oldVisit
    sourceIndex

/-- Zero-choice local first locus of the generated two-section field. -/
structure SourceGeneratedContributionCapacityMinimalDeathLocusAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type where
  private mk ::

def sourceGeneratedContributionCapacityMinimalDeathLocusAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedContributionCapacityMinimalDeathLocusAt oldVisit
      sourceIndex :=
  ⟨⟩

namespace SourceGeneratedContributionCapacityMinimalDeathLocusAt

variable {oldVisit : OldVisit} {sourceIndex : Nat}

def locus
    (_minimal : SourceGeneratedContributionCapacityMinimalDeathLocusAt
      oldVisit sourceIndex) : Fin 2 :=
  1

theorem before_isEmpty
    (_minimal : SourceGeneratedContributionCapacityMinimalDeathLocusAt
      oldVisit sourceIndex) :
    IsEmpty
      (ContributionCapacityJointSettlementDeathAt oldVisit sourceIndex
        (0 : Fin 2)) :=
  contributionCapacityJointSettlementDeathAt_zero_isEmpty oldVisit sourceIndex

theorem atLocus_nonempty
    (minimal : SourceGeneratedContributionCapacityMinimalDeathLocusAt
      oldVisit sourceIndex) :
    Nonempty
      (ContributionCapacityJointSettlementDeathAt oldVisit sourceIndex
        minimal.locus) :=
  contributionCapacityJointSettlementDeathAt_one_nonempty oldVisit sourceIndex

/-- Calendar value is only the finite-chart readout. -/
def observerTimeChart
    (minimal : SourceGeneratedContributionCapacityMinimalDeathLocusAt
      oldVisit sourceIndex) : Nat :=
  minimal.locus.val

@[simp] theorem observerTimeChart_eq_one
    (minimal : SourceGeneratedContributionCapacityMinimalDeathLocusAt
      oldVisit sourceIndex) :
    minimal.observerTimeChart = 1 :=
  rfl

theorem observerTimeChart_matches_generatedFold
    (minimal : SourceGeneratedContributionCapacityMinimalDeathLocusAt
      oldVisit sourceIndex) :
    some minimal.observerTimeChart = contributionCapacityDeathLocusReadout :=
  rfl

end SourceGeneratedContributionCapacityMinimalDeathLocusAt

/-! ## Same-occurrence sealed pre-locus/publication Payment -/

/-- The installed demand and rich action Payment are forced to share the
exact current-twelve occurrence.  There is no caller result, locus or next. -/
structure ExactContributionCapacityPreLocusPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 23 where
  private mk ::
  demand : SourceGeneratedContributionCapacityDeathFieldDemandAt oldVisit
    sourceIndex
    (CanonicalContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
      ).occurrence
  actionPayment :
    CanonicalContributionCapacityJointSettlementCrossRootPaymentAt oldVisit
      sourceIndex
  sourceMaterial :
    SourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
      sourceIndex
  sourceActualExit : PeriodicActualServiceExitAt
    (contributionCapacityJointSettlementDepthAt sourceIndex)
  demandExact : demand =
    contributionCapacityJointSettlementDeathFieldDemandAt oldVisit sourceIndex
  actionPaymentExact : actionPayment =
    sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
      oldVisit sourceIndex
  sourceMaterialExact : sourceMaterial =
    ContributionCapacityJointSettlementPaidMaterialAt oldVisit sourceIndex
  sourceActualExitExact : sourceActualExit =
    contributionCapacityJointSettlementSourceActualExitAt oldVisit sourceIndex
  sourceRootEventExact :
    contributionCapacityJointSettlementDeathFieldRootEventAt oldVisit
        sourceIndex =
      ContributionCapacityJointSettlementPaidSourceEventAt oldVisit
        sourceIndex
  demandActualServiceExact : demand.actualService = actionPayment.sourcePayment.down
  everySourceRowEvolved : ∀ entryIndex : Fin 2,
    (ContributionCapacityJointSettlementPaidSourceEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex) =
      .evolved
        (contributionCapacityJointSettlementSourceRowEvolutionAt oldVisit
          sourceIndex entryIndex)

def exactContributionCapacityPreLocusPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ExactContributionCapacityPreLocusPaymentAt oldVisit sourceIndex :=
  let demand :=
    contributionCapacityJointSettlementDeathFieldDemandAt oldVisit sourceIndex
  let payment :=
    sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
      oldVisit sourceIndex
  { demand := demand
    actionPayment := payment
    sourceMaterial :=
      sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
        sourceIndex
    sourceActualExit :=
      contributionCapacityJointSettlementSourceActualExitAt oldVisit
        sourceIndex
    demandExact := rfl
    actionPaymentExact := rfl
    sourceMaterialExact := rfl
    sourceActualExitExact := rfl
    sourceRootEventExact := rfl
    demandActualServiceExact := Subsingleton.elim _ _
    everySourceRowEvolved := payment.everySourceRowEvolved }

/-- Publication is not a second Payment species.  It is the same sealed
pre-locus Payment viewed through its installed source demand. -/
abbrev ExactContributionCapacityPublicationPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ExactContributionCapacityPreLocusPaymentAt oldVisit sourceIndex

namespace ExactContributionCapacityPreLocusPaymentAt

variable {oldVisit : OldVisit} {sourceIndex : Nat}

def readBy
    (_payment : ExactContributionCapacityPreLocusPaymentAt oldVisit
      sourceIndex) : Nat :=
  1

def nextPaidBy
    (payment : ExactContributionCapacityPreLocusPaymentAt oldVisit
      sourceIndex) :=
  payment.actionPayment.nextPaidBy

def targetDeathLocus
    (_payment : ExactContributionCapacityPreLocusPaymentAt oldVisit
      sourceIndex) : Nat :=
  0

@[simp] theorem readBy_eq_one
    (payment : ExactContributionCapacityPreLocusPaymentAt oldVisit
      sourceIndex) : payment.readBy = 1 :=
  rfl

@[simp] theorem targetDeathLocus_eq_zero
    (payment : ExactContributionCapacityPreLocusPaymentAt oldVisit
      sourceIndex) : payment.targetDeathLocus = 0 :=
  rfl

theorem nextPaidBy_isTerminalCurrent
    (payment : ExactContributionCapacityPreLocusPaymentAt oldVisit
      sourceIndex) :
    payment.nextPaidBy =
      ⟨(generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex).target.TargetV,
        (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex).target.targetRoot.toAuthoritativeRoot,
        (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex).target.targetVisit⟩ := by
  rw [nextPaidBy, payment.actionPaymentExact]
  exact
    (sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
      oldVisit sourceIndex).nextPaidBy_exact

/-- Proof terms cannot hide a different actual action or next. -/
theorem actionPayment_proofIndependent
    (left right : ExactContributionCapacityPreLocusPaymentAt oldVisit
      sourceIndex) :
    left.actionPayment = right.actionPayment :=
  left.actionPaymentExact.trans right.actionPaymentExact.symm

theorem nextPaidBy_proofIndependent
    (left right : ExactContributionCapacityPreLocusPaymentAt oldVisit
      sourceIndex) :
    left.nextPaidBy = right.nextPaidBy := by
  unfold nextPaidBy
  rw [left.actionPayment_proofIndependent right]

end ExactContributionCapacityPreLocusPaymentAt

/-- Generated pre-locus nexts have no other mouth than the sealed Payment. -/
abbrev GeneratedContributionCapacityPreLocusNextAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  Sigma fun payment : ExactContributionCapacityPreLocusPaymentAt oldVisit
      sourceIndex =>
    { next // next = payment.nextPaidBy }

def generatedContributionCapacityPreLocusNextAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    GeneratedContributionCapacityPreLocusNextAt oldVisit sourceIndex :=
  let payment := exactContributionCapacityPreLocusPaymentAt oldVisit sourceIndex
  ⟨payment, ⟨payment.nextPaidBy, rfl⟩⟩

theorem generatedPreLocusNext_isEmpty_of_payment_isEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (empty : IsEmpty
      (ExactContributionCapacityPreLocusPaymentAt oldVisit sourceIndex)) :
    IsEmpty (GeneratedContributionCapacityPreLocusNextAt oldVisit
      sourceIndex) :=
  ⟨fun next => empty.false next.1⟩

theorem paidDeathField_hasNoCallerDateTargetOrFuture
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let payment := exactContributionCapacityPreLocusPaymentAt oldVisit sourceIndex
  fail_if_success exact payment.date
  fail_if_success exact payment.locus
  fail_if_success exact payment.target
  fail_if_success exact payment.fixedPoint
  fail_if_success exact payment.history
  fail_if_success exact payment.registry
  fail_if_success exact payment.future
  trivial

end
end M14SourceGeneratedContributionCapacityPaidDeathField
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPaidDeathField.contributionCapacityJointSettlementInitialSubstantiveDeath_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPaidDeathField.exactContributionCapacityPreLocusPaymentAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPaidDeathField.generatedPreLocusNext_isEmpty_of_payment_isEmpty
