import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation.SourceInstalledM14RefusalCultureFace
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Capture.StructuralRentCaptureRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Recognition.StructuralExploitationWitness
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Consumer.ProofCarryingPostSettlementObserverPaidSelfU8Recurrence

/-!
# Source-native M14 structural class/price coordinates

The refusal target is not relabelled as class or price.  Its actual paid
successor is consumed by the existing paid-self-U8 recurrence; that recurrence
regenerates the next external-Payment span and fixes the target periodic UBI
Payment.  Structural rent and the root-independent exploitation witness are
then read at that exact target depth.

The low-universe readouts contain no Payment, proof-carrying legislation,
whole ledger, quotient, factorization, or root next.  Those remain source
provenance.  In particular, this interface does not import or reuse the fixed
depth-zero structural-exploitation legislation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ClassPrice
namespace Interface

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Relationship Renewal UBI.Capture
open ProcessGame.Society.M8RelationshipMaintenanceFixture
open ProcessGame.Society.M8RelationshipMaintenanceRenewalRegression
open ProcessGame.Society.M3ExchangeSettlementPriceRegression
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14EssentialAccessRelationFixture
open ProcessGame.Society.M14UBIExitCapacityFixture
open ProcessGame.Society.M14UBIPeriodicRootHistory
open ProcessGame.Society.M14UBIPeriodicActualServiceCapacity
open ProcessGame.Society.M14StructuralRentCaptureRegression
open ProcessGame.Society.M14StructuralExploitationWitness
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open ProcessGame.Society.M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Transport
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation

noncomputable section

/-! ## Exact refusal-target Payment recurrence -/

def m14StructuralClassPriceClosedRecurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt oldVisit
    sourceIndex boundary

def m14StructuralClassPriceRecurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceClosedRecurrenceAt oldVisit sourceIndex boundary).2.1

def m14StructuralClassPricePaidRenewalAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceRecurrenceAt oldVisit sourceIndex boundary
    ).currentPaidRenewal

def m14StructuralClassPriceNextSpanAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceRecurrenceAt oldVisit sourceIndex boundary).nextSpan

def m14StructuralClassPriceDepthAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Nat :=
  (m14StructuralClassPricePaidRenewalAt oldVisit sourceIndex boundary
    ).targetAuthorityCurrent

def m14StructuralClassPriceTargetPaymentAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPricePaidRenewalAt oldVisit sourceIndex boundary
    ).targetConsequence.actualExit.paymentOccurrence

theorem m14StructuralClassPricePaidRenewal_eq_refusal
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14StructuralClassPricePaidRenewalAt oldVisit sourceIndex boundary =
      (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
        ).standingRenewal := by
  rfl

theorem m14StructuralClassPriceRefusalTarget_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14StructuralClassPricePaidRenewalAt oldVisit sourceIndex boundary
      ).targetOuterAuthority =
      m14RefusalOuterAuthorityRead
        (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary) := by
  rfl

@[simp] theorem m14StructuralClassPriceDepth_eq_nextRightCurrent
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary =
      rightCurrentAt oldVisit sourceIndex (boundary + 1) := by
  rfl

theorem m14StructuralClassPriceVisit_eq_nextRightVisit
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    temporalVisitAt
        (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary) =
      .finite (oldRootVisitAt oldVisit sourceIndex (boundary + 1)) := by
  rfl

theorem m14StructuralClassPriceTargetPayment_eq_nextSpanPayment
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary =
      targetPaymentOccurrence
        (m14StructuralClassPriceNextSpanAt oldVisit sourceIndex boundary) :=
  (m14StructuralClassPriceRecurrenceAt oldVisit sourceIndex boundary
    ).currentPaidTargetPayment_isNextSpanPayment

theorem m14StructuralClassPriceTargetPayment_eq_periodic
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary =
      periodicSourceBackedPaymentAt
        (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary) :=
  (m14StructuralClassPricePaidRenewalAt oldVisit sourceIndex boundary
    ).targetConsequence.actualExit.paymentOccurrence_eq

theorem m14StructuralClassPriceTargetPayment_installedExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary
      ).installed =
      installedUBIAt
        (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary) :=
  (m14StructuralClassPricePaidRenewalAt oldVisit sourceIndex boundary
    ).targetConsequence.actualExit.paymentInstalled_eq

theorem m14StructuralClassPriceTargetPayment_rootExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary
      ).rootOccurrence =
      (ProcessGame.Society.M9ProofCarryingRenewalInquiryRoot.jointRoot
        ).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          (temporalVisitAt
            (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary)) := by
  exact (m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary
    ).rootOccurrence_eq

/-! ## Actual structural-rent and exploitation sources -/

theorem m14StructuralClassPricePeriodicRentAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    PeriodicStructuralRentCaptureAt
      (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary)
      (periodicSourceBackedPaymentAt
        (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary)) :=
  periodicStructuralRentCaptureAt
    (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary)

theorem m14StructuralClassPriceRootFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (periodicSourceBackedPaymentAt
      (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary)
      ).installed.RootAnswerAndNextFactorizes :=
  (m14StructuralClassPricePeriodicRentAt oldVisit sourceIndex boundary
    ).periodicTenure.periodicCounterparty.periodicCapture.rootFactorization

def m14StructuralClassPriceExploitationWitnessAt
    (_oldVisit : OldVisit) (_sourceIndex _boundary : Nat) :
    SourceGeneratedStructuralExploitationWitnessAt relationshipRenewalSeed :=
  sourceGeneratedStructuralExploitationWitness

inductive SourceGeneratedM14StructuralClassPriceCoordinatesAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32
  | private generated

def sourceGeneratedM14StructuralClassPriceCoordinatesAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit sourceIndex
      boundary :=
  .generated

namespace SourceGeneratedM14StructuralClassPriceCoordinatesAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}

def refusalTransport
    (source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) :
    SourceGeneratedM14InstitutionalRefusalNextTransportAt oldVisit sourceIndex
      boundary := by
  cases source
  exact sourceGeneratedM14InstitutionalRefusalNextTransportAt oldVisit
    sourceIndex boundary

def recurrence
    (source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) := by
  cases source
  exact m14StructuralClassPriceRecurrenceAt oldVisit sourceIndex boundary

theorem targetOuterExact
    (_source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) : type_of%
    (m14StructuralClassPriceRefusalTarget_exact oldVisit sourceIndex boundary) :=
  m14StructuralClassPriceRefusalTarget_exact oldVisit sourceIndex boundary

theorem targetPaymentRecurs
    (_source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) : type_of%
    (m14StructuralClassPriceTargetPayment_eq_nextSpanPayment oldVisit
      sourceIndex boundary) :=
  m14StructuralClassPriceTargetPayment_eq_nextSpanPayment oldVisit sourceIndex
    boundary

theorem targetPaymentPeriodic
    (_source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) : type_of%
    (m14StructuralClassPriceTargetPayment_eq_periodic oldVisit sourceIndex
      boundary) :=
  m14StructuralClassPriceTargetPayment_eq_periodic oldVisit sourceIndex boundary

theorem targetPaymentInstalled
    (_source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) : type_of%
    (m14StructuralClassPriceTargetPayment_installedExact oldVisit sourceIndex
      boundary) :=
  m14StructuralClassPriceTargetPayment_installedExact oldVisit sourceIndex
    boundary

theorem targetPaymentRoot
    (_source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) : type_of%
    (m14StructuralClassPriceTargetPayment_rootExact oldVisit sourceIndex
      boundary) :=
  m14StructuralClassPriceTargetPayment_rootExact oldVisit sourceIndex boundary

theorem periodicRent
    (_source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) : PeriodicStructuralRentCaptureAt
    (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary)
    (periodicSourceBackedPaymentAt
      (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary)) :=
  m14StructuralClassPricePeriodicRentAt oldVisit sourceIndex boundary

def exploitationWitness
    (source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) :
    SourceGeneratedStructuralExploitationWitnessAt relationshipRenewalSeed := by
  cases source
  exact m14StructuralClassPriceExploitationWitnessAt oldVisit sourceIndex
    boundary

theorem refusalWholeLedger
    (_source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) : type_of%
    (m14RefusalCulturePayload_wholeLedger_exact oldVisit sourceIndex boundary) :=
  m14RefusalCulturePayload_wholeLedger_exact oldVisit sourceIndex boundary

theorem refusalGeneratedNext
    (_source : SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary) : type_of%
    (m14RefusalCulture_generatedNextCurrentAt_eq oldVisit sourceIndex boundary 1) :=
  m14RefusalCulture_generatedNextCurrentAt_eq oldVisit sourceIndex boundary 1

end SourceGeneratedM14StructuralClassPriceCoordinatesAt

/-! ## Independent Type-0 readouts -/

abbrev M14StructuralActor :=
  type_of% (renewalController (.a : RelationshipParty))

abbrev M14StructuralClassPriceActualCarrierAt
    (_oldVisit : OldVisit) (_sourceIndex _boundary : Nat) :=
  Lifecycle.TargetToken × M14StructuralActor

abbrev M14StructuralControllerOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence : M14StructuralClassPriceActualCarrierAt oldVisit sourceIndex
      boundary //
    occurrence =
      (relationshipRenewalFace.event,
        renewalController (.a : RelationshipParty)) ∧
      m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary =
        periodicSourceBackedPaymentAt
          (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary) }

abbrev M14StructuralAffectedOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence : M14StructuralClassPriceActualCarrierAt oldVisit sourceIndex
      boundary //
    occurrence =
      (relationshipRenewalFace.event,
        affectedCounterparty (.a : RelationshipParty)) ∧
      m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary =
        periodicSourceBackedPaymentAt
          (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary) }

abbrev M14StructuralClassPriceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M14StructuralControllerOccurrenceAt oldVisit sourceIndex boundary ⊕
    M14StructuralAffectedOccurrenceAt oldVisit sourceIndex boundary

def m14StructuralClassPriceSourceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary :=
  .inl ⟨(relationshipRenewalFace.event,
    renewalController (.a : RelationshipParty)), rfl,
    m14StructuralClassPriceTargetPayment_eq_periodic oldVisit sourceIndex
      boundary⟩

def m14StructuralClassPriceTargetOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary :=
  .inr ⟨(relationshipRenewalFace.event,
    affectedCounterparty (.a : RelationshipParty)), rfl,
    m14StructuralClassPriceTargetPayment_eq_periodic oldVisit sourceIndex
      boundary⟩

def m14StructuralClassPriceEventRead
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary →
      Lifecycle.TargetToken
  | .inl occurrence => occurrence.1.1
  | .inr occurrence => occurrence.1.1

def m14StructuralClassReadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary →
      M14StructuralActor
  | .inl occurrence => occurrence.1.2
  | .inr occurrence => occurrence.1.2

structure M14StructuralPriceReadout : Type where
  occurrenceCurrent : Nat
  actor : M14StructuralActor
  sector : EssentialAccessSector
  targetRole : EssentialAccessRole
  priceOpen : Bool
  captureActive : Bool
  sourceOwnedResidual : Bool
  rootFactorized : Bool
  isPaymentCounterparty : Bool

def m14StructuralPriceReadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex boundary →
      M14StructuralPriceReadout
  | .inl occurrence =>
      { occurrenceCurrent :=
          m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary
        actor := occurrence.1.2
        sector := .tenure
        targetRole := .tenureProvider
        priceOpen := true
        captureActive := true
        sourceOwnedResidual := true
        rootFactorized := true
        isPaymentCounterparty := false }
  | .inr occurrence =>
      { occurrenceCurrent :=
          m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary
        actor := occurrence.1.2
        sector := .tenure
        targetRole := .tenureProvider
        priceOpen := true
        captureActive := true
        sourceOwnedResidual := true
        rootFactorized := true
        isPaymentCounterparty := true }

def m14StructuralClassPriceReadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :
    M14StructuralActor × M14StructuralPriceReadout :=
  ⟨m14StructuralClassReadAt occurrence,
    m14StructuralPriceReadAt occurrence⟩

theorem m14StructuralClassPriceOccurrences_samePaymentAndEvent
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14StructuralClassPriceTargetPaymentAt oldVisit sourceIndex boundary =
        periodicSourceBackedPaymentAt
          (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary) ∧
      m14StructuralClassPriceEventRead
          (m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex
            boundary) =
        m14StructuralClassPriceEventRead
          (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
            boundary) :=
  ⟨m14StructuralClassPriceTargetPayment_eq_periodic oldVisit sourceIndex
      boundary,
    rfl⟩

theorem m14StructuralClassRead_sourceExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let sourceOccurrence :=
      m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex boundary
    let targetOccurrence :=
      m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex boundary
    let witness := m14StructuralClassPriceExploitationWitnessAt oldVisit
      sourceIndex boundary
    m14StructuralClassReadAt sourceOccurrence =
        renewalController (.a : RelationshipParty) ∧
      m14StructuralClassReadAt targetOccurrence =
        affectedCounterparty (.a : RelationshipParty) ∧
      m14StructuralClassReadAt sourceOccurrence ≠
        m14StructuralClassReadAt targetOccurrence ∧
      type_of% witness.exact_directions := by
  let witness := m14StructuralClassPriceExploitationWitnessAt oldVisit
    sourceIndex boundary
  exact ⟨rfl, rfl, witness.generatedActorsDistinct,
    witness.exact_directions⟩

theorem m14StructuralClassRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14StructuralClassReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary)) := by
  intro left right sameRead
  let witness := m14StructuralClassPriceExploitationWitnessAt oldVisit
    sourceIndex boundary
  cases left with
  | inl leftSource =>
      cases right with
      | inl rightSource =>
          apply congrArg Sum.inl
          apply Subtype.ext
          exact leftSource.property.1.trans rightSource.property.1.symm
      | inr rightTarget =>
          have leftActorExact := congrArg Prod.snd leftSource.property.1
          have rightActorExact := congrArg Prod.snd rightTarget.property.1
          exact (witness.generatedActorsDistinct
            (leftActorExact.symm.trans (sameRead.trans rightActorExact))).elim
  | inr leftTarget =>
      cases right with
      | inl rightSource =>
          have leftActorExact := congrArg Prod.snd leftTarget.property.1
          have rightActorExact := congrArg Prod.snd rightSource.property.1
          exact (witness.generatedActorsDistinct
            (rightActorExact.symm.trans
              (sameRead.symm.trans leftActorExact))).elim
      | inr rightTarget =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact leftTarget.property.1.trans rightTarget.property.1.symm

theorem m14StructuralPriceRead_sourceExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let sourceRead := m14StructuralPriceReadAt
      (m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex boundary)
    let targetRead := m14StructuralPriceReadAt
      (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex boundary)
    sourceRead.occurrenceCurrent =
        m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary ∧
      targetRead.occurrenceCurrent =
        m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary ∧
      sourceRead.actor = renewalController (.a : RelationshipParty) ∧
      targetRead.actor = affectedCounterparty (.a : RelationshipParty) ∧
      targetRead.actor = exactCounterpartyActor exactResidualActivation ∧
      sourceRead.actor ≠ exactCounterpartyActor exactResidualActivation ∧
      sourceRead.sector = .tenure ∧
      targetRead.targetRole = .tenureProvider ∧
      sourceRead.priceOpen = true ∧
      targetRead.captureActive = true ∧
      targetRead.sourceOwnedResidual = true ∧
      targetRead.rootFactorized = true ∧
      sourceRead.isPaymentCounterparty = false ∧
      targetRead.isPaymentCounterparty = true := by
  let witness := m14StructuralClassPriceExploitationWitnessAt oldVisit
    sourceIndex boundary
  have targetCounterparty :
      affectedCounterparty (.a : RelationshipParty) =
        exactCounterpartyActor exactResidualActivation :=
    witness.affectedActorIsTenureCounterparty.trans
      witness.tenureActorIsPaymentCounterparty
  have sourceNotCounterparty :
      renewalController (.a : RelationshipParty) ≠
        exactCounterpartyActor exactResidualActivation := by
    intro sameActor
    exact witness.generatedActorsDistinct
      (sameActor.trans targetCounterparty.symm)
  exact ⟨rfl, rfl, rfl, rfl, targetCounterparty,
    sourceNotCounterparty, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem m14StructuralClassPriceRead_hasActualDifference
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14StructuralClassReadAt
        (m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex
          boundary) ≠
      m14StructuralClassReadAt
        (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
          boundary) ∧
      m14StructuralPriceReadAt
          (m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex
            boundary) ≠
        m14StructuralPriceReadAt
          (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
            boundary) := by
  let witness := m14StructuralClassPriceExploitationWitnessAt oldVisit
    sourceIndex boundary
  constructor
  · exact witness.generatedActorsDistinct
  · intro samePrice
    exact witness.generatedActorsDistinct
      (congrArg M14StructuralPriceReadout.actor samePrice)

theorem sourceNativeM14StructuralClassPriceCoordinates_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let source := sourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
      sourceIndex boundary
    Nonempty (SourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
        sourceIndex boundary) ∧
      source.recurrence =
        m14StructuralClassPriceRecurrenceAt oldVisit sourceIndex boundary ∧
      type_of% (m14StructuralClassPriceRefusalTarget_exact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14StructuralClassPriceTargetPayment_eq_nextSpanPayment
        oldVisit sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceTargetPayment_eq_periodic oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceTargetPayment_installedExact oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceTargetPayment_rootExact oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPricePeriodicRentAt oldVisit sourceIndex
        boundary) ∧
      source.exploitationWitness =
        m14StructuralClassPriceExploitationWitnessAt oldVisit sourceIndex
          boundary ∧
      type_of% (structural_rent_payment_price_residual_next_commute
        (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary)) ∧
      type_of% ((source.exploitationWitness).exact_trace_provenance) ∧
      type_of% ((source.exploitationWitness).open_residual_destination) ∧
      type_of% (m14StructuralClassPriceOccurrences_samePaymentAndEvent oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassRead_injective oldVisit sourceIndex
        boundary) ∧
      type_of% (m14StructuralClassRead_sourceExact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14StructuralPriceRead_sourceExact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14StructuralClassPriceRead_hasActualDifference oldVisit
        sourceIndex boundary) ∧
      type_of% (m14RefusalCulturePayload_wholeLedger_exact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14RefusalCulture_generatedNextCurrentAt_eq oldVisit sourceIndex
        boundary 1) := by
  let source := sourceGeneratedM14StructuralClassPriceCoordinatesAt oldVisit
    sourceIndex boundary
  exact ⟨⟨source⟩, rfl, source.targetOuterExact,
    source.targetPaymentRecurs, source.targetPaymentPeriodic,
    source.targetPaymentInstalled, source.targetPaymentRoot,
    source.periodicRent, rfl,
    structural_rent_payment_price_residual_next_commute
      (m14StructuralClassPriceDepthAt oldVisit sourceIndex boundary),
    source.exploitationWitness.exact_trace_provenance,
    source.exploitationWitness.open_residual_destination,
    m14StructuralClassPriceOccurrences_samePaymentAndEvent oldVisit
      sourceIndex boundary,
    m14StructuralClassRead_injective oldVisit sourceIndex boundary,
    m14StructuralClassRead_sourceExact oldVisit sourceIndex boundary,
    m14StructuralPriceRead_sourceExact oldVisit sourceIndex boundary,
    m14StructuralClassPriceRead_hasActualDifference oldVisit sourceIndex
      boundary,
    source.refusalWholeLedger, source.refusalGeneratedNext⟩

end
end Interface
end ClassPrice
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface.m14StructuralClassPriceTargetPayment_eq_periodic
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface.m14StructuralClassPriceOccurrences_samePaymentAndEvent
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface.m14StructuralClassRead_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface.m14StructuralClassRead_sourceExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface.m14StructuralPriceRead_sourceExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface.sourceNativeM14StructuralClassPriceCoordinates_directConsumer
