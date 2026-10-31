import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Clearing.SourceCommonClearingRenewal
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.ExchangeSettlementPriceRegression

/-!
# M14 clearing-consumer death

The existing partial settlement occurrence has already fulfilled leg `a`
while its generated counterparty leg `b` remains open.  That open `b` slot
has not realized a fulfillment consumer at the same occurrence.  This is the
first clearing-consumer death: one side survived an actual settlement action,
the other side retains an exact admitted residual but has not activated its
exact clearing consumer in the current occurrence.

The carrier is indexed by the existing `partialOpenB`.  It creates no death
enum, side selector, participant registry, backstop, coverage table, second
settlement occurrence, run, ledger, or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ClearingConsumerDeath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Renewal Clearing
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M4AutomaticFullFulfillmentRegression
open M14SourceCommonClearingRenewal

/-! ## Exact existing one-sided source -/

def canonicalAClearingFace :
    SourceGeneratedSymmetricClearingAt fulfillmentAuthority
      exactExchangeSeed .a :=
  SourceGeneratedSymmetricClearingAt.generate fulfillmentAuthority
    exactExchangeSeed .a

@[simp] theorem canonicalA_counterparty_is_B :
    canonicalAClearingFace.counterpartyLeg = .b :=
  rfl

/-- The C1 one-sided action is literally the already existing first edge of
the partial settlement occurrence. -/
@[simp] theorem canonicalA_oneSidedEdge_eq_fulfillA :
    canonicalAClearingFace.oneSidedEdge = fulfillA :=
  rfl

/-- The old residual-consumer compiler is singleton and points only to open
leg `a`; it cannot select the missing counterparty `b`. -/
theorem residualCompiler_cannot_select_B :
    ¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
      (activation.openSettlement residualConsumerCompiler).leg = .b := by
  rintro ⟨activation, equality⟩
  cases activation.1
  cases equality

/-- The same singleton compiler is tied to `openOccurrence`; it cannot be
retyped as an activation of `partialOccurrence`. -/
theorem residualCompiler_cannot_point_to_partialOccurrence :
    ¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
      activation.occurrence residualConsumerCompiler = partialOccurrence := by
  rintro ⟨activation, equality⟩
  cases activation.1
  have seedEquality := congrArg
    (fun occurrence : settlementCompiler.GeneratedSettlementOccurrence =>
      occurrence.1.1) equality
  cases seedEquality

theorem residualCompiler_is_exactly_openA
    (activation : residualConsumerCompiler.ExactActivationSeed) :
    activation.occurrence residualConsumerCompiler = openOccurrence ∧
      (activation.openSettlement residualConsumerCompiler).leg = .a :=
  ⟨rfl, rfl⟩

/-- Partial and automatic settlement currents are genuinely different.  If
they were equal, the live `b` slot would construct an open settlement inside
the fully fulfilled automatic target. -/
theorem partial_current_ne_automatic_current :
    partialOccurrence.current settlementCompiler ≠
      automaticOccurrence.current automaticCompiler := by
  intro currentEquality
  have slotsEquality :
      (partialOccurrence.current settlementCompiler).slots =
        (automaticOccurrence.current automaticCompiler).slots :=
    congrArg (fun state : ResponsibilityState V => state.slots)
      currentEquality
  have slotIndexEquality :
      partialOccurrence.slotIndex settlementCompiler partialOpenB.leg =
        automaticOccurrence.slotIndex automaticCompiler (.b : Leg) :=
    rfl
  have partialGet? :
      (partialOccurrence.current settlementCompiler).slots[
          partialOccurrence.slotIndex settlementCompiler partialOpenB.leg]? =
        some (.live
          (exactExchangeSeed.obligation exchangeCompiler .b)) := by
    have partialPresent := partialOpenB.present
    have indexLt :=
      (partialOccurrence.slot settlementCompiler partialOpenB.leg).isLt
    have slotValueExact :
        (partialOccurrence.slot settlementCompiler partialOpenB.leg).val =
          partialOccurrence.slotIndex settlementCompiler partialOpenB.leg :=
      rfl
    rw [← slotValueExact]
    rw [List.getElem?_eq_getElem indexLt]
    exact congrArg some partialPresent
  have automaticGet? :
      (automaticOccurrence.current automaticCompiler).slots[
          automaticOccurrence.slotIndex automaticCompiler (.b : Leg)]? =
        some (.live
          (exactExchangeSeed.obligation exchangeCompiler .b)) := by
    rw [← slotIndexEquality, ← slotsEquality]
    exact partialGet?
  apply automaticFullyFulfilled.openSettlement_isEmpty.false
  refine
    { leg := .b
      obligation := exactExchangeSeed.obligation exchangeCompiler .b
      present := ?_ }
  have indexLt :=
    (automaticOccurrence.slot automaticCompiler (.b : Leg)).isLt
  have slotValueExact :
      (automaticOccurrence.slot automaticCompiler (.b : Leg)).val =
        automaticOccurrence.slotIndex automaticCompiler (.b : Leg) :=
    rfl
  rw [← slotValueExact] at automaticGet?
  rw [List.getElem?_eq_getElem indexLt] at automaticGet?
  exact Option.some.inj automaticGet?

theorem partial_generatedState_ne_automatic_generatedState :
    partialOccurrence.generatedState settlementCompiler ≠
      automaticOccurrence.generatedState automaticCompiler := by
  intro equality
  exact partial_current_ne_automatic_current
    (congrArg (fun generated : P.GeneratedState => generated.current)
      equality)

/-! ## Source-generated death carrier -/

structure SourceGeneratedClearingConsumerDeathAt
    (missing : OpenSettlementAt settlementCompiler partialOccurrence) :
    Type 3 where
  private mk ::
  missingExact : missing = partialOpenB
  missingLegExact : missing.leg = .b
  missingCounterpartyExact :
    exactExchangeSeed.counterparty exchangeCompiler missing.leg = .a
  survivingFulfilledA :
    FulfilledExchangeLegAt settlementCompiler partialOccurrence .a
  survivingFulfilledAExact : survivingFulfilledA = partialFulfilledA
  survivorBoundaryOwnership : SourceOwnsResponsibilityIncidence V
    (P.boundarySource canonicalAClearingFace.legConsumer.event)
    (exactExchangeSeed.obligation exchangeCompiler .a)
  missingBoundaryConsumer :
    ExactLegFulfillmentAt (exchangeLaw := exchangeLaw)
      exactExchangeSeed (.b : Leg)
  missingBoundaryConsumerExact : missingBoundaryConsumer =
    canonicalAClearingFace.counterpartyConsumer
  missingBoundaryOwnership : SourceOwnsResponsibilityIncidence V
    (P.boundarySource canonicalAClearingFace.counterpartyConsumer.event)
    (exactExchangeSeed.obligation exchangeCompiler .b)
  missingBoundaryEdgeExact :
    partialOpenB.consumerEdge
      canonicalAClearingFace.counterpartyConsumer.event = fulfillB
  missingAdmissionOwnership : SourceOwnsResponsibilityIncidence V
    (exactExchangeSeed.sourceEvent exchangeCompiler .b)
    (exactExchangeSeed.obligation exchangeCompiler .b)
  actorsDistinct :
    exactExchangeSeed.actor exchangeCompiler .b ≠
      exactExchangeSeed.actor exchangeCompiler .a
  slotsDistinct :
    exactExchangeSeed.obligationSlotIndex exchangeCompiler .b ≠
      exactExchangeSeed.obligationSlotIndex exchangeCompiler .a
  missingFulfillmentEmpty :
    IsEmpty (FulfilledExchangeLegAt settlementCompiler partialOccurrence
      missing.leg)
  residualCannotSelectMissing :
    ¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
      (activation.openSettlement residualConsumerCompiler).leg = .b
  residualCannotPointPartial :
    ¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
      activation.occurrence residualConsumerCompiler = partialOccurrence
  residualCompilerExact : ∀ activation :
      residualConsumerCompiler.ExactActivationSeed,
    activation.occurrence residualConsumerCompiler = openOccurrence ∧
      (activation.openSettlement residualConsumerCompiler).leg = .a
  canonicalOneSidedActionExact :
    canonicalAClearingFace.oneSidedEdge = fulfillA
  partialCurrentDistinctFromAutomatic :
    partialOccurrence.current settlementCompiler ≠
      automaticOccurrence.current automaticCompiler
  partialGeneratedStateDistinctFromAutomatic :
    partialOccurrence.generatedState settlementCompiler ≠
      automaticOccurrence.generatedState automaticCompiler
  automaticTargetClosed :
    IsEmpty (OpenSettlementAt automaticCompiler automaticOccurrence)
  nilTargetOpen : Nonempty
    (OpenSettlementAt nilOpenCompiler nilOpenOccurrence)
  nilTargetAFulfillmentEmpty :
    IsEmpty (FulfilledExchangeLegAt nilOpenCompiler nilOpenOccurrence
      nilOpenA.leg)
  nilTargetNotFullyFulfilled :
    ¬ Nonempty (FullyFulfilledExchangeAt nilOpenCompiler nilOpenOccurrence)

/-! ## Raw adapter exists; source provenance does not -/

/-- The installed process grammar can form the exact B adapter from C1's
boundary event.  This is deliberately public: the death is not raw event or
edge absence. -/
def rawBackstopAdapter :
    OpenSettlementAt.ActivatedResidualConsumerAt partialOpenB where
  activation := canonicalAClearingFace.counterpartyConsumer.event

@[simp] theorem rawBackstopAdapter_edge_eq_fulfillB :
    rawBackstopAdapter.edge = fulfillB :=
  rfl

/-- The raw adapter has the right process effect and source ownership.  What
is still absent is an exact source seed in the current residual compiler that
generates this adapter at `partialOccurrence`. -/
theorem rawBackstopAdapter_generates_exact_next :
    rawBackstopAdapter.edge.target.history =
        (partialOccurrence.current settlementCompiler).history ++
          [rawBackstopAdapter.edge.lifecycleEvent] ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource rawBackstopAdapter.activation)
        partialOpenB.obligation) :=
  ⟨rawBackstopAdapter.history_append,
    ⟨rawBackstopAdapter.sourceOwnership⟩⟩

/-- Unique producer.  Every witness is reread from the existing partial,
automatic, nil, and C1 source objects; the mouth has no arguments. -/
def sourceGeneratedClearingConsumerDeath :
    SourceGeneratedClearingConsumerDeathAt partialOpenB where
  missingExact := rfl
  missingLegExact := rfl
  missingCounterpartyExact := rfl
  survivingFulfilledA := partialFulfilledA
  survivingFulfilledAExact := rfl
  survivorBoundaryOwnership := canonicalAClearingFace.legSourceOwnership
  missingBoundaryConsumer := canonicalAClearingFace.counterpartyConsumer
  missingBoundaryConsumerExact := rfl
  missingBoundaryOwnership :=
    canonicalAClearingFace.counterpartySourceOwnership
  missingBoundaryEdgeExact := rfl
  missingAdmissionOwnership :=
    exactExchangeSeed.admissionOwnership exchangeCompiler .b
  actorsDistinct :=
    SourceOwnedExchangeLaw.counterparty_actors_distinct exchangeLaw
      exactExchangeSeed .b
  slotsDistinct :=
    (SourceOwnedExchangeCompiler.ExactExchangeSeed.counterparty_slot_ne
      exchangeCompiler exactExchangeSeed .b).symm
  missingFulfillmentEmpty := partialOpenB.fulfilledLeg_isEmpty
  residualCannotSelectMissing := residualCompiler_cannot_select_B
  residualCannotPointPartial :=
    residualCompiler_cannot_point_to_partialOccurrence
  residualCompilerExact := residualCompiler_is_exactly_openA
  canonicalOneSidedActionExact := canonicalA_oneSidedEdge_eq_fulfillA
  partialCurrentDistinctFromAutomatic :=
    partial_current_ne_automatic_current
  partialGeneratedStateDistinctFromAutomatic :=
    partial_generatedState_ne_automatic_generatedState
  automaticTargetClosed :=
    automaticFullyFulfilled.openSettlement_isEmpty
  nilTargetOpen := ⟨nilOpenA⟩
  nilTargetAFulfillmentEmpty := nilOpenA.fulfilledLeg_isEmpty
  nilTargetNotFullyFulfilled :=
    nil_open_occurrence_has_no_fully_fulfilled_witness

theorem clearingConsumerDeath_exact :
    partialOpenB.leg = .b ∧
      exactExchangeSeed.counterparty exchangeCompiler
          partialOpenB.leg = .a ∧
      Nonempty (FulfilledExchangeLegAt settlementCompiler
        partialOccurrence .a) ∧
      Nonempty (ExactLegFulfillmentAt (exchangeLaw := exchangeLaw)
        exactExchangeSeed (.b : Leg)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          canonicalAClearingFace.counterpartyConsumer.event)
        (exactExchangeSeed.obligation exchangeCompiler .b)) ∧
      partialOpenB.consumerEdge
          canonicalAClearingFace.counterpartyConsumer.event = fulfillB ∧
      IsEmpty (FulfilledExchangeLegAt settlementCompiler
        partialOccurrence partialOpenB.leg) ∧
      partialOccurrence.current settlementCompiler ≠
        automaticOccurrence.current automaticCompiler ∧
      partialOccurrence.generatedState settlementCompiler ≠
        automaticOccurrence.generatedState automaticCompiler ∧
      IsEmpty (OpenSettlementAt automaticCompiler automaticOccurrence) ∧
      Nonempty (OpenSettlementAt nilOpenCompiler nilOpenOccurrence) ∧
      IsEmpty (FulfilledExchangeLegAt nilOpenCompiler nilOpenOccurrence
        nilOpenA.leg) ∧
      ¬ Nonempty
        (FullyFulfilledExchangeAt nilOpenCompiler nilOpenOccurrence) :=
  ⟨rfl,
    sourceGeneratedClearingConsumerDeath.missingCounterpartyExact,
    ⟨sourceGeneratedClearingConsumerDeath.survivingFulfilledA⟩,
    ⟨sourceGeneratedClearingConsumerDeath.missingBoundaryConsumer⟩,
    ⟨sourceGeneratedClearingConsumerDeath.missingBoundaryOwnership⟩,
    sourceGeneratedClearingConsumerDeath.missingBoundaryEdgeExact,
    sourceGeneratedClearingConsumerDeath.missingFulfillmentEmpty,
    sourceGeneratedClearingConsumerDeath.partialCurrentDistinctFromAutomatic,
    sourceGeneratedClearingConsumerDeath
      |>.partialGeneratedStateDistinctFromAutomatic,
    sourceGeneratedClearingConsumerDeath.automaticTargetClosed,
    sourceGeneratedClearingConsumerDeath.nilTargetOpen,
    sourceGeneratedClearingConsumerDeath.nilTargetAFulfillmentEmpty,
    sourceGeneratedClearingConsumerDeath.nilTargetNotFullyFulfilled⟩

theorem clearingConsumerDeath_mouth_has_no_backstop_enum_selector_or_run :
    True := by
  let death := sourceGeneratedClearingConsumerDeath
  fail_if_success exact death.backstop
  fail_if_success exact death.deathKind
  fail_if_success exact death.sideSelector
  fail_if_success exact death.coverage
  fail_if_success exact death.secondOccurrence
  fail_if_success exact death.run
  fail_if_success exact death.completedFuture
  trivial

end
end M14ClearingConsumerDeath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ClearingConsumerDeath.residualCompiler_cannot_select_B
#print axioms SaturationMonoid.ProcessGame.Society.M14ClearingConsumerDeath.residualCompiler_cannot_point_to_partialOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14ClearingConsumerDeath.partial_current_ne_automatic_current
#print axioms SaturationMonoid.ProcessGame.Society.M14ClearingConsumerDeath.rawBackstopAdapter_edge_eq_fulfillB
#print axioms SaturationMonoid.ProcessGame.Society.M14ClearingConsumerDeath.rawBackstopAdapter_generates_exact_next
#print axioms SaturationMonoid.ProcessGame.Society.M14ClearingConsumerDeath.sourceGeneratedClearingConsumerDeath
#print axioms SaturationMonoid.ProcessGame.Society.M14ClearingConsumerDeath.clearingConsumerDeath_exact
