import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Clearing.Death.ClearingConsumerDeath
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Clearing.PeriodicCommonClearingRenewal

/-!
# M14 proof-carrying clearing-consumer death

The death is not absence of a global fulfillment authority.  The existing C1
counterparty consumer and boundary ownership remain available.  What failed
is occurrence-indexed realization: at `partialOccurrence`, leg `a` is already
fulfilled, leg `b` is still live, and the current singleton activation
compiler can select neither that leg nor that occurrence.

The raw B adapter and exact edge are constructible from the existing process
grammar.  The remaining responsibility is stricter: generate that adapter
from an exact source-owned activation seed at `partialOccurrence`.  The direct
sink pairs this provenance gap with every periodic mandate/root visit without
claiming that the death has already been installed as a dependent root face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingClearingConsumerDeathRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Renewal Clearing
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M4AutomaticFullFulfillmentRegression
open M9ProofCarryingRenewalInquiryRoot
open M14SourceCommonClearingRenewal
open M14UBIPeriodicRootHistory
open M14PeriodicCommonClearingRenewal
open M14ClearingConsumerDeath

theorem deathRetainsBoundaryAuthorityButLacksCurrentRealization :
    Nonempty (ExactLegFulfillmentAt (exchangeLaw := exchangeLaw)
        exactExchangeSeed (.b : Leg)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          canonicalAClearingFace.counterpartyConsumer.event)
        (exactExchangeSeed.obligation exchangeCompiler .b)) ∧
      partialOpenB.consumerEdge
          canonicalAClearingFace.counterpartyConsumer.event = fulfillB ∧
      IsEmpty (FulfilledExchangeLegAt settlementCompiler
        partialOccurrence partialOpenB.leg) :=
  ⟨⟨sourceGeneratedClearingConsumerDeath.missingBoundaryConsumer⟩,
    ⟨sourceGeneratedClearingConsumerDeath.missingBoundaryOwnership⟩,
    sourceGeneratedClearingConsumerDeath.missingBoundaryEdgeExact,
    sourceGeneratedClearingConsumerDeath.missingFulfillmentEmpty⟩

theorem rawBackstopAdapterExistsButLacksCurrentSourceProvenance :
    Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt partialOpenB) ∧
      rawBackstopAdapter.edge = fulfillB ∧
      rawBackstopAdapter.edge.target.history =
        (partialOccurrence.current settlementCompiler).history ++
          [rawBackstopAdapter.edge.lifecycleEvent] ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource rawBackstopAdapter.activation)
        partialOpenB.obligation) :=
  ⟨⟨rawBackstopAdapter⟩,
    rawBackstopAdapter_edge_eq_fulfillB,
    rawBackstopAdapter_generates_exact_next⟩

theorem currentCompilerCannotDischargeBackstopResponsibility :
    (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
      (activation.openSettlement residualConsumerCompiler).leg = .b) ∧
      (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        activation.occurrence residualConsumerCompiler = partialOccurrence) :=
  ⟨sourceGeneratedClearingConsumerDeath.residualCannotSelectMissing,
    sourceGeneratedClearingConsumerDeath.residualCannotPointPartial⟩

theorem clearingDeathPairedWithEveryPeriodicRootVisit
    (depth : Nat) :
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    Nonempty (SourceGeneratedClearingConsumerDeathAt partialOpenB) ∧
      clearing.installed.payload.sourceSeed = commonClearingSeed ∧
      clearing.installed.payload.disposition.fullResult =
        AutomaticFullFulfillment.fullResult fulfillmentAuthority
          exactExchangeSeed ∧
      clearing.rootOccurrence =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth)) ∧
      Nonempty (RenewalResponsibilityConsumerAt
        clearing.mandate.installed.operationalAuthority) ∧
      clearing.appliedReform.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      clearing.appliedReform.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      canonicalAClearingFace.oneSidedEdge = fulfillA ∧
      partialOpenB.consumerEdge
        canonicalAClearingFace.counterpartyConsumer.event = fulfillB := by
  let clearing :=
    sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
  exact ⟨⟨sourceGeneratedClearingConsumerDeath⟩,
    clearing.seedExact,
    clearing.fullResultExact,
    clearing.rootOccurrenceExact,
    ⟨clearing.mandate.installed.rootResponsibilityConsumer⟩,
    clearing.wholeLedgerExact,
    clearing.generatedNextExact,
    sourceGeneratedClearingConsumerDeath.canonicalOneSidedActionExact,
    sourceGeneratedClearingConsumerDeath.missingBoundaryEdgeExact⟩

theorem automaticAndNilControlsAreNotThisDeath :
    IsEmpty (OpenSettlementAt automaticCompiler automaticOccurrence) ∧
      Nonempty (OpenSettlementAt nilOpenCompiler nilOpenOccurrence) ∧
      IsEmpty (FulfilledExchangeLegAt nilOpenCompiler nilOpenOccurrence
        nilOpenA.leg) :=
  ⟨sourceGeneratedClearingConsumerDeath.automaticTargetClosed,
    sourceGeneratedClearingConsumerDeath.nilTargetOpen,
    sourceGeneratedClearingConsumerDeath.nilTargetAFulfillmentEmpty⟩

structure ProofCarryingClearingConsumerDeathCertificate : Prop where
  death : Nonempty (SourceGeneratedClearingConsumerDeathAt partialOpenB)
  exactFailure :
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
        (FullyFulfilledExchangeAt nilOpenCompiler nilOpenOccurrence)
  boundaryAuthorityStillExists :
    Nonempty (ExactLegFulfillmentAt (exchangeLaw := exchangeLaw)
        exactExchangeSeed (.b : Leg)) ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource
          canonicalAClearingFace.counterpartyConsumer.event)
        (exactExchangeSeed.obligation exchangeCompiler .b)) ∧
      partialOpenB.consumerEdge
          canonicalAClearingFace.counterpartyConsumer.event = fulfillB ∧
      IsEmpty (FulfilledExchangeLegAt settlementCompiler
        partialOccurrence partialOpenB.leg)
  rawAdapterExists :
    Nonempty (OpenSettlementAt.ActivatedResidualConsumerAt partialOpenB)
  rawAdapterExact :
    rawBackstopAdapter.edge = fulfillB ∧
      rawBackstopAdapter.edge.target.history =
        (partialOccurrence.current settlementCompiler).history ++
          [rawBackstopAdapter.edge.lifecycleEvent] ∧
      Nonempty (SourceOwnsResponsibilityIncidence V
        (P.boundarySource rawBackstopAdapter.activation)
        partialOpenB.obligation)
  currentCompilerCannotDischarge :
    (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
      (activation.openSettlement residualConsumerCompiler).leg = .b) ∧
      (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        activation.occurrence residualConsumerCompiler = partialOccurrence)
  periodicRootPairing : ∀ depth : Nat,
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    Nonempty (SourceGeneratedClearingConsumerDeathAt partialOpenB) ∧
      clearing.installed.payload.sourceSeed = commonClearingSeed ∧
      clearing.installed.payload.disposition.fullResult =
        AutomaticFullFulfillment.fullResult fulfillmentAuthority
          exactExchangeSeed ∧
      clearing.rootOccurrence =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth)) ∧
      Nonempty (RenewalResponsibilityConsumerAt
        clearing.mandate.installed.operationalAuthority) ∧
      clearing.appliedReform.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      clearing.appliedReform.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      canonicalAClearingFace.oneSidedEdge = fulfillA ∧
      partialOpenB.consumerEdge
        canonicalAClearingFace.counterpartyConsumer.event = fulfillB
  controls :
    IsEmpty (OpenSettlementAt automaticCompiler automaticOccurrence) ∧
      Nonempty (OpenSettlementAt nilOpenCompiler nilOpenOccurrence) ∧
      IsEmpty (FulfilledExchangeLegAt nilOpenCompiler nilOpenOccurrence
        nilOpenA.leg)

theorem proofCarryingClearingConsumerDeathDirectConsumer :
    ProofCarryingClearingConsumerDeathCertificate where
  death := ⟨sourceGeneratedClearingConsumerDeath⟩
  exactFailure := clearingConsumerDeath_exact
  boundaryAuthorityStillExists :=
    deathRetainsBoundaryAuthorityButLacksCurrentRealization
  rawAdapterExists :=
    rawBackstopAdapterExistsButLacksCurrentSourceProvenance.1
  rawAdapterExact :=
    rawBackstopAdapterExistsButLacksCurrentSourceProvenance.2
  currentCompilerCannotDischarge :=
    currentCompilerCannotDischargeBackstopResponsibility
  periodicRootPairing :=
    clearingDeathPairedWithEveryPeriodicRootVisit
  controls := automaticAndNilControlsAreNotThisDeath

end
end M14ProofCarryingClearingConsumerDeathRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingClearingConsumerDeathRegression.proofCarryingClearingConsumerDeathDirectConsumer
