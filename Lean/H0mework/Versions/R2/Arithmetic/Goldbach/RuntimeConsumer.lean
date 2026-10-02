import H0mework.Versions.R2.Arithmetic.Goldbach.EffectiveReadout
import H0mework.Versions.R2.Arithmetic.GoldbachDynamics.Runtime

/-!
# Direct consumer of the operational Goldbach runtime face

The consumer reads the event-indexed factor process from the real
`SourceNativeLivingRuntimeFacade`.  Every channel returns its exact target,
signed conservative trace and recollecting write-back together with the same
runtime projection equation, whole ledger and generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticOperationalGoldbachRuntimeConsumer

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticEffectiveAdditiveReadoutConsumer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open SourceGeneratedFiniteEventIndexedResidualProcess

noncomputable section

abbrev RuntimeIndex (depth : Nat) :=
  scanIndex (runtimeAt depth).current.visit.current

/-- Branch-preserving elimination of the actual effective readout.  This is
used by named runtime consumers so the inhabited branch returns its concrete
prime-pair fibre and the residual branch returns its faithful miss witness. -/
theorem actualAdditiveReadout_cases {index : Nat}
    {disposition :
      CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveDispositionAt
        index}
    (readout : TotalReadoutAt index disposition) :
    (∃ fibre,
      disposition =
        SourceGeneratedEffectiveFibreDisposition.Disposition.inhabited fibre ∧
      PositiveReadoutAt index fibre) ∨
    (∃ residual,
      disposition =
        SourceGeneratedEffectiveFibreDisposition.Disposition.residual residual ∧
      ResidualReadoutAt index residual) := by
  cases readout with
  | inhabited fibre consumer => exact .inl ⟨fibre, rfl, consumer⟩
  | residual residual consumer => exact .inr ⟨residual, rfl, consumer⟩

/-- Type-valued positive branch of an effective additive readout. -/
structure ActualInhabitedAdditiveReadoutAt (index : Nat)
    (disposition :
      CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveDispositionAt
        index) : Type where
  fibre : CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveFibreAt
    index
  disposition_eq : disposition =
    SourceGeneratedEffectiveFibreDisposition.Disposition.inhabited fibre
  consumer : PositiveReadoutAt
    index fibre

/-- Type-valued faithful-residual branch of an effective additive readout. -/
structure ActualResidualAdditiveReadoutAt (index : Nat)
    (disposition :
      CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveDispositionAt
        index) : Type where
  residual :
    CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveResidualAt
      index
  disposition_eq : disposition =
    SourceGeneratedEffectiveFibreDisposition.Disposition.residual residual
  consumer : ResidualReadoutAt index residual

/-- Large-elimination-safe branch split used by dependent runtime producers. -/
def splitActualAdditiveReadout {index : Nat}
    {disposition :
      CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveDispositionAt
        index}
    (readout : TotalReadoutAt index disposition) :
    ActualInhabitedAdditiveReadoutAt index disposition ⊕
      ActualResidualAdditiveReadoutAt index disposition := by
  cases readout with
  | inhabited fibre consumer => exact .inl ⟨fibre, rfl, consumer⟩
  | residual residual consumer => exact .inr ⟨residual, rfl, consumer⟩

structure ConsumesAt (depth : Nat) : Type 7 where
  payload : RootGeneratedOperationalGoldbachCurrentAt
    (runtimeAt depth).current.visit.current (runtimeAt depth).emittedOccurrence
    (runtimeActive depth).down
  payload_eq : payload = runtimePayload depth
  namedReadout :
    runtimeFacade.readoutAt (runtimeAt depth) .operationalGoldbach =
      .inl ⟨runtimeActive depth, payload⟩
  scanIndex_eq : scanIndex (runtimeAt depth).current.visit.current = depth + 1
  additiveDispositionGenerated : payload.additiveDisposition =
    CanonicalUnitArithmeticEffectiveAdditiveProducer.generatedAdditiveDisposition
      (scanIndex (runtimeAt depth).current.visit.current)
  additiveReadout : TotalReadoutAt
    (scanIndex (runtimeAt depth).current.visit.current)
    payload.additiveDisposition
  targetOccurrenceGenerated : payload.targetOccurrence =
    CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.evenTargetOccurrenceAt
      (runtimeAt depth).emittedOccurrence
      (scanIndex (runtimeAt depth).current.visit.current)
  sourceOccurrence : payload.sourceOccurrence =
    (runtimeAt depth).emittedOccurrence
  targetRoot :
    payload.targetOccurrence.root.rootOccurrence =
      (runtimeAt depth).emittedOccurrence
  targetOccurrenceFold :
    payload.targetOccurrence.fold
        CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.terminalHistoryAlgebra =
      CanonicalUnitArithmeticEffectiveAdditiveProducer.evenTargetHistory
        (scanIndex (runtimeAt depth).current.visit.current)
  factorDecayGenerated : payload.factorDecay =
    CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer.generate
      (runtimeAt depth).emittedOccurrence
      (scanIndex (runtimeAt depth).current.visit.current)
      (runtimeActive depth).down
  factorDecayOccurrence :
    payload.factorDecay.occurrence = payload.targetOccurrence
  factorDecayFactorizationGenerated :
    payload.factorDecay.factorization =
      CanonicalUnitArithmeticEffectiveAdditiveProducer.evenTargetFactorization
        (scanIndex (runtimeAt depth).current.visit.current)
  factorDecayTargetFold :
    payload.factorDecay.occurrence.fold
        CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.terminalHistoryAlgebra =
      CanonicalUnitArithmeticEffectiveAdditiveProducer.evenTargetHistory
        (scanIndex (runtimeAt depth).current.visit.current)
  canonicalSource : payload.factorDecay.source =
    CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer.canonicalSplit
      (scanIndex (runtimeAt depth).current.visit.current)
      (runtimeActive depth).down
  everyChannelReceipt : ∀ state : EffectiveSplitAt
      (scanIndex (runtimeAt depth).current.visit.current),
    (channel : FactorDecayChannelAt state) →
      OperationalFactorDecayChannelReceiptAt channel
  everyChannelTarget : ∀ state : EffectiveSplitAt
      (scanIndex (runtimeAt depth).current.visit.current),
    (channel : FactorDecayChannelAt state) →
      (everyChannelReceipt state channel).step.target = channel.target
  everyChannelConservesTotal : ∀ state : EffectiveSplitAt
      (scanIndex (runtimeAt depth).current.visit.current),
    (channel : FactorDecayChannelAt state) →
      (everyChannelReceipt state channel).step.trace.1 +
        (everyChannelReceipt state channel).step.trace.2 = 0
  everyChannelWriteBackRecollects : ∀ state : EffectiveSplitAt
      (scanIndex (runtimeAt depth).current.visit.current),
    (channel : FactorDecayChannelAt state) →
      (factorDecayProcess
          (scanIndex (runtimeAt depth).current.visit.current)).recollectTrace
          (everyChannelReceipt state channel).step.writeBack.live
          (everyChannelReceipt state channel).step.writeBack.trace =
        splitResidual state
  everyChannelLifecycleProgress : ∀ state : EffectiveSplitAt
      (scanIndex (runtimeAt depth).current.visit.current),
    (channel : FactorDecayChannelAt state) →
      (everyChannelReceipt state channel).lifecycleEdge.lifecycleEvent.kind.IsProgress
  everyPathReceipt : ∀
      {source target : EffectiveSplitAt
        (scanIndex (runtimeAt depth).current.visit.current)},
    (path : SourceGeneratedFiniteEffectiveBranchingReachability.GeneratedPathAt
      (CanonicalUnitArithmeticFullFactorEmissionProducer.fullFactorDecayLaw
        (scanIndex (runtimeAt depth).current.visit.current)) source target) →
      OperationalFactorDecayPathReceiptAt path
  emittedOccurrence :
    runtimeFacade.process.toAnswerNextCausalWorld.emitted
        (ULift.up (runtimeAt depth).state) =
      ULift.up (runtimeAt depth).tick.generated
  occurrenceRoot :
    (runtimeAt depth).tick.generated.occurrence =
      (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (runtimeAt depth).current.visit.current
  wholeLedger :
    HEq (runtimeAt depth).tick.generated.wholeLedgerWriteBack
      ((runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt depth).current.visit.current)
  projectionFactorizes :
    HEq (runtimeFacade.readoutAt (runtimeAt depth) .operationalGoldbach)
      ((runtimeAt depth).tick.generated.projectionOutcome
        ((runtimeFacade.installationAt
          (runtimeAt depth) .operationalGoldbach).embed
          (runtimeFacade.projectionAt
            (runtimeAt depth) .operationalGoldbach)))
  generatedNext :
    (runtimeAt depth).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor (runtimeAt depth).state)

noncomputable def consume (depth : Nat) : ConsumesAt depth := by
  let runtime := runtimeAt depth
  let payload := runtimePayload depth
  let additiveReadoutAtPayload :=
    consumeDisposition payload.additiveDisposition
  have factorization := coversAt_factorizes runtime .operationalGoldbach
  exact
    { payload := payload
      payload_eq := rfl
      namedReadout := runtimeReadout_is_operational depth
      scanIndex_eq := runtimeAt_scanIndex depth
      additiveDispositionGenerated := payload.additiveDisposition_eq
      additiveReadout := additiveReadoutAtPayload
      targetOccurrenceGenerated := payload.targetOccurrence_eq
      sourceOccurrence := payload.sourceOccurrence_eq
      targetRoot := payload.targetRoot
      targetOccurrenceFold := by
        rw [← payload.factorDecayOccurrence]
        exact payload.factorDecay.targetFold
      factorDecayGenerated := payload.factorDecay_eq
      factorDecayOccurrence := payload.factorDecayOccurrence
      factorDecayFactorizationGenerated :=
        payload.factorDecay.factorization_eq
      factorDecayTargetFold := payload.factorDecay.targetFold
      canonicalSource := payload.factorDecay.source_eq
      everyChannelReceipt := fun _state channel =>
        payload.factorDecay.channelReceipt _state channel
      everyChannelTarget := fun state channel =>
        (payload.factorDecay.channelReceipt state channel).target_eq
      everyChannelConservesTotal := fun state channel =>
        (payload.factorDecay.channelReceipt state channel).trace_total_zero
      everyChannelWriteBackRecollects := fun state channel =>
        (payload.factorDecay.channelReceipt state channel).writeBack_recollects
      everyChannelLifecycleProgress := fun state channel =>
        (payload.factorDecay.channelReceipt state channel).lifecycleProgress
      everyPathReceipt := fun path => payload.factorDecay.pathReceipt path
      emittedOccurrence := factorization.1
      occurrenceRoot := factorization.2.1
      wholeLedger := factorization.2.2.1
      projectionFactorizes := factorization.2.2.2.1
      generatedNext := factorization.2.2.2.2 }

end
end CanonicalUnitArithmeticOperationalGoldbachRuntimeConsumer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
