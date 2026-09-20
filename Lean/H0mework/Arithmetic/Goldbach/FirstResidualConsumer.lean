import H0mework.Arithmetic.Goldbach.RuntimeConsumer
import H0mework.Arithmetic.GoldbachResidual.PrimeTrace
import H0mework.Arithmetic.Goldbach.FirstResidualProducer

/-!
# Direct consumer of the operational first residual

The old least counterexample package now only locates an already emitted
runtime visit.  This consumer combines that visit with the existing dark SCC:
every SCC channel has a canonical operational receipt, every SCC path lifts
to an ordered residual path, and the same runtime projection returns the
whole ledger and generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticOperationalFirstResidualConsumer

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFirstResidualFullFactorDecayPrimeTraceProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticGlobalGoldbachDisposition
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open CanonicalUnitArithmeticOperationalFirstResidualProducer
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open SourceGeneratedFiniteEffectiveBranchingReachability
open SourceGeneratedFiniteEventIndexedResidualProcess

noncomputable section

structure ConsumesAt (failure : FirstResidualOccurrence) : Type 7 where
  operational : RootGeneratedOperationalFirstResidualAt failure
  operational_eq : operational = generateOperationalFirstResidual failure
  runtime :
    CanonicalUnitArithmeticOperationalGoldbachRuntimeConsumer.ConsumesAt
      (failureDepth failure)
  primeTrace : RootGeneratedFirstResidualFullFactorDecayPrimeTraceAt failure
  primeTrace_eq : primeTrace =
    generateFirstResidualFullFactorDecayPrimeTrace failure
  runtimeIndex :
    scanIndex (runtimeAt (failureDepth failure)).current.visit.current =
      failure.index
  residualReadout : HEq
    runtime.payload.additiveDisposition
      (residualDisposition failure.residual)
  everySCCChannelReceipt : ∀ state,
    state ∈ primeTrace.scc.scc.sector.states →
      (channel : FactorDecayChannelAt state) →
        OperationalFactorDecayChannelReceiptAt channel
  everySCCChannelTarget : ∀ state,
    (stateMem : state ∈ primeTrace.scc.scc.sector.states) →
      (channel : FactorDecayChannelAt state) →
        (everySCCChannelReceipt state stateMem channel).step.target = channel.target
  pathBetweenOperational : ∀ source,
    source ∈ primeTrace.scc.scc.sector.states →
      ∀ target, target ∈ primeTrace.scc.scc.sector.states →
        SourceGeneratedFiniteEventIndexedResidualProcess.GeneratedPathAt
          (factorDecayProcess failure.index) source target
  sourceOccurrence :
    (runtimePayload (failureDepth failure)).sourceOccurrence =
      (runtimeAt (failureDepth failure)).emittedOccurrence
  namedReadout :
    runtimeFacade.readoutAt (runtimeAt (failureDepth failure))
        .operationalGoldbach =
      .inl ⟨runtimeActive (failureDepth failure),
        runtimePayload (failureDepth failure)⟩
  wholeLedger :
    HEq (runtimeAt (failureDepth failure)).tick.generated.wholeLedgerWriteBack
      ((runtimeAt (failureDepth failure)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt (failureDepth failure)).current.visit.current)
  projectionFactorizes :
    HEq
      (runtimeFacade.readoutAt (runtimeAt (failureDepth failure))
        .operationalGoldbach)
      ((runtimeAt (failureDepth failure)).tick.generated.projectionOutcome
        ((runtimeFacade.installationAt
          (runtimeAt (failureDepth failure)) .operationalGoldbach).embed
          (runtimeFacade.projectionAt
            (runtimeAt (failureDepth failure)) .operationalGoldbach)))
  generatedNext :
    (runtimeAt (failureDepth failure)).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor
          (runtimeAt (failureDepth failure)).state)

noncomputable def consume (failure : FirstResidualOccurrence) :
    ConsumesAt failure := by
  let operational := generateOperationalFirstResidual failure
  let runtime :=
    CanonicalUnitArithmeticOperationalGoldbachRuntimeConsumer.consume
      (failureDepth failure)
  let primeTrace := generateFirstResidualFullFactorDecayPrimeTrace failure
  have runtimeChannelReceiptAtFailure : ∀
      (state : EffectiveSplitAt failure.index),
      (channel : FactorDecayChannelAt state) →
        OperationalFactorDecayChannelReceiptAt channel := by
    rw [← operational.runtimeIndex]
    exact runtime.everyChannelReceipt
  have runtimePathReceiptAtFailure : ∀
      {source target : EffectiveSplitAt failure.index},
      (path : SourceGeneratedFiniteEffectiveBranchingReachability.GeneratedPathAt
        (CanonicalUnitArithmeticFullFactorEmissionProducer.fullFactorDecayLaw
          failure.index) source target) →
        OperationalFactorDecayPathReceiptAt path := by
    rw [← operational.runtimeIndex]
    exact runtime.everyPathReceipt
  exact
    { operational := operational
      operational_eq := rfl
      runtime := runtime
      primeTrace := primeTrace
      primeTrace_eq := rfl
      runtimeIndex := operational.runtimeIndex
      residualReadout := by
        exact HEq.trans
          (heq_of_eq (congrArg
            (fun payload => payload.additiveDisposition)
            runtime.payload_eq))
          operational.dispositionIsResidual
      everySCCChannelReceipt := fun _state _stateMem channel =>
        runtimeChannelReceiptAtFailure _state channel
      everySCCChannelTarget := fun _state _stateMem channel =>
        (runtimeChannelReceiptAtFailure _state channel).target_eq
      pathBetweenOperational := by
        intro source sourceMem target targetMem
        let path := primeTrace.scc.pathBetween source sourceMem target targetMem
        exact (runtimePathReceiptAtFailure path).path
      sourceOccurrence := operational.sourceOccurrence
      namedReadout := operational.namedReadout
      wholeLedger := operational.wholeLedger
      projectionFactorizes := operational.projectionFactorizes
      generatedNext := operational.generatedNext }

end
end CanonicalUnitArithmeticOperationalFirstResidualConsumer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
