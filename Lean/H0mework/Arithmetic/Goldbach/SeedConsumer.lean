import H0mework.Arithmetic.Goldbach.RuntimeConsumer

/-!
# Direct positive consumer at the operational Goldbach seed

Runtime depth zero owns classical-range index one.  Its branch-preserving
effective readout is forced to be inhabited by the source-generated `4 = 2+2`
fixture.  This consumer extracts that actual runtime fibre and returns every
prime, landing, coordinate, factor-event, occurrence, ledger and next receipt
from the same installed operational face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticOperationalGoldbachSeedConsumer

open CanonicalUnitArithmeticEffectiveAdditiveReadoutConsumer
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open CanonicalUnitArithmeticOperationalGoldbachRuntimeConsumer
open RootArithmeticUnfoldingFace
open SourceGeneratedEffectiveFibreDisposition
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

abbrev SeedIndex :=
  scanIndex (runtimeAt 0).current.visit.current

noncomputable def seedRuntime :=
  CanonicalUnitArithmeticOperationalGoldbachRuntimeConsumer.consume 0

theorem seedIndex_eq : SeedIndex = 1 := by
  simpa using seedRuntime.scanIndex_eq

theorem seedFibre_nonempty :
    Nonempty (EffectiveAdditiveFibreAt SeedIndex) := by
  rw [seedIndex_eq]
  exact ⟨goldbachAdditiveFibre⟩

/-- The actual inhabited branch extracted from the runtime readout.  The
fixed fixture is used only to eliminate the impossible residual branch; the
returned fibre is the one carried by `seedRuntime.additiveReadout`. -/
noncomputable def seedPositiveReadout :
    ActualInhabitedAdditiveReadoutAt SeedIndex
      seedRuntime.payload.additiveDisposition := by
  cases splitActualAdditiveReadout seedRuntime.additiveReadout with
  | inl positive => exact positive
  | inr negative =>
    have residualEqGenerated :=
      negative.disposition_eq.symm.trans
        seedRuntime.additiveDispositionGenerated
    have positiveAtSeed :
        generatedAdditiveDisposition SeedIndex =
          .inhabited (Classical.choice seedFibre_nonempty) :=
      settle_eq_inhabited_of_nonempty _ _ seedFibre_nonempty
    rw [positiveAtSeed] at residualEqGenerated
    exact nomatch residualEqGenerated

noncomputable def seedFibre : EffectiveAdditiveFibreAt SeedIndex :=
  seedPositiveReadout.fibre

theorem seedDispositionReadout :
    seedRuntime.payload.additiveDisposition = .inhabited seedFibre :=
  seedPositiveReadout.disposition_eq

theorem seedFibreConsumer :
    PositiveReadoutAt SeedIndex seedFibre :=
  seedPositiveReadout.consumer

/-- Fixed positive named coverage, now rooted in the operational runtime
rather than in the old settlement catalog. -/
structure SeedConsumesAt : Type 7 where
  private mk ::
  fibre : EffectiveAdditiveFibreAt SeedIndex
  fibre_eq : fibre = seedFibre
  dispositionReadout :
    seedRuntime.payload.additiveDisposition = .inhabited fibre
  fibreConsumer :
    PositiveReadoutAt SeedIndex fibre
  leftPrime : Nat.Prime fibre.leftHistory.cardinalShadow
  rightPrime : Nat.Prime fibre.rightHistory.cardinalShadow
  leftFactorizationLanding :
    CanonicalUnitArithmeticFactorizationOccurrence.factorialHistory
        (evenTargetHistory SeedIndex) =
      fibre.leftHistory.joint
        (generatedPrimeQuotientHistory fibre.leftPrimeIndex)
  rightFactorizationLanding :
    CanonicalUnitArithmeticFactorizationOccurrence.factorialHistory
        (evenTargetHistory SeedIndex) =
      fibre.rightHistory.joint
        (generatedPrimeQuotientHistory fibre.rightPrimeIndex)
  fibreMembership :
    additiveEvaluation SeedIndex fibre.1 = evenTargetHistory SeedIndex
  parallelLanding :
    evenTargetHistory SeedIndex =
      fibre.leftHistory.parallel fibre.rightHistory
  siblingFoldLanding :
    evenTargetHistory SeedIndex =
      parallelChildren [fibre.leftHistory, fibre.rightHistory]
  coordinateReadout : EffectiveAdditiveCoordinateReadoutAt SeedIndex fibre
  coordinateReadout_eq : coordinateReadout =
    CanonicalUnitArithmeticEffectiveAdditiveProducer.coordinateReadout fibre
  coordinateLanding :
    coordinateReadout.target = coordinateReadout.left + coordinateReadout.right
  targetOccurrenceGenerated : seedRuntime.payload.targetOccurrence =
    CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.evenTargetOccurrenceAt
      (runtimeAt 0).emittedOccurrence SeedIndex
  sourceOccurrence : seedRuntime.payload.sourceOccurrence =
    (runtimeAt 0).emittedOccurrence
  targetRoot :
    seedRuntime.payload.targetOccurrence.root.rootOccurrence =
      (runtimeAt 0).emittedOccurrence
  targetOccurrenceFold :
    seedRuntime.payload.targetOccurrence.fold
        CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.terminalHistoryAlgebra =
      evenTargetHistory SeedIndex
  factorDecayOccurrence :
    seedRuntime.payload.factorDecay.occurrence =
      seedRuntime.payload.targetOccurrence
  factorizationGenerated :
    seedRuntime.payload.factorDecay.factorization =
      evenTargetFactorization SeedIndex
  factorizationTargetFold :
    seedRuntime.payload.factorDecay.occurrence.fold
        CanonicalUnitArithmeticExactOccurrenceAdditiveProducer.terminalHistoryAlgebra =
      evenTargetHistory SeedIndex
  canonicalSource : seedRuntime.payload.factorDecay.source =
    canonicalSplit SeedIndex (runtimeActive 0).down
  everyChannelReceipt : ∀ state : EffectiveSplitAt SeedIndex,
    (channel : FactorDecayChannelAt state) →
      OperationalFactorDecayChannelReceiptAt channel
  everyPathReceipt : ∀ {source target : EffectiveSplitAt SeedIndex},
    (path : GeneratedPathAt (fullFactorDecayLaw SeedIndex) source target) →
      OperationalFactorDecayPathReceiptAt path
  namedReadout :
    runtimeFacade.readoutAt (runtimeAt 0) .operationalGoldbach =
      .inl ⟨runtimeActive 0, runtimePayload 0⟩
  emittedOccurrence :
    runtimeFacade.process.toAnswerNextCausalWorld.emitted
          (ULift.up (runtimeAt 0).state) =
      ULift.up (runtimeAt 0).tick.generated
  occurrenceRoot :
    (runtimeAt 0).tick.generated.occurrence =
      (runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (runtimeAt 0).current.visit.current
  wholeLedger :
    HEq (runtimeAt 0).tick.generated.wholeLedgerWriteBack
      ((runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt 0).current.visit.current)
  projectionFactorizes :
    HEq (runtimeFacade.readoutAt (runtimeAt 0) .operationalGoldbach)
      ((runtimeAt 0).tick.generated.projectionOutcome
        ((runtimeFacade.installationAt
          (runtimeAt 0) .operationalGoldbach).embed
          (runtimeFacade.projectionAt
            (runtimeAt 0) .operationalGoldbach)))
  generatedNext :
    (runtimeAt 0).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor (runtimeAt 0).state)

noncomputable def consume : SeedConsumesAt :=
  { fibre := seedFibre
    fibre_eq := rfl
    dispositionReadout := seedDispositionReadout
    fibreConsumer := seedFibreConsumer
    leftPrime := seedFibreConsumer.leftPrime
    rightPrime := seedFibreConsumer.rightPrime
    leftFactorizationLanding := seedFibreConsumer.leftFactorizationLanding
    rightFactorizationLanding := seedFibreConsumer.rightFactorizationLanding
    fibreMembership := seedFibreConsumer.fibreMembership
    parallelLanding := seedFibreConsumer.parallelLanding
    siblingFoldLanding := seedFibreConsumer.siblingFoldLanding
    coordinateReadout :=
      CanonicalUnitArithmeticEffectiveAdditiveProducer.coordinateReadout seedFibre
    coordinateReadout_eq := rfl
    coordinateLanding :=
      (CanonicalUnitArithmeticEffectiveAdditiveProducer.coordinateReadout
        seedFibre).target_eq_left_add_right
    targetOccurrenceGenerated := seedRuntime.targetOccurrenceGenerated
    sourceOccurrence := seedRuntime.sourceOccurrence
    targetRoot := seedRuntime.targetRoot
    targetOccurrenceFold := seedRuntime.targetOccurrenceFold
    factorDecayOccurrence := seedRuntime.factorDecayOccurrence
    factorizationGenerated := seedRuntime.factorDecayFactorizationGenerated
    factorizationTargetFold := seedRuntime.factorDecayTargetFold
    canonicalSource := seedRuntime.canonicalSource
    everyChannelReceipt := seedRuntime.everyChannelReceipt
    everyPathReceipt := seedRuntime.everyPathReceipt
    namedReadout := seedRuntime.namedReadout
    emittedOccurrence := seedRuntime.emittedOccurrence
    occurrenceRoot := seedRuntime.occurrenceRoot
    wholeLedger := seedRuntime.wholeLedger
    projectionFactorizes := seedRuntime.projectionFactorizes
    generatedNext := seedRuntime.generatedNext }

end
end CanonicalUnitArithmeticOperationalGoldbachSeedConsumer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
