import H0mework.Versions.R2.Arithmetic.Goldbach.EffectiveConsumer
import H0mework.Versions.R2.Arithmetic.Goldbach.SeedConsumer
import H0mework.Versions.R2.Arithmetic.GoldbachFourier.EffectiveCoefficient
import H0mework.Versions.R2.Arithmetic.GoldbachDynamics.FactorOrbit
import H0mework.Versions.R2.Arithmetic.GoldbachDynamics.RepairReachability
import H0mework.Versions.R2.Arithmetic.GoldbachDynamics.DecayReachability
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.DualReadouts
import H0mework.Versions.R2.Arithmetic.EulerLocal.UnitDeterminantAction

/-!
# Named generated settlement facade for canonical unit arithmetic

This facade inventories the arithmetic calculation faces generated from the
canonical root: exact factorization rows, the direct unit-normalized
cofinal relation history, the full-Euler local realization, quotient
rigidity, compact perfect/determinant/unit settlement, and the existing
occurrence-indexed effective Goldbach disposition together with its exact
nonnegative prime-pair coefficient.  Goldbach authority itself is supplied by
the installed operational runtime face; the stored fixed fibre remains a
positive calculation fixture.

It is a dependent facade over the existing runtime, not a second root.  Its
coverage theorem returns the same exact runtime occurrence, whole-ledger
write-back and generated next; none of those receipts is supplied to the
domain relation producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticGeneratedSettlementFacade

open CanonicalUnitArithmeticDualReadouts
open CanonicalUnitArithmeticEffectiveAdditiveCoefficientProducer
open CanonicalUnitArithmeticEffectiveAdditiveConsumer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorRepairReachabilityProducer
open CanonicalUnitArithmeticFullFactorDecayReachabilityProducer
open CanonicalUnitArithmeticFactorizationEulerLocalLanding
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticUnitNormalizedEulerLocalRealization
open CanonicalUnitArithmeticUnitNormalizedEulerDeterminantAction
open CanonicalUnitArithmeticUnitNormalizedRelationHistory
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open PerfectComplexDeterminantProjection
open PrimePowerKernelIncidenceRigidity
open RootGeneratedCanonicalUnitArithmeticPrimePowerCofinalClosure
  (scheduledFactor)

noncomputable section

/-- Complete public inventory of the generated arithmetic settlement. -/
inductive FaceAt
  | exactFactorizationRows
  | unitNormalizedRelationHistory
  | fullEulerLocalRealization
  | fullEulerDeterminantAction
  | primePowerRigidity
  | perfectDeterminantUnit
  | goldbachAdditiveCoefficient
  | goldbachAdditiveDisposition
  | goldbachFactorRepairOrbit
  | goldbachFullFactorReachability
  | goldbachFullFactorDecayReachability
  | goldbachAdditiveFibre
  | runtimeWholeLedgerAndNext
  deriving DecidableEq

/-- One named dependent facade.  The stored objects are generated objects,
not certificates submitted to their producers. -/
structure Facade : Type 7 where
  private mk ::
  relationHistory : RootGeneratedCofinalHistoryAt
    CanonicalUnitArithmeticUnitNormalizedRelationHistory.rootOccurrence
    seedEventOccurrence continuationOccurrence
  relationHistory_eq : relationHistory = history
  localEulerRealization : (cursor : Nat) →
    Carrier (scheduledFactor cursor) →ₗ[ℤ]
      history.CompletionCarrier
  localEulerRealization_eq : localEulerRealization = twoLevelRealization
  eulerDeterminantAction : FourTermIntegralComplexEquivAt
    twoLevelPerfectComplex twoLevelPerfectComplex
  eulerDeterminantAction_eq :
    eulerDeterminantAction = twoLevelEulerReversalComplexEquiv
  rigidity : RootGeneratedPrimePowerKernelIncidenceRigidityAt
    quotientFace.dependentOccurrence
  rigidity_eq : rigidity = rigidityFace
  compactReadout : GeneratedCompactPerfectReadoutAt history compactTrace
  compactReadout_eq : compactReadout = compactPerfectReadout
  additiveCoefficientFace : (index : Nat) →
    RootGeneratedAdditiveCoefficientAt index
  additiveCoefficientFace_eq : ∀ index,
    additiveCoefficientFace index = generatedAdditiveCoefficientFace index
  additiveFibre : GoldbachAdditiveFibreAt 1
  additiveFibre_eq : additiveFibre = goldbachAdditiveFibre
  additiveDisposition : (index : Nat) →
    CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveDispositionAt index
  additiveDisposition_eq : ∀ index,
    additiveDisposition index =
      CanonicalUnitArithmeticEffectiveAdditiveProducer.generatedAdditiveDisposition index
  factorRepairOrbit : (index : Nat) → (indexInRange : 1 ≤ index) →
    RootGeneratedEffectiveFactorRepairOrbitAt index indexInRange
  factorRepairOrbit_eq : ∀ index indexInRange,
    factorRepairOrbit index indexInRange =
      generatedFactorRepairOrbitFace index indexInRange
  fullFactorReachability : (index : Nat) → (indexInRange : 1 ≤ index) →
    RootGeneratedFullFactorRepairReachabilityAt index indexInRange
  fullFactorReachability_eq : ∀ index indexInRange,
    fullFactorReachability index indexInRange =
      generatedFullFactorRepairReachabilityFace index indexInRange
  fullFactorDecayReachability : (index : Nat) → (indexInRange : 1 ≤ index) →
    RootGeneratedFullFactorDecayReachabilityAt index indexInRange
  fullFactorDecayReachability_eq : ∀ index indexInRange,
    fullFactorDecayReachability index indexInRange =
      generatedFullFactorDecayReachabilityFace index indexInRange

def generatedFacade : Facade :=
  ⟨history, rfl, twoLevelRealization, rfl,
    twoLevelEulerReversalComplexEquiv, rfl,
    rigidityFace, rfl, compactPerfectReadout, rfl,
    generatedAdditiveCoefficientFace, fun _index => rfl,
    goldbachAdditiveFibre, rfl,
    CanonicalUnitArithmeticEffectiveAdditiveProducer.generatedAdditiveDisposition,
    fun _index => rfl,
    generatedFactorRepairOrbitFace, fun _index _indexInRange => rfl,
    generatedFullFactorRepairReachabilityFace,
    fun _index _indexInRange => rfl,
    generatedFullFactorDecayReachabilityFace,
    fun _index _indexInRange => rfl⟩

def determinantStateAt (_facade : Facade) := determinantState

abbrev IntegralLineAt (facade : Facade) :=
  (determinantStateAt facade).integralLine

noncomputable def unitTorsorAt (facade : Facade) :=
  (determinantStateAt facade).unitTorsor

/-- Face-specific coverage.  Each branch is a concrete factorization claim,
not a Boolean registry marker. -/
def CoversAt (facade : Facade) : FaceAt → Prop
  | .exactFactorizationRows =>
      ∀ cursor,
        (certifiedRelationRowOccurrence cursor).map Prod.fst =
          factorizationOccurrence (scheduledFactor cursor).stage
  | .unitNormalizedRelationHistory =>
      facade.relationHistory = history ∧
        history.root =
          CanonicalUnitArithmeticUnitNormalizedRelationHistory.rootOccurrence ∧
        history.actualContinuation = nextPatch
  | .fullEulerLocalRealization =>
      facade.localEulerRealization = twoLevelRealization ∧
        ∀ cursor,
          twoLevelRealization cursor
              (difference (scheduledFactor cursor)) = 0 ∧
            twoLevelRealization cursor
                (component (scheduledFactor cursor)) =
              twoLevelRealization cursor
                (reversedComponent (scheduledFactor cursor))
  | .fullEulerDeterminantAction =>
      facade.eulerDeterminantAction =
          twoLevelEulerReversalComplexEquiv ∧
        twoLevelDeterminantNaturality.root = history.root ∧
        Nonempty (TwoLevelIntegralLine ≃ₗ[ℤ] TwoLevelIntegralLine) ∧
        twoLevelEulerReversalEquiv stageZeroReversalEquiv ≠
          twoLevelPointwiseEquiv stageZeroReversalEquiv ∧
        (∀ cursor,
          completionTwoLevelSum
              (completionTwoLevelBoundary
                (completionTwoLevelSource cursor)) =
            twoLevelRealization cursor
              (component (scheduledFactor cursor)))
  | .primePowerRigidity =>
      facade.rigidity = rigidityFace ∧
        globalComponent = 0 ∧
        componentClass 0 = componentClass 1
  | .perfectDeterminantUnit =>
      facade.compactReadout = compactPerfectReadout ∧
        Nonempty
          ((history.generatorStage compactTrace.index ⧸
            LinearMap.ker
              (history.stageGeneratorToCompletion compactTrace.index)) ≃ₗ[ℤ]
            history.CompletionCarrier) ∧
        Nonempty
          (GradedIntegralDeterminantLine.CanonicalIntegralUnitTorsor
            (IntegralLineAt facade))
  | .goldbachAdditiveCoefficient =>
      ∀ index,
        facade.additiveCoefficientFace index =
            generatedAdditiveCoefficientFace index ∧
          (facade.additiveCoefficientFace index).occurrence =
            CanonicalUnitArithmeticEffectiveAdditiveProducer.evenTargetOccurrence index ∧
          (facade.additiveCoefficientFace index).factorization =
            CanonicalUnitArithmeticEffectiveAdditiveProducer.generatedEvenTargetFactorization index ∧
          (facade.additiveCoefficientFace index).additivePolynomial =
            (facade.additiveCoefficientFace index).primePolynomial *
              (facade.additiveCoefficientFace index).primePolynomial ∧
          (0 < (facade.additiveCoefficientFace index).coefficient ↔
            Nonempty
              (CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveFibreAt
                index)) ∧
          ((facade.additiveCoefficientFace index).coefficient = 0 ↔
            ¬ Nonempty
              (CanonicalUnitArithmeticEffectiveAdditiveProducer.EffectiveAdditiveFibreAt
                index))
  | .goldbachAdditiveDisposition =>
      (∀ index,
        facade.additiveDisposition index =
          CanonicalUnitArithmeticEffectiveAdditiveProducer.generatedAdditiveDisposition index) ∧
      (∀ index,
        Nonempty (TotalConsumesAt index (facade.additiveDisposition index))) ∧
      (∀ depth,
        ∃ runtime :
            CanonicalUnitArithmeticOperationalGoldbachRuntimeConsumer.ConsumesAt
              depth,
          facade.additiveDisposition
              (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex
                (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt
                  depth).current.visit.current) =
            runtime.payload.additiveDisposition)
  | .goldbachFactorRepairOrbit =>
      ∀ index indexInRange,
        facade.factorRepairOrbit index indexInRange =
            generatedFactorRepairOrbitFace index indexInRange ∧
          (facade.factorRepairOrbit index indexInRange).occurrence =
            CanonicalUnitArithmeticEffectiveAdditiveProducer.evenTargetOccurrence index ∧
          (facade.factorRepairOrbit index indexInRange).factorization =
            CanonicalUnitArithmeticEffectiveAdditiveProducer.generatedEvenTargetFactorization index ∧
          (facade.factorRepairOrbit index indexInRange).source =
            canonicalSplit index indexInRange ∧
          (facade.factorRepairOrbit index indexInRange).disposition =
            generatedFactorRepairDisposition index indexInRange
  | .goldbachFullFactorReachability =>
      ∀ index indexInRange,
        facade.fullFactorReachability index indexInRange =
            generatedFullFactorRepairReachabilityFace index indexInRange ∧
          (facade.fullFactorReachability index indexInRange).occurrence =
            CanonicalUnitArithmeticEffectiveAdditiveProducer.evenTargetOccurrence index ∧
          (facade.fullFactorReachability index indexInRange).factorization =
            CanonicalUnitArithmeticEffectiveAdditiveProducer.generatedEvenTargetFactorization index ∧
          (facade.fullFactorReachability index indexInRange).source =
            canonicalSplit index indexInRange ∧
          (facade.fullFactorReachability index indexInRange).disposition =
            generatedFullFactorReachabilityDisposition index indexInRange
  | .goldbachFullFactorDecayReachability =>
      ∀ index indexInRange,
        facade.fullFactorDecayReachability index indexInRange =
            generatedFullFactorDecayReachabilityFace index indexInRange ∧
          (facade.fullFactorDecayReachability index indexInRange).occurrence =
            CanonicalUnitArithmeticEffectiveAdditiveProducer.evenTargetOccurrence index ∧
          (facade.fullFactorDecayReachability index indexInRange).factorization =
            CanonicalUnitArithmeticEffectiveAdditiveProducer.generatedEvenTargetFactorization index ∧
          (facade.fullFactorDecayReachability index indexInRange).source =
            canonicalSplit index indexInRange ∧
          (facade.fullFactorDecayReachability index indexInRange).disposition =
            generatedFullFactorDecayDisposition index indexInRange
  | .goldbachAdditiveFibre =>
      facade.additiveFibre = goldbachAdditiveFibre ∧
        ConsumesAt 1 facade.additiveFibre ∧
        Nonempty
          CanonicalUnitArithmeticOperationalGoldbachSeedConsumer.SeedConsumesAt
  | .runtimeWholeLedgerAndNext =>
      (runtimeAt 0).tick.generated.occurrence =
          (runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
            (runtimeAt 0).current.visit.current ∧
        HEq (runtimeAt 0).tick.generated.wholeLedgerWriteBack
          ((runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (runtimeAt 0).current.visit.current) ∧
        (runtimeAt 0).tick.nextCurrent =
          runtimeFacade.process.stateAt
            (runtimeFacade.process.successor (runtimeAt 0).state)

theorem coversAt (face : FaceAt) : CoversAt generatedFacade face := by
  cases face with
  | exactFactorizationRows =>
      intro cursor
      exact certifiedRelationRowOccurrence_projects_to_factorization cursor
  | unitNormalizedRelationHistory =>
      exact ⟨rfl, rfl, rfl⟩
  | fullEulerLocalRealization =>
      refine ⟨rfl, fun cursor => ?_⟩
      exact ⟨twoLevelRealization_difference_zero cursor,
        twoLevelRealization_generatedFixedComponent cursor⟩
  | fullEulerDeterminantAction =>
      exact ⟨rfl, rfl, ⟨twoLevelDeterminantLineEulerReversal⟩,
        twoLevelEulerReversal_ne_bareReversal,
        actualLocalEulerComponent_is_determinantBoundary⟩
  | primePowerRigidity =>
      exact ⟨rfl, globalComponent_eq_zero, generatedFixedComponent⟩
  | perfectDeterminantUnit =>
      exact ⟨rfl,
        ⟨compactPerfectReadout.degreeOneHomologyEquiv⟩,
        ⟨unitTorsorAt generatedFacade⟩⟩
  | goldbachAdditiveCoefficient =>
      intro index
      exact ⟨rfl,
        (generatedAdditiveCoefficientFace index).occurrence_eq,
        (generatedAdditiveCoefficientFace index).factorization_eq,
        (generatedAdditiveCoefficientFace index).convolutionSquare,
        (generatedAdditiveCoefficientFace index).positiveIffFibre,
        (generatedAdditiveCoefficientFace index).zeroIffFibreEmpty⟩
  | goldbachAdditiveDisposition =>
      exact ⟨fun _index => rfl,
        fun index => ⟨consumeGeneratedDisposition index⟩,
        fun depth => by
          let runtime :=
            CanonicalUnitArithmeticOperationalGoldbachRuntimeConsumer.consume
              depth
          exact ⟨runtime, by
            rw [generatedFacade.additiveDisposition_eq,
              runtime.additiveDispositionGenerated]⟩⟩
  | goldbachFactorRepairOrbit =>
      intro index indexInRange
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | goldbachFullFactorReachability =>
      intro index indexInRange
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | goldbachFullFactorDecayReachability =>
      intro index indexInRange
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | goldbachAdditiveFibre =>
      exact ⟨rfl, goldbachConsumer,
        ⟨CanonicalUnitArithmeticOperationalGoldbachSeedConsumer.consume⟩⟩
  | runtimeWholeLedgerAndNext =>
      exact runtime_authority_factorizes 0

theorem coversAt_factorizes (face : FaceAt) :
    CoversAt generatedFacade face ∧
      (runtimeAt 0).tick.generated.occurrence =
        (runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtimeAt 0).current.visit.current ∧
      HEq (runtimeAt 0).tick.generated.wholeLedgerWriteBack
        ((runtimeAt 0).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtimeAt 0).current.visit.current) ∧
      (runtimeAt 0).tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor (runtimeAt 0).state) := by
  exact ⟨coversAt face, runtime_authority_factorizes 0⟩

theorem all_named_faces_covered :
    ∀ face : FaceAt, CoversAt generatedFacade face :=
  coversAt

/-- The historical fixed `4 = 2 + 2` calculation consumer.  It is retained as
a regression fixture and is not the operational authority mouth. -/
theorem goldbachFixedFourCatalogCoverage :
    ConsumesAt 1 generatedFacade.additiveFibre :=
  (coversAt .goldbachAdditiveFibre).2.1

/-- Named Goldbach coverage now returns the actual operational seed consumer:
prime restrictions, both landings, effective fibre/readout, factor channels,
exact occurrence, projection, whole ledger and generated next. -/
noncomputable def goldbachCoverage :
    CanonicalUnitArithmeticOperationalGoldbachSeedConsumer.SeedConsumesAt :=
  Classical.choice (coversAt .goldbachAdditiveFibre).2.2

/-- Pointwise calculation disposition retained for existing arithmetic
consumers.  Operational authority is `goldbachOperationalDispositionCoverage`.
-/
noncomputable def goldbachDispositionCoverage (index : Nat) :
    TotalConsumesAt index (generatedFacade.additiveDisposition index) :=
  consumeGeneratedDisposition index

/-- Occurrence-indexed operational Goldbach coverage.  Runtime depth owns the
classical-range target index and returns the actual fibre-or-residual readout,
complete factor-channel inventory, whole ledger and generated next. -/
noncomputable def goldbachOperationalDispositionCoverage (depth : Nat) :
    CanonicalUnitArithmeticOperationalGoldbachRuntimeConsumer.ConsumesAt depth :=
  Classical.choose ((coversAt .goldbachAdditiveDisposition).2.2 depth)

theorem goldbachOperationalDispositionCoverage_eq_catalog (depth : Nat) :
    generatedFacade.additiveDisposition
        (CanonicalUnitArithmeticOperationalGoldbachRuntime.scanIndex
          (CanonicalUnitArithmeticOperationalGoldbachRuntime.runtimeAt
            depth).current.visit.current) =
      (goldbachOperationalDispositionCoverage depth).payload.additiveDisposition :=
  Classical.choose_spec ((coversAt .goldbachAdditiveDisposition).2.2 depth)

/-- Classical-range factor-repair authority is the exact producer stored by
the same named facade. -/
theorem goldbachFactorRepairCoverage (index : Nat)
    (indexInRange : 1 ≤ index) :
    generatedFacade.factorRepairOrbit index indexInRange =
      generatedFactorRepairOrbitFace index indexInRange :=
  (coversAt .goldbachFactorRepairOrbit index indexInRange).1

/-- Complete full-factor reachable-image authority stored by the same named
facade. -/
theorem goldbachFullFactorReachabilityCoverage (index : Nat)
    (indexInRange : 1 ≤ index) :
    generatedFacade.fullFactorReachability index indexInRange =
      generatedFullFactorRepairReachabilityFace index indexInRange :=
  (coversAt .goldbachFullFactorReachability index indexInRange).1

theorem goldbachFullFactorDecayReachabilityCoverage (index : Nat)
    (indexInRange : 1 ≤ index) :
    generatedFacade.fullFactorDecayReachability index indexInRange =
      generatedFullFactorDecayReachabilityFace index indexInRange :=
  (coversAt .goldbachFullFactorDecayReachability index indexInRange).1

end

end CanonicalUnitArithmeticGeneratedSettlementFacade
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
