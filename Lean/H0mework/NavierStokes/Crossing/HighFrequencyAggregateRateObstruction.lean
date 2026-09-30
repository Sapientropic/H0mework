import H0mework.NavierStokes.Crossing.HighFrequencyAggregatePersistence

/-!
# Physical rate obstruction of a generated high-frequency aggregate

The canonical persistence charge is consumed before its finite coefficient
family is forgotten.  Its tangent square is paid by the same restart
segment's dual-square ledger, while its frequency-weighted coefficient mass
is bounded by the actual current's whole gradient mass.  Consequently every
generated aggregate satisfies the source-native alternative

```text
ν T M ≤ 2 K
or
M³ ≤ 32 (2π)² G D K,
```

where `T` is the actual successor time, `G` the current whole gradient mass,
`D` the successor dual-square payment, and `K` the successor kinetic
payment.  No rate ceiling, cutoff, branch, or absorption certificate is
supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateRateObstruction

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregatePersistence
open AffineRelaxation

noncomputable section

/-- The selected finite family's viscous multiplier mass is paid by the
actual current's whole Fourier-gradient carrier. -/
theorem finiteAggregateWeightedInitialMass_le_wholeGradientMass
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector) :
    (∑ output ∈ modes,
        integerWaveViscousMultiplier output *
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output)) ≤
      (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass
          (run initial index).contact.physicalState := by
  let state := (run initial index).contact.physicalState
  have finiteLe :=
    finiteStateVorticityEnstrophyMass_le_wholeGradientMass
      modes state (run initial index).contact.gradient_summable
  calc
    (∑ output ∈ modes,
        integerWaveViscousMultiplier output *
          complexCoordinateAmplitudeSq (state output)) =
        (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes state := by
      unfold integerWaveViscousMultiplier
        finiteStateVorticityEnstrophyMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro output outputMem
      ring
    _ ≤
        (2 * Real.pi) ^ 2 *
          wholeStateVorticityGradientMass state :=
      mul_le_mul_of_nonneg_left finiteLe (sq_nonneg _)

/-- The explicit persistence charge has only two possible physical rate
escapes.  Both alternatives live on the same actual restart event: either
contact time times aggregate mass is paid by kinetic dissipation, or cubic
aggregate mass is paid by current gradient mass, successor dual-square
payment, and successor kinetic payment together. -/
theorem wholeRestartCrossingFiniteAggregate_physicalRateObstruction
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ output ∈ modes, output ≠ 0)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) :
    let initialMass :=
      ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
    let wholeGradientMass :=
      wholeStateVorticityGradientMass
        (run initial index).contact.physicalState
    let segmentDualSquarePayment :=
      wholeRestartSegmentDualSquarePayment initial (index + 1)
    let kineticPayment :=
      wholeRestartNextKineticDissipationPayment initial index
    ν.coeff * (run initial index).nextContact.time.1 * initialMass ≤
        2 * kineticPayment ∨
      initialMass ^ 3 ≤
        32 * (2 * Real.pi) ^ 2 * wholeGradientMass *
          segmentDualSquarePayment * kineticPayment := by
  let initialMass :=
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        ((run initial index).contact.physicalState output)
  let weightedInitialMass :=
    ∑ output ∈ modes,
      integerWaveViscousMultiplier output *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
  let tangentSq :=
    ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2
  let contactTime := (run initial index).nextContact.time.1
  let wholeGradientMass :=
    wholeStateVorticityGradientMass
      (run initial index).contact.physicalState
  let segmentDualSquarePayment :=
    wholeRestartSegmentDualSquarePayment initial (index + 1)
  let kineticPayment :=
    wholeRestartNextKineticDissipationPayment initial index
  let charge :=
    wholeRestartCrossingFiniteAggregateKineticCharge
      initial index modes
  change
    ν.coeff * contactTime * initialMass ≤ 2 * kineticPayment ∨
      initialMass ^ 3 ≤
        32 * (2 * Real.pi) ^ 2 * wholeGradientMass *
          segmentDualSquarePayment * kineticPayment
  have initialMassPos' : 0 < initialMass := by
    simpa only [initialMass] using initialMassPos
  have weightedInitialMassPos : 0 < weightedInitialMass := by
    simpa only [weightedInitialMass] using
      wholeRestartCrossingFiniteAggregateWeightedInitialMass_pos
        initial index modes modesNonzero initialMassPos
  have tangentSqPos : 0 < tangentSq := by
    simpa only [tangentSq] using
      wholeRestartCrossingPrefixWholeTangent_norm_sq_pos
        initial index crossed
  have chargeRate :
      charge =
        min
          (ν.coeff * contactTime * initialMass / 2)
          (ν.coeff * initialMass ^ 3 /
            (48 * weightedInitialMass * tangentSq)) := by
    simpa only [charge, contactTime, initialMass,
      weightedInitialMass, tangentSq] using
      wholeRestartCrossingFiniteAggregateKineticCharge_eq_min_rate
        initial index crossed modes modesNonzero initialMassPos
  have chargeLe : charge ≤ kineticPayment := by
    simpa only [charge, kineticPayment] using
      wholeRestartCrossingFiniteAggregateKineticCharge_le_nextPayment
        initial index crossed modes modesNonzero initialMassPos
  have weightedInitialMassLe :
      weightedInitialMass ≤
        (2 * Real.pi) ^ 2 * wholeGradientMass := by
    simpa only [weightedInitialMass, wholeGradientMass] using
      finiteAggregateWeightedInitialMass_le_wholeGradientMass
        initial index modes
  have tangentSqLe :
      tangentSq ≤
        (2 * ν.coeff / 3) * segmentDualSquarePayment := by
    simpa only [tangentSq, segmentDualSquarePayment] using
      nextContact_wholeTangent_norm_sq_le_segmentDualSquarePayment
        initial index
  have wholeGradientMassNonneg : 0 ≤ wholeGradientMass := by
    unfold wholeGradientMass wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  have segmentDualSquarePaymentNonneg :
      0 ≤ segmentDualSquarePayment := by
    simpa only [segmentDualSquarePayment] using
      wholeRestartSegmentDualSquarePayment_nonneg initial (index + 1)
  have kineticPaymentNonneg : 0 ≤ kineticPayment := by
    simpa only [kineticPayment] using
      wholeRestartNextKineticDissipationPayment_nonneg initial index
  have weightedTangentProductLe :
      weightedInitialMass * tangentSq ≤
        ((2 * Real.pi) ^ 2 * wholeGradientMass) *
          ((2 * ν.coeff / 3) * segmentDualSquarePayment) := by
    exact mul_le_mul weightedInitialMassLe tangentSqLe
      tangentSqPos.le
      (mul_nonneg (sq_nonneg _) wholeGradientMassNonneg)
  have denominatorLe :
      48 * weightedInitialMass * tangentSq ≤
        ν.coeff *
          (32 * (2 * Real.pi) ^ 2 * wholeGradientMass *
            segmentDualSquarePayment) := by
    calc
      48 * weightedInitialMass * tangentSq =
          48 * (weightedInitialMass * tangentSq) := by ring
      _ ≤
          48 *
            (((2 * Real.pi) ^ 2 * wholeGradientMass) *
              ((2 * ν.coeff / 3) * segmentDualSquarePayment)) :=
        mul_le_mul_of_nonneg_left weightedTangentProductLe (by norm_num)
      _ =
          ν.coeff *
            (32 * (2 * Real.pi) ^ 2 * wholeGradientMass *
              segmentDualSquarePayment) := by ring
  by_cases contactRateLe :
      ν.coeff * contactTime * initialMass / 2 ≤
        ν.coeff * initialMass ^ 3 /
          (48 * weightedInitialMass * tangentSq)
  · left
    have chargeEq :
        charge = ν.coeff * contactTime * initialMass / 2 :=
      chargeRate.trans (min_eq_left contactRateLe)
    have contactHalfLe :
        ν.coeff * contactTime * initialMass / 2 ≤ kineticPayment := by
      rw [← chargeEq]
      exact chargeLe
    calc
      ν.coeff * contactTime * initialMass =
          2 * (ν.coeff * contactTime * initialMass / 2) := by ring
      _ ≤ 2 * kineticPayment :=
        mul_le_mul_of_nonneg_left contactHalfLe (by norm_num)
  · right
    have cubicRateLeContact :
        ν.coeff * initialMass ^ 3 /
            (48 * weightedInitialMass * tangentSq) ≤
          ν.coeff * contactTime * initialMass / 2 :=
      le_of_lt (lt_of_not_ge contactRateLe)
    have chargeEq :
        charge =
          ν.coeff * initialMass ^ 3 /
            (48 * weightedInitialMass * tangentSq) :=
      chargeRate.trans (min_eq_right cubicRateLeContact)
    have cubicRateLe :
        ν.coeff * initialMass ^ 3 /
            (48 * weightedInitialMass * tangentSq) ≤
          kineticPayment := by
      rw [← chargeEq]
      exact chargeLe
    have denominatorPos :
        0 < 48 * weightedInitialMass * tangentSq := by positivity
    have numeratorLe :
        ν.coeff * initialMass ^ 3 ≤
          kineticPayment *
            (48 * weightedInitialMass * tangentSq) :=
      (div_le_iff₀ denominatorPos).mp cubicRateLe
    have scaledDenominatorLe :
        kineticPayment *
            (48 * weightedInitialMass * tangentSq) ≤
          kineticPayment *
            (ν.coeff *
              (32 * (2 * Real.pi) ^ 2 * wholeGradientMass *
                segmentDualSquarePayment)) :=
      mul_le_mul_of_nonneg_left denominatorLe kineticPaymentNonneg
    have withViscosity :
        ν.coeff * initialMass ^ 3 ≤
          ν.coeff *
            (32 * (2 * Real.pi) ^ 2 * wholeGradientMass *
              segmentDualSquarePayment * kineticPayment) := by
      calc
        ν.coeff * initialMass ^ 3 ≤
            kineticPayment *
              (48 * weightedInitialMass * tangentSq) := numeratorLe
        _ ≤
            kineticPayment *
              (ν.coeff *
                (32 * (2 * Real.pi) ^ 2 * wholeGradientMass *
                  segmentDualSquarePayment)) := scaledDenominatorLe
        _ =
            ν.coeff *
              (32 * (2 * Real.pi) ^ 2 * wholeGradientMass *
                segmentDualSquarePayment * kineticPayment) := by ring
    exact le_of_mul_le_mul_left withViscosity ν.coeff_pos

/-- The physical rate responsibility carried by one generated aggregate
persistence receipt. -/
def aggregatePhysicalRateObstruction
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    {index radius : ℕ}
    {crossed : wholeRestartHalfCriticalCrossed initial index}
    {budget : ℝ}
    (receipt :
      WholeRestartHighFrequencyAggregatePersistenceReceipt
        initial index radius crossed budget) : Prop :=
  let initialMass :=
    ∑ output ∈ receipt.outputs,
      complexCoordinateAmplitudeSq
        ((run initial index).contact.physicalState output)
  let wholeGradientMass :=
    wholeStateVorticityGradientMass
      (run initial index).contact.physicalState
  let segmentDualSquarePayment :=
    wholeRestartSegmentDualSquarePayment initial (index + 1)
  let kineticPayment :=
    wholeRestartNextKineticDissipationPayment initial index
  ν.coeff * (run initial index).nextContact.time.1 * initialMass ≤
      2 * kineticPayment ∨
    initialMass ^ 3 ≤
      32 * (2 * Real.pi) ^ 2 * wholeGradientMass *
        segmentDualSquarePayment * kineticPayment

theorem aggregatePersistenceReceipt_physicalRateObstruction
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    {index radius : ℕ}
    {crossed : wholeRestartHalfCriticalCrossed initial index}
    {budget : ℝ}
    (receipt :
      WholeRestartHighFrequencyAggregatePersistenceReceipt
        initial index radius crossed budget) :
    aggregatePhysicalRateObstruction receipt := by
  have outputsNonzero :
      ∀ output ∈ receipt.outputs, output ≠ 0 :=
    fun output outputMem =>
      (receipt.outputsGeometry output outputMem).1
  have initialMassPos :
      0 < ∑ output ∈ receipt.outputs,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output) :=
    lt_of_le_of_lt
      (le_max_right budget 0) receipt.initialMassLarge
  unfold aggregatePhysicalRateObstruction
  exact wholeRestartCrossingFiniteAggregate_physicalRateObstruction
    initial index crossed receipt.outputs outputsNonzero initialMassPos

/-- Bounded physical-time accumulation now generates a larger least core,
native nonzero gluing transport, or an actual finite high-frequency receipt
whose remaining rate escape is already expressed entirely in the same
restart's physical gradient, dual-square, and kinetic ledgers. -/
theorem
    elapsedTime_bddAbove_forces_aggregate_physicalRateObstruction
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∀ radius : ℕ, ∀ budget : ℝ,
      ∃ index : ℕ,
        ∃ crossed : wholeRestartHalfCriticalCrossed initial index,
          radius <
              wholeRestartCrossingFiniteCoreRadius initial index crossed ∨
            ((wholeRestartCrossingCompleteSourceGluingNegativeOneState
                  initial index crossed ≠ 0 ∧
                (wholeRestartComponentGluingResidualRow
                      initial (index + 1) ≠ 0 ∨
                  linearResidualTrace
                      wholeRestartComponentGluingResidualTailKeep
                      (wholeRestartComponentGluingResidualTail
                        initial index) 0 ≠ 0) ∧
                0 < wholeRestartCrossingTangentPayment initial index) ∨
              Nonempty
                { receipt :
                    WholeRestartHighFrequencyAggregatePersistenceReceipt
                      initial index radius crossed budget //
                  aggregatePhysicalRateObstruction receipt }) := by
  intro radius budget
  obtain ⟨index, crossed, responsibility⟩ :=
    elapsedTime_bddAbove_forces_aggregate_frequency_persistence_responsibility
      initial elapsedBounded radius budget
  refine ⟨index, crossed, ?_⟩
  rcases responsibility with coreEscapes | gluingOrPersistence
  · exact Or.inl coreEscapes
  rcases gluingOrPersistence with gluing | persistence
  · exact Or.inr (Or.inl gluing)
  obtain ⟨receipt⟩ := persistence
  exact Or.inr (Or.inr
    ⟨⟨receipt,
      aggregatePersistenceReceipt_physicalRateObstruction receipt⟩⟩)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateRateObstruction
end NavierStokes
end SaturationMonoid
