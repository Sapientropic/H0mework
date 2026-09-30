import H0mework.NavierStokes.Crossing.FrequencySupportExhaustion
import H0mework.NavierStokes.Crossing.HighFrequencyAggregateCharge

/-!
# Source-generated aggregate high-frequency responsibility

Finite physical-time accumulation makes the actual whole-vorticity tail
outside every fixed native cube unbounded.  This module consumes that tail
before coefficient quotient: it generates a finite nonzero-frequency family
with arbitrarily large aggregate initial mass and aligns every member with
the same crossing's own pair-support complement whenever the least core has
not already escaped the requested radius.

The faithful-zero branch then applies the finite aggregate derivative before
choosing time.  Hence all rows share one actual outgoing receipt and one
generated positive time.  The alternative is a larger native core or the
already generated nonzero gluing transport; no branch, output family, mass
bound, local time, or charge is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateResponsibility

open scoped BigOperators Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateCharge
open AffineRelaxation

noncomputable section

/-- The source-native sharp complement is exactly the nonnegative coefficient
`tsum` outside that same finite inventory. -/
theorem restartPhysicalHighFrequencyTailMass_eq_tsum_compl
    { ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    restartPhysicalHighFrequencyTailMass initial index radius =
      ∑' wave : IntegerWavevector,
        if wave ∈ wholeRestartModes radius then 0
        else
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState wave) := by
  unfold restartPhysicalHighFrequencyTailMass wholeVorticityEuclideanMass
  apply tsum_congr
  intro wave
  by_cases waveMem : wave ∈ wholeRestartModes radius
  · simp [complexSharpSupportProjection_apply, waveMem,
      vorticityRowAmplitude_sq, complexCoordinateVectorNormSq]
  · simp [complexSharpSupportProjection_apply, waveMem,
      vorticityRowAmplitude_sq, complexCoordinateVectorNormSq,
      complexCoordinateAmplitudeSq]

/-- A large actual sharp-complement mass generates a finite family of
nonzero frequencies outside the same native cube carrying more than the
requested aggregate coefficient mass. -/
theorem restartPhysicalHighFrequencyTailMass_generates_finite_modes_above
    { ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ)
    (budget : ℝ)
    (tailLarge :
      budget < restartPhysicalHighFrequencyTailMass initial index radius) :
    ∃ outputs : Finset IntegerWavevector,
      (∀ output ∈ outputs,
        output ≠ 0 ∧ output ∉ wholeRestartModes radius) ∧
      budget < ∑ output ∈ outputs,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output) := by
  classical
  let summand : IntegerWavevector → ℝ := fun wave =>
    if wave ∈ wholeRestartModes radius then 0
    else
      complexCoordinateAmplitudeSq
        ((run initial index).contact.physicalState wave)
  have tsumLarge : budget < ∑' wave, summand wave := by
    simpa [summand,
      restartPhysicalHighFrequencyTailMass_eq_tsum_compl] using tailLarge
  have existsPartial :
      ∃ candidates : Finset IntegerWavevector,
        budget < ∑ wave ∈ candidates, summand wave := by
    by_contra noPartial
    simp only [not_exists, not_lt] at noPartial
    have tsumLe : (∑' wave, summand wave) ≤ budget := by
      apply Real.tsum_le_of_sum_le
      · intro wave
        dsimp [summand]
        split
        · exact le_rfl
        · exact complexCoordinateAmplitudeSq_nonneg _
      · exact noPartial
    exact (not_lt_of_ge tsumLe) tsumLarge
  obtain ⟨candidates, candidatesLarge⟩ := existsPartial
  let outputs := candidates.filter fun wave =>
    wave ≠ 0 ∧ wave ∉ wholeRestartModes radius
  refine ⟨outputs, ?_, ?_⟩
  · intro output outputMem
    exact (Finset.mem_filter.mp outputMem).2
  · calc
      budget < ∑ wave ∈ candidates, summand wave := candidatesLarge
      _ = ∑ output ∈ outputs,
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output) := by
        unfold outputs
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro wave waveMem
        by_cases waveZero : wave = 0
        · subst wave
          simp [summand,
            (run initial index).contact.physicalState_zero,
            complexCoordinateVectorNormSq]
        · by_cases waveIn : wave ∈ wholeRestartModes radius
          · simp [summand, waveZero, waveIn]
          · simp [summand, waveZero, waveIn]

/-- Finite physical-time accumulation generates arbitrarily large
pre-quotient high-frequency aggregate responsibility on the actual restart
chain.  At each requested radius and mass budget, the source itself exhausts:

* a larger least crossing core;
* nonzero gluing carried by the native next/trace process; or
* faithful-zero aggregate rows outside the same crossing pair support,
  charged at one common positive time to the same successor kinetic payment
  while retaining every viscous frequency multiplier in the exact drop.
-/
theorem elapsedTime_bddAbove_forces_aggregate_frequency_responsibility
    { ν : Viscosity}
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
              (wholeRestartCrossingCompleteSourceGluingNegativeOneState
                    initial index crossed = 0 ∧
                ∃ outputs : Finset IntegerWavevector,
                  (∀ output ∈ outputs,
                    output ≠ 0 ∧
                      2 * radius < integerWaveCoordinateRadius output ∧
                      output ∉ finiteVorticityPairOutputSupport
                        (wholeRestartCrossingFiniteCoreModes
                          initial index crossed)) ∧
                  max budget 0 <
                    ∑ output ∈ outputs,
                      complexCoordinateAmplitudeSq
                        ((run initial index).contact.physicalState output) ∧
                  ∃ actual :
                      Ioo (0 : ℝ) (run initial index).nextContact.time.1,
                    let initialMass :=
                      ∑ output ∈ outputs,
                        complexCoordinateAmplitudeSq
                          ((run initial index).contact.physicalState output)
                    let weightedInitialMass :=
                      ∑ output ∈ outputs,
                        integerWaveViscousMultiplier output *
                          complexCoordinateAmplitudeSq
                            ((run initial index).contact.physicalState output)
                    let charge := ν.coeff * actual.1 * initialMass
                    0 < charge ∧
                      charge ≤
                        wholeRestartNextKineticDissipationPayment
                          initial index ∧
                      ν.coeff * actual.1 * weightedInitialMass <
                        initialMass -
                          ∑ output ∈ outputs,
                            complexCoordinateAmplitudeSq
                              ((run initial index).nextContact.prefixReceipt.wholePath
                                ⟨actual.1, actual.2.1.le,
                                  actual.2.2.le⟩ output))) := by
  classical
  intro radius budget
  have tailUnbounded :=
    elapsedTime_bddAbove_forces_highFrequencyTail_unbounded
      initial elapsedBounded (2 * radius)
  obtain ⟨tail, ⟨index, rfl⟩, tailLarge⟩ :=
    not_bddAbove_iff.1 tailUnbounded (max budget 0)
  let crossed : wholeRestartHalfCriticalCrossed initial index :=
    elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      initial elapsedBounded index
  by_cases coreEscapes :
      radius < wholeRestartCrossingFiniteCoreRadius initial index crossed
  · exact ⟨index, crossed, Or.inl coreEscapes⟩
  · have coreRadiusLe :
        wholeRestartCrossingFiniteCoreRadius initial index crossed ≤ radius :=
      le_of_not_gt coreEscapes
    by_cases gluingZero :
        wholeRestartCrossingCompleteSourceGluingNegativeOneState
          initial index crossed = 0
    · obtain ⟨outputs, outputsOutside, outputsLarge⟩ :=
        restartPhysicalHighFrequencyTailMass_generates_finite_modes_above
          initial index (2 * radius) (max budget 0) tailLarge
      have outputsGeometry :
          ∀ output ∈ outputs,
            output ≠ 0 ∧
              2 * radius < integerWaveCoordinateRadius output ∧
              output ∉ finiteVorticityPairOutputSupport
                (wholeRestartCrossingFiniteCoreModes
                  initial index crossed) := by
        intro output outputMem
        have outputNonzero := (outputsOutside output outputMem).1
        have outputOutside := (outputsOutside output outputMem).2
        have outputRadiusLarge :
            2 * radius < integerWaveCoordinateRadius output := by
          apply lt_of_not_ge
          intro outputRadiusLe
          apply outputOutside
          have outputInCube :
              output ∈ integerWaveFrequencyCube (2 * radius) :=
            integerWave_mem_frequencyCube_of_radius_le
              output (2 * radius) outputRadiusLe
          simpa [wholeRestartModes,
            puncturedIntegerWaveFrequencyCube] using
            (Finset.mem_erase.mpr ⟨outputNonzero, outputInCube⟩)
        have outputNotMem :
            output ∉ finiteVorticityPairOutputSupport
              (wholeRestartCrossingFiniteCoreModes
                initial index crossed) := by
          intro outputMem
          have outputInOwnDoubledCube :
              output ∈ integerWaveFrequencyCube
                (2 * wholeRestartCrossingFiniteCoreRadius
                  initial index crossed) := by
            apply
              finiteVorticityPairOutputSupport_puncturedCube_subset_doubledCube
                (wholeRestartCrossingFiniteCoreRadius
                  initial index crossed)
            simpa [wholeRestartCrossingFiniteCoreModes,
              wholeRestartModes] using outputMem
          have doubledRadiusLe :
              2 * wholeRestartCrossingFiniteCoreRadius
                    initial index crossed ≤
                2 * radius :=
            Nat.mul_le_mul_left 2 coreRadiusLe
          have outputInBoundedCube :
              output ∈ integerWaveFrequencyCube (2 * radius) :=
            integerWaveFrequencyCube_mono
              doubledRadiusLe outputInOwnDoubledCube
          apply outputOutside
          simpa [wholeRestartModes,
            puncturedIntegerWaveFrequencyCube] using
            (Finset.mem_erase.mpr
              ⟨outputNonzero, outputInBoundedCube⟩)
        exact ⟨outputNonzero, outputRadiusLarge, outputNotMem⟩
      have initialMassPos :
          0 < ∑ output ∈ outputs,
            complexCoordinateAmplitudeSq
              ((run initial index).contact.physicalState output) :=
        lt_of_le_of_lt (le_max_right budget 0) outputsLarge
      obtain ⟨actual, aggregateCharge⟩ :=
        wholeRestartCrossingActualWholeFiniteAmplitudeSq_generates_aggregateKineticCharge_of_gluing_zero
          initial index crossed gluingZero outputs
          (fun output outputMem =>
            (outputsGeometry output outputMem).2.2)
          (fun output outputMem =>
            (outputsGeometry output outputMem).1)
          initialMassPos
      exact
        ⟨index, crossed, Or.inr (Or.inr
          ⟨gluingZero, outputs, outputsGeometry, outputsLarge,
            actual, aggregateCharge⟩)⟩
    · have nativeNonzero :
          wholeRestartComponentGluingResidualRow initial index ≠ 0 :=
        (wholeRestartComponentGluingResidualRow_nonzero_iff_negativeOne
          initial index crossed).2 gluingZero
      exact
        ⟨index, crossed, Or.inr (Or.inl
          ⟨gluingZero,
            wholeRestartComponentGluingResidual_nonzero_next_or_trace
              initial index nativeNonzero,
            wholeRestartCrossingTangentPayment_pos_of_crossed
              initial index crossed⟩)⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateResponsibility
end NavierStokes
end SaturationMonoid
