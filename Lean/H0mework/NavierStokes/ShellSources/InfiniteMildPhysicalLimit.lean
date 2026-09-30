import H0mework.NavierStokes.ShellSources.InfiniteMildDuhamel
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeViscousNegativeOne

/-!
# Physical closure of the source-generated infinite mild state

This module records the zero-mean, transverse, and Fourier-real laws that
were present on every actual punctured Galerkin path but were not yet exposed
on the common whole-space mild limit and its initial trace.  Each law is
passed along the receipt's own whole convergence; none is accepted as a
target premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildPhysicalLimit

open scoped BigOperators ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCriticalPathCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellClosedNonlinearWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellCriticalSerrinWeakLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne

noncomputable section

/-! ## Physical laws on the actual whole limit -/

/-- Coordinatewise conjugation lifted continuously to one fixed-wave
time-`L²` carrier. -/
def fixedWaveSpaceTimeConjugation
    (requestedTime : ℝ) :
    FixedWaveSpaceTimeState requestedTime →L[ℝ]
      FixedWaveSpaceTimeState requestedTime :=
  (starL' ℝ :
      ComplexCoordinateVector ≃L[ℝ] ComplexCoordinateVector)
    |>.toContinuousLinearMap
    |>.compLpL 2 (commonTimeMeasure requestedTime)

theorem fixedWaveSpaceTimeConjugation_coeFn
    (requestedTime : ℝ)
    (row : FixedWaveSpaceTimeState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      fixedWaveSpaceTimeConjugation requestedTime row time =
        vectorConj (row time) := by
  filter_upwards [
    (starL' ℝ :
      ComplexCoordinateVector ≃L[ℝ] ComplexCoordinateVector)
      |>.toContinuousLinearMap
      |>.coeFn_compLpL row] with time rowEq
  rw [fixedWaveSpaceTimeConjugation, rowEq]
  exact star_complexCoordinateVector_eq_vectorConj _

/--
The zero Fourier row vanishes in the same whole space-time limit carried by
the infinite mild receipt.
-/
theorem InfiniteMildDuhamelForcingReceipt.stateLimit_zero_row
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    fixedWaveSpaceTimeRestriction requestedTime 0 receipt.stateLimit = 0 := by
  have approximantZero :
      ∀ index : ℕ,
        fixedWaveSpaceTimeRestriction requestedTime 0
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence index)) =
          0 := by
    intro index
    apply MeasureTheory.Lp.ext
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn requestedTime 0
        (puncturedCanonicalCriticalSpaceTimePath
          lineage ν θ θLtOne criticalMargin
          requestedTime requestedTimePos
          (receipt.subsequence index)),
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := commonTimeMeasure requestedTime)
        ℂ
        (generatedWholeBoundedPath θLtOne requestedTimePos
          (puncturedCanonicalCriticalScalePath
            lineage ν θ criticalMargin
            (receipt.subsequence index))),
      MeasureTheory.Lp.coeFn_zero
        ComplexCoordinateVector 2
        (commonTimeMeasure requestedTime)] with
        time rowEq wholeEq zeroEq
    rw [rowEq]
    simp only [puncturedCanonicalCriticalSpaceTimePath,
      generatedCriticalSpaceTimePath]
    rw [wholeEq, zeroEq]
    simpa [generatedWholeBoundedPath, generatedWholeTrajectory,
      puncturedCanonicalCriticalTrajectory] using
      (puncturedCanonicalCriticalTrajectory_physicalProperties
        lineage ν θ θLtOne criticalMargin requestedTime
        requestedTimePos (receipt.subsequence index)
        time.1 time.2).2.1 0
          (zero_not_mem_puncturedIntegerWaveFrequencyCube
            (receipt.subsequence index))
  have rowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction requestedTime 0
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence index)))
        atTop
        (𝓝
          (fixedWaveSpaceTimeRestriction
            requestedTime 0 receipt.stateLimit)) :=
    (fixedWaveSpaceTimeRestriction requestedTime 0).continuous.tendsto
      receipt.stateLimit |>.comp receipt.state_tendsto
  have zeroTendsto :
      Tendsto
        (fun _ : ℕ =>
          (0 : FixedWaveSpaceTimeState requestedTime))
        atTop (𝓝 0) :=
    tendsto_const_nhds
  exact
    tendsto_nhds_unique rowTendsto <| by
      simpa only [approximantZero] using zeroTendsto

/--
Every pair of opposite Fourier rows of the actual whole space-time limit
satisfies the real-field conjugation law in the time-`L²` carrier.
-/
theorem InfiniteMildDuhamelForcingReceipt.stateLimit_fourierReality
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    fixedWaveSpaceTimeRestriction
        requestedTime (waveNeg wave) receipt.stateLimit =
      fixedWaveSpaceTimeConjugation requestedTime
        (fixedWaveSpaceTimeRestriction
          requestedTime wave receipt.stateLimit) := by
  have approximantReality :
      ∀ index : ℕ,
        fixedWaveSpaceTimeRestriction requestedTime (waveNeg wave)
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence index)) =
          fixedWaveSpaceTimeConjugation requestedTime
            (fixedWaveSpaceTimeRestriction requestedTime wave
              (puncturedCanonicalCriticalSpaceTimePath
                lineage ν θ θLtOne criticalMargin
                requestedTime requestedTimePos
                (receipt.subsequence index))) := by
    intro index
    apply MeasureTheory.Lp.ext
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime (waveNeg wave)
        (puncturedCanonicalCriticalSpaceTimePath
          lineage ν θ θLtOne criticalMargin
          requestedTime requestedTimePos
          (receipt.subsequence index)),
      fixedWaveSpaceTimeRestriction_coeFn requestedTime wave
        (puncturedCanonicalCriticalSpaceTimePath
          lineage ν θ θLtOne criticalMargin
          requestedTime requestedTimePos
          (receipt.subsequence index)),
      fixedWaveSpaceTimeConjugation_coeFn requestedTime
        (fixedWaveSpaceTimeRestriction requestedTime wave
          (puncturedCanonicalCriticalSpaceTimePath
            lineage ν θ θLtOne criticalMargin
            requestedTime requestedTimePos
            (receipt.subsequence index))),
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := commonTimeMeasure requestedTime)
        ℂ
        (generatedWholeBoundedPath θLtOne requestedTimePos
          (puncturedCanonicalCriticalScalePath
            lineage ν θ criticalMargin
            (receipt.subsequence index)))] with
        time negRowEq rowEq conjugateEq wholeEq
    rw [negRowEq, conjugateEq]
    change
      ((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ)
        (generatedWholeBoundedPath θLtOne requestedTimePos
          (puncturedCanonicalCriticalScalePath
            lineage ν θ criticalMargin
            (receipt.subsequence index)))) time (waveNeg wave) =
        vectorConj
          ((fixedWaveSpaceTimeRestriction requestedTime wave
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence index))) time)
    rw [rowEq]
    change
      ((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ)
        (generatedWholeBoundedPath θLtOne requestedTimePos
          (puncturedCanonicalCriticalScalePath
            lineage ν θ criticalMargin
            (receipt.subsequence index)))) time (waveNeg wave) =
        vectorConj
          (((BoundedContinuousFunction.toLp 2
            (commonTimeMeasure requestedTime) ℂ)
            (generatedWholeBoundedPath θLtOne requestedTimePos
              (puncturedCanonicalCriticalScalePath
                lineage ν θ criticalMargin
                (receipt.subsequence index)))) time wave)
    rw [wholeEq]
    exact
      (puncturedCanonicalCriticalTrajectory_physicalProperties
        lineage ν θ θLtOne criticalMargin requestedTime
        requestedTimePos (receipt.subsequence index)
        time.1 time.2).2.2.2 wave
  have negativeRowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction requestedTime (waveNeg wave)
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence index)))
        atTop
        (𝓝
          (fixedWaveSpaceTimeRestriction requestedTime
            (waveNeg wave) receipt.stateLimit)) :=
    (fixedWaveSpaceTimeRestriction requestedTime
      (waveNeg wave)).continuous.tendsto receipt.stateLimit
        |>.comp receipt.state_tendsto
  have positiveRowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction requestedTime wave
            (puncturedCanonicalCriticalSpaceTimePath
              lineage ν θ θLtOne criticalMargin
              requestedTime requestedTimePos
              (receipt.subsequence index)))
        atTop
        (𝓝
          (fixedWaveSpaceTimeRestriction
            requestedTime wave receipt.stateLimit)) :=
    (fixedWaveSpaceTimeRestriction requestedTime wave).continuous.tendsto
      receipt.stateLimit |>.comp receipt.state_tendsto
  have conjugateRowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeConjugation requestedTime
            (fixedWaveSpaceTimeRestriction requestedTime wave
              (puncturedCanonicalCriticalSpaceTimePath
                lineage ν θ θLtOne criticalMargin
                requestedTime requestedTimePos
                (receipt.subsequence index))))
        atTop
        (𝓝
          (fixedWaveSpaceTimeConjugation requestedTime
            (fixedWaveSpaceTimeRestriction
              requestedTime wave receipt.stateLimit))) :=
    (fixedWaveSpaceTimeConjugation requestedTime).continuous.tendsto
      (fixedWaveSpaceTimeRestriction requestedTime wave receipt.stateLimit)
        |>.comp positiveRowTendsto
  exact
    tendsto_nhds_unique negativeRowTendsto <| by
      simpa only [approximantReality] using conjugateRowTendsto

/-! ## Physical laws on the generated initial trace -/

@[simp] theorem InfiniteMildDuhamelForcingReceipt.initialState_zero_row
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    receipt.initialState 0 = 0 := by
  have rowTendsto :
      Tendsto
        (fun radius =>
          puncturedCanonicalInitialState lineage radius 0)
        atTop
        (𝓝 (receipt.initialState 0)) :=
    ((lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 0).continuous.tendsto receipt.initialState).comp
        receipt.initial_tendsto
  have approximantZero :
      (fun radius =>
        puncturedCanonicalInitialState lineage radius 0) =
        fun _ : ℕ => (0 : ComplexCoordinateVector) := by
    funext radius
    exact
      puncturedCanonicalInitialState_supported lineage radius 0
        (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
  exact
    tendsto_nhds_unique rowTendsto <| by
      simpa only [approximantZero] using
        (tendsto_const_nhds :
          Tendsto
            (fun _ : ℕ => (0 : ComplexCoordinateVector))
            atTop (𝓝 0))

theorem InfiniteMildDuhamelForcingReceipt.initialState_transverse
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ∀ wave : IntegerWavevector,
      complexWavevector wave ⬝ᵥ receipt.initialState wave = 0 := by
  intro wave
  have rowTendsto :
      Tendsto
        (fun radius =>
          puncturedCanonicalInitialState lineage radius wave)
        atTop
        (𝓝 (receipt.initialState wave)) :=
    ((lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.tendsto receipt.initialState).comp
        receipt.initial_tendsto
  have dotTendsto :
      Tendsto
        (fun radius =>
          complexWavevector wave ⬝ᵥ
            puncturedCanonicalInitialState lineage radius wave)
        atTop
        (𝓝
          (complexWavevector wave ⬝ᵥ
            receipt.initialState wave)) :=
    ((continuous_const.dotProduct continuous_id).tendsto
      (receipt.initialState wave)).comp rowTendsto
  have approximantTransverse :
      (fun radius =>
        complexWavevector wave ⬝ᵥ
          puncturedCanonicalInitialState lineage radius wave) =
        fun _ : ℕ => (0 : ℂ) := by
    funext radius
    by_cases waveMem :
        wave ∈ puncturedIntegerWaveFrequencyCube radius
    · exact
        puncturedCanonicalInitialState_transverse
          lineage radius wave waveMem
    · rw [puncturedCanonicalInitialState_supported
        lineage radius wave waveMem]
      simp
  exact
    tendsto_nhds_unique dotTendsto <| by
      simpa only [approximantTransverse] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

theorem InfiniteMildDuhamelForcingReceipt.initialState_fourierReality
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    FiniteStateFourierReality receipt.initialState := by
  intro wave
  have rowTendsto :
      ∀ actualWave : IntegerWavevector,
        Tendsto
          (fun radius =>
            puncturedCanonicalInitialState
              lineage radius actualWave)
          atTop
          (𝓝 (receipt.initialState actualWave)) := by
    intro actualWave
    exact
      ((lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 actualWave).continuous.tendsto receipt.initialState).comp
          receipt.initial_tendsto
  have vectorConjContinuous :
      Continuous
        (fun vector : ComplexCoordinateVector =>
          vectorConj vector) := by
    apply continuous_pi
    intro coordinate
    exact
      Complex.continuous_conj.comp
        (continuous_apply coordinate)
  have conjugateTendsto :
      Tendsto
        (fun radius =>
          vectorConj
            (puncturedCanonicalInitialState
              lineage radius wave))
        atTop
        (𝓝 (vectorConj (receipt.initialState wave))) :=
    (vectorConjContinuous.tendsto
      (receipt.initialState wave)).comp (rowTendsto wave)
  have negativeWaveTendsto :
      Tendsto
        (fun radius =>
          puncturedCanonicalInitialState
            lineage radius (waveNeg wave))
        atTop
        (𝓝 (vectorConj (receipt.initialState wave))) := by
    have approximantReality :
        (fun radius =>
          puncturedCanonicalInitialState
            lineage radius (waveNeg wave)) =
          (fun radius =>
            vectorConj
              (puncturedCanonicalInitialState
                lineage radius wave)) := by
      funext radius
      exact
        puncturedCanonicalInitialState_reality
          lineage radius wave
    rw [approximantReality]
    exact conjugateTendsto
  exact
    tendsto_nhds_unique
      (rowTendsto (waveNeg wave))
      negativeWaveTendsto

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildPhysicalLimit
end NavierStokes
end SaturationMonoid
