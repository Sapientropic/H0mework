import H0mework.NavierStokes.RecoveryAction.RecoveryPhysical
import H0mework.NavierStokes.Restart.HalfCriticalDualSquareReduction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoverySmallK

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeRecoveryControlProducer

noncomputable section

variable {nu : Viscosity}

def smallK (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) : Prop :=
  criticalEnstrophyLatticeConstant * (2 * kineticAllowance ledger) ≤
    (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2

theorem finite_late_enstrophy_le (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (small : smallK ledger) (radius : ℕ) (time : ℝ) (late : time ∈ Icc (1 / 2 : ℝ) 1) :
    finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory time) ≤ 2 * kineticAllowance ledger := by
  obtain ⟨start, startInside, startBound⟩ := exists_low_enstrophy_time ledger radius
    (left := 0) (right := 1 / 2) le_rfl (by norm_num) (by norm_num)
  have low : finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory start) ≤ 2 * kineticAllowance ledger := by
    simp only [bandCeiling, sub_zero, div_eq_mul_inv] at startBound
    linarith
  have physical (actual : ℝ) (inside : actual ∈ Icc start 1) :=
    (ledger.family.stage radius).physical actual ⟨startInside.1.trans inside.1, inside.2⟩
  have margin : criticalEnstrophyLatticeConstant *
      finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius)
        ((ledger.family.stage radius).trajectory start) ≤ nu.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    have bounded := (mul_le_mul_of_nonneg_left low criticalEnstrophyLatticeConstant_nonneg).trans small
    nlinarith [sq_nonneg nu.coeff, sq_nonneg (2 * Real.pi)]
  have barrier := finiteStateVorticityHalfEnstrophy_le_initial_of_criticalSmall
    (wholeRestartModes radius) (fun _ member => puncturedIntegerWaveFrequencyCube_waveNeg_mem radius member)
    nu.coeff nu.coeff_pos (ledger.family.stage radius).trajectory start 1
    (fun actual inside => (physical actual inside).1)
    (fun actual inside => (physical actual inside).2.2.2)
    (fun actual inside wave _ => (physical actual inside).2.2.1 wave) margin
    time ⟨startInside.2.trans late.1, late.2⟩
  simp only [finiteStateVorticityHalfEnstrophy] at barrier
  linarith [barrier.1]

theorem wholeMild_late_curl_bound
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (small : smallK ledger) (time : Icc (0 : ℝ) 1) (late : (1 / 2 : ℝ) ≤ time.1) :
    (Summable fun wave => complexCoordinateAmplitudeSq (fourierCurlCoefficient wave (receipt.wholePath time wave))) ∧
      (∑' wave, complexCoordinateAmplitudeSq (fourierCurlCoefficient wave (receipt.wholePath time wave))) ≤
        2 * kineticAllowance ledger := by
  have rows (wave : IntegerWavevector) : Tendsto (fun index =>
      (ledger.family.stage (receipt.core.subsequence index)).trajectory time.1 wave) atTop
      (𝓝 (fourierCurlCoefficient wave (receipt.wholePath time wave))) := by
    have continuous : Continuous (fourierCurlCoefficient wave) := by
      unfold fourierCurlCoefficient
      fun_prop
    have source := continuous.tendsto _ |>.comp (endpoint_velocity_row_tendsto ledger receipt.core time wave)
    rw [← receipt.wholePath_apply] at source
    have same (index) : fourierCurlCoefficient wave
        (finiteStateVelocityCoefficient ((ledger.family.stage (receipt.core.subsequence index)).trajectory time.1) wave) =
        (ledger.family.stage (receipt.core.subsequence index)).trajectory time.1 wave := by
      have physical := (ledger.family.stage (receipt.core.subsequence index)).physical time.1 time.2
      by_cases nonzero : wave ≠ 0
      · exact fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse wave _ nonzero (physical.2.2.1 wave)
      · have atZero : wave = 0 := not_ne_iff.mp nonzero
        subst wave
        rw [physical.2.1 0 (zero_not_mem_puncturedIntegerWaveFrequencyCube _)]
        simp [finiteStateVelocityCoefficient, fourierCurlCoefficient]
    simpa only [Function.comp_def, same] using source
  have finiteBound (observed : Finset IntegerWavevector) :
      (∑ wave ∈ observed, complexCoordinateAmplitudeSq (fourierCurlCoefficient wave (receipt.wholePath time wave))) ≤
        2 * kineticAllowance ledger := by
    have continuous : Continuous complexCoordinateAmplitudeSq := by
      unfold complexCoordinateAmplitudeSq
      fun_prop
    have source := tendsto_finsetSum observed (fun wave _ => (continuous.tendsto _).comp (rows wave))
    apply le_of_tendsto source
    exact Eventually.of_forall fun index =>
      (finiteStateVorticityCoefficientEnstrophy_le_of_supported observed (wholeRestartModes (receipt.core.subsequence index))
        ((ledger.family.stage (receipt.core.subsequence index)).trajectory time.1)
        ((ledger.family.stage (receipt.core.subsequence index)).physical time.1 time.2).2.1).trans
        (finite_late_enstrophy_le ledger small (receipt.core.subsequence index) time.1 ⟨late, time.2.2⟩)
  exact ⟨summable_of_sum_le (fun _ => complexCoordinateAmplitudeSq_nonneg _) finiteBound,
    Real.tsum_le_of_sum_le (fun _ => complexCoordinateAmplitudeSq_nonneg _) finiteBound⟩

theorem chosenH1_mass_le
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (small : smallK ledger) :
    wholeVorticityEuclideanMass (generatedPositiveVelocityH1SliceOfWholeMildReceipt receipt).vorticityState ≤
      2 * kineticAllowance ledger := by
  let slice := generatedPositiveVelocityH1SliceOfWholeMildReceipt receipt
  have paid := (wholeMild_late_curl_bound ledger receipt small slice.time slice.time_half_lt.le).2
  simpa only [wholeVorticityEuclideanMass, vorticityRowAmplitude_sq, GeneratedPositiveVelocityH1Slice.vorticityState,
    wholeVelocityCurlState_apply, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid

theorem source_next_initial_halfCritical (initial : GeneratedWholeRestartCurrent nu)
    (small : smallK (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial)) :
    criticalEnstrophyLatticeConstant *
      wholeVorticityEuclideanMass (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).initialState ≤
        (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
  have paid := chosenH1_mass_le (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial)
    (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) small
  exact (mul_le_mul_of_nonneg_left paid criticalEnstrophyLatticeConstant_nonneg).trans small

end
end SaturationMonoid.NavierStokes.NativeRecoverySmallK
