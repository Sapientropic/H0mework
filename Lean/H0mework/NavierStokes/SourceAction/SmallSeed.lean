import H0mework.NavierStokes.RecoveryAction.RecoverySmallK
import H0mework.NavierStokes.SourceAction.Limit

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeSmallSeedControl

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMildClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeMildAssembly
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalDualSquareReduction
open NativeRecoveryControlProducer NativeRecoverySmallK

noncomputable section

variable {nu : Viscosity} {Seed : Type} [WholeRestartPhysicalSeed nu Seed] {seed : Seed}

theorem canonical_stage_enstrophy_le {radius : ℕ} (stage : GeneratedWholeRestartCanonicalStage seed radius)
    (small : criticalEnstrophyLatticeConstant * wholeVorticityEuclideanMass (wholeRestartPhysicalState seed) ≤
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2) (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius) (stage.trajectory time.1) ≤
      wholeVorticityEuclideanMass (wholeRestartPhysicalState seed) := by
  have initialLe : finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius) (stage.trajectory 0) ≤
      wholeVorticityEuclideanMass (wholeRestartPhysicalState seed) := by
    rw [stage.initial]
    have same : finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius) (wholeRestartInitialState seed radius) =
        finiteStateVorticityCoefficientEnstrophy (wholeRestartModes radius) (wholeRestartPhysicalState seed) := by
      unfold finiteStateVorticityCoefficientEnstrophy wholeRestartInitialState
      apply Finset.sum_congr rfl
      intro wave inside
      rw [complexSharpSupportProjection_apply, if_pos inside]
    rw [same]
    exact finiteStateVorticityCoefficientEnstrophy_le_wholeMass _ _
  have margin := (mul_le_mul_of_nonneg_left initialLe criticalEnstrophyLatticeConstant_nonneg).trans small
  have result := finiteStateVorticityHalfEnstrophy_le_initial_of_criticalSmall
    (wholeRestartModes radius) (fun _ member => puncturedIntegerWaveFrequencyCube_waveNeg_mem radius member)
    nu.coeff nu.coeff_pos stage.trajectory 0 (wholeRestartDuration seed)
    (fun actual inside => (stage.physical actual inside).1)
    (fun actual inside => (stage.physical actual inside).2.2.2)
    (fun actual inside wave _ => (stage.physical actual inside).2.2.1 wave) margin time.1 time.2
  simp only [finiteStateVorticityHalfEnstrophy] at result
  linarith [result.1]

theorem closure_vorticity_row_tendsto {replay : GeneratedWholeRestartCanonicalReplay seed}
    (closure : GeneratedWholeRestartCriticalClosure replay) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    Tendsto (fun index => (replay.current (closure.weakClosure.subsequence index)).trajectory time.1 wave)
      atTop (𝓝 ((wholeRestartWholeContinuousMildSerrinReceipt closure).wholePath time wave)) := by
  by_cases nonzero : wave ≠ 0
  · have source := (wholeRestartFixedWaveMildHolderReceipt closure wave nonzero).row_full_tendsto
    have evaluated := ((BoundedContinuousFunction.evalCLM ℂ time).continuous.tendsto
      (wholeRestartFixedWaveMildData closure wave nonzero).rowPath).comp source
    change Tendsto (fun index => (replay.current (closure.weakClosure.subsequence index)).trajectory time.1 wave)
      atTop (𝓝 ((wholeRestartFixedWaveMildData closure wave nonzero).rowPath time)) at evaluated
    rw [← wholeRestartWholeMildAssembly_fixedWave_eq closure wave nonzero time] at evaluated
    exact evaluated
  · have atZero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    have zero (index) := ((replay.current (closure.weakClosure.subsequence index)).physical time.1 time.2).2.1 0
      (zero_not_mem_puncturedIntegerWaveFrequencyCube _)
    simp only [zero, (wholeRestartWholeContinuousMildSerrinReceipt closure).wholePath_zero_row time]
    exact tendsto_const_nhds

theorem physical_seed_receipt_mass_le (seed : Seed)
    (small : criticalEnstrophyLatticeConstant * wholeVorticityEuclideanMass (wholeRestartPhysicalState seed) ≤
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2) (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    wholeVorticityEuclideanMass ((generatedWholeRestartPhysicalSeedWholeContinuousMildSerrinReceipt seed).wholePath time) ≤
      wholeVorticityEuclideanMass (wholeRestartPhysicalState seed) := by
  let replay := generatedWholeRestartCanonicalReplay seed
  let closure := generatedWholeRestartCriticalClosure replay
  have continuous : Continuous complexCoordinateAmplitudeSq := by
    unfold complexCoordinateAmplitudeSq
    fun_prop
  have finiteBound (observed : Finset IntegerWavevector) :
      (∑ wave ∈ observed, complexCoordinateAmplitudeSq
        ((generatedWholeRestartPhysicalSeedWholeContinuousMildSerrinReceipt seed).wholePath time wave)) ≤
          wholeVorticityEuclideanMass (wholeRestartPhysicalState seed) := by
    have source := tendsto_finsetSum observed (fun wave _ =>
      (continuous.tendsto _).comp (closure_vorticity_row_tendsto closure wave time))
    apply le_of_tendsto source
    exact Eventually.of_forall fun index =>
      (finiteStateVorticityCoefficientEnstrophy_le_of_supported observed (wholeRestartModes (closure.weakClosure.subsequence index))
        ((replay.current (closure.weakClosure.subsequence index)).trajectory time.1)
        ((replay.current (closure.weakClosure.subsequence index)).physical time.1 time.2).2.1).trans
        (canonical_stage_enstrophy_le _ small time)
  have result := Real.tsum_le_of_sum_le (fun wave => complexCoordinateAmplitudeSq_nonneg
    ((generatedWholeRestartPhysicalSeedWholeContinuousMildSerrinReceipt seed).wholePath time wave)) finiteBound
  simpa only [wholeVorticityEuclideanMass, vorticityRowAmplitude_sq,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using result

theorem source_next_contact_halfCritical (initial : GeneratedWholeRestartCurrent nu)
    (small : smallK (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial)) :
    criticalEnstrophyLatticeConstant *
      wholeVorticityEuclideanMass (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).contact.physicalState ≤
        (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
  let slice := sourceGeneratedNativeTemporalPositiveTimeH1Slice initial
  let seed := slice.toWholeRestartPhysicalSeed (ν := nu)
  let next := sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial
  have initialMargin := source_next_initial_halfCritical initial small
  have fullMargin : criticalEnstrophyLatticeConstant * wholeVorticityEuclideanMass (wholeRestartPhysicalState seed) ≤
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    change criticalEnstrophyLatticeConstant * wholeVorticityEuclideanMass next.initialState ≤ _
    nlinarith [sq_nonneg nu.coeff, sq_nonneg (2 * Real.pi)]
  have paid := physical_seed_receipt_mass_le seed fullMargin next.contact.time
  exact (mul_le_mul_of_nonneg_left paid criticalEnstrophyLatticeConstant_nonneg).trans initialMargin

theorem source_next_unbounded (initial : GeneratedWholeRestartCurrent nu)
    (small : smallK (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial)) :
    ¬ BddAbove (Set.range (elapsedTime (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial))) :=
  elapsedTime_not_bddAbove_of_initial_halfCriticalMargin _ (source_next_contact_halfCritical initial small)

end
end SaturationMonoid.NavierStokes.NativeSmallSeedControl
