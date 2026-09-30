import H0mework.NavierStokes.Accumulation.PhysicalCompactness
import H0mework.NavierStokes.Galerkin.AmbientNorm

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WholePrefixState

open scoped ENNReal
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration

noncomputable section

variable {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) (length : Nat)

def duration : Real := elapsedTime initial (length + 1)

theorem duration_pos : 0 < duration initial length := by
  exact elapsedTime_strictMono initial (Nat.zero_lt_succ length)

def wholePath : BoundedContinuousFunction (Icc (0 : Real) (duration initial length))
    ComplexVorticityHilbertState :=
  wholeTrajectoryBoundedPath (duration initial length)
    (wholeRestartPrefixPhysicalTrajectory initial (length + 1))
    (wholeRestartPrefixPhysicalTrajectory_continuousOn initial (length + 1))

def stateLimit : SpaceTimeState (duration initial length) :=
  (wholePath initial length).toLp 2 (commonTimeMeasure (duration initial length)) Complex

def transverseLimit : TransverseSpaceTimeState (duration initial length) :=
  wholeTransverseTrajectorySpaceTimePath (duration initial length)
    (wholeRestartPrefixPhysicalTrajectory initial (length + 1))
    (wholeRestartPrefixPhysicalTrajectory_continuousOn initial (length + 1))
    (fun time _ => wholeRestartPrefixPhysicalTrajectory_transverse initial (length + 1) time)

theorem transverse_inclusion :
    transverseSpaceTimeInclusion (duration initial length) (transverseLimit initial length) =
      stateLimit initial length :=
  transverseSpaceTimeInclusion_wholeTransverseTrajectory _ _ _ _

theorem state_eq_wholePath_ae :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      stateLimit initial length time = wholePath initial length time :=
  BoundedContinuousFunction.coeFn_toLp (p := (2 : ℝ≥0∞))
    (μ := commonTimeMeasure (duration initial length)) Complex (wholePath initial length)

theorem transverse_eq_wholePath_ae :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      (transverseLimit initial length time).1 = wholePath initial length time := by
  filter_upwards [transverseSpaceTimeInclusion_coeFn (duration initial length)
    (transverseLimit initial length), state_eq_wholePath_ae initial length] with time inclusion path
  rw [transverse_inclusion] at inclusion
  exact inclusion.symm.trans path

def enstrophyCeiling : Real := 3 * ‖wholePath initial length‖ ^ 2

theorem enstrophyCeiling_nonneg : 0 ≤ enstrophyCeiling initial length := by
  unfold enstrophyCeiling
  positivity

theorem transverse_massBound :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      wholeVorticityEuclideanMass (transverseLimit initial length time).1 ≤
        enstrophyCeiling initial length := by
  filter_upwards [transverse_eq_wholePath_ae initial length] with time equal
  rw [equal]
  apply (wholeVorticityEuclideanMass_le_three_mul_norm_sq _).trans
  unfold enstrophyCeiling
  gcongr
  exact (wholePath initial length).norm_coe_le_norm time

private theorem commonTime_eq_comap (time : Real) :
    commonTimeMeasure time = Measure.comap (Subtype.val : Icc (0 : Real) time → Real) volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

theorem gradient_integrable :
    Integrable (fun time => wholeStateVorticityGradientMass (wholePath initial length time))
      (commonTimeMeasure (duration initial length)) := by
  have massBound : ∀ time ∈ Icc (0 : Real) (duration initial length),
      wholeVorticityEuclideanMass
        (wholeRestartPrefixPhysicalTrajectory initial (length + 1) time) ≤
          3 * ‖wholePath initial length‖ ^ 2 := by
    intro time mem
    change wholeVorticityEuclideanMass (wholePath initial length ⟨time, mem⟩) ≤ _
    apply (wholeVorticityEuclideanMass_le_three_mul_norm_sq _).trans
    gcongr
    exact (wholePath initial length).norm_coe_le_norm _
  rcases wholeRestartPrefixFiniteBandWindowEnergy initial (length + 1) ∅
      (show (0 : Real) ≤ 0 from le_rfl) (duration_pos initial length) le_rfl
      (by simp) 0 le_rfl (by simp) massBound with
    ⟨_energy, _nonneg, _balance, integrable, _gradient, _modulus⟩
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (duration_pos initial length).le,
    integrableOn_iff_comap_subtypeVal measurableSet_Icc,
    ← commonTime_eq_comap] at integrable
  exact integrable

theorem gradient_pointwise_summable :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      Summable fun wave : IntegerWavevector => integerWaveNormSq wave *
        complexCoordinateAmplitudeSq (wholePath initial length time wave) := by
  rw [commonTime_eq_comap]
  exact (ae_restrict_iff_subtype measurableSet_Icc).mp
    (wholeRestartPrefixPhysicalTrajectory_gradientSummable_ae initial (length + 1))

theorem fourierReality_ae :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      FiniteStateFourierReality (wholePath initial length time) := by
  rw [commonTime_eq_comap]
  exact (ae_restrict_iff_subtype measurableSet_Icc).mp
    (wholeRestartPrefixPhysicalTrajectory_fourierReality_ae initial (length + 1))

private theorem waveDensity_integrable (wave : IntegerWavevector) :
    Integrable (fun time => integerWaveNormSq wave * ‖wholePath initial length time wave‖ ^ 2)
      (commonTimeMeasure (duration initial length)) := by
  have continuous : Continuous
      (fun time => integerWaveNormSq wave * ‖wholePath initial length time wave‖ ^ 2) :=
    continuous_const.mul
      (((lp.evalCLM Complex (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous
        |>.comp (wholePath initial length).continuous).norm.pow 2)
  simpa only [integrableOn_univ] using
    (ContinuousOn.integrableOn_compact isCompact_univ continuous.continuousOn)

theorem gradientDensity_eq_integral (wave : IntegerWavevector) :
    wholeSpaceTimeVorticityGradientDensity (duration initial length)
      (stateLimit initial length) wave =
    ∫ time, integerWaveNormSq wave * ‖wholePath initial length time wave‖ ^ 2
      ∂(commonTimeMeasure (duration initial length)) := by
  rw [wholeSpaceTimeVorticityGradientDensity, fixedWaveSpaceTimeState_norm_sq_eq_integral,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [fixedWaveSpaceTimeRestriction_coeFn (duration initial length) wave
      (stateLimit initial length),
    BoundedContinuousFunction.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure (duration initial length)) Complex (wholePath initial length)] with
    time rowEq pathEq
  rw [rowEq]
  change integerWaveNormSq wave * ‖stateLimit initial length time wave‖ ^ 2 = _
  rw [stateLimit, pathEq]

/-- The finite source prefix pays one whole space-time gradient carrier. -/
theorem gradient_summable :
    Summable fun wave : IntegerWavevector => wholeSpaceTimeVorticityGradientDensity
      (duration initial length) (stateLimit initial length) wave := by
  apply summable_of_sum_le
    (wholeSpaceTimeVorticityGradientDensity_nonneg _ (stateLimit initial length))
    (c := ∫ time, wholeStateVorticityGradientMass (wholePath initial length time)
      ∂(commonTimeMeasure (duration initial length)))
  intro waves
  simp_rw [gradientDensity_eq_integral]
  rw [← integral_finsetSum waves (fun wave _ => waveDensity_integrable initial length wave)]
  apply integral_mono_ae
    (integrable_finsetSum _ fun wave _ => waveDensity_integrable initial length wave)
    (gradient_integrable initial length)
  filter_upwards [gradient_pointwise_summable initial length] with time summable
  calc
    _ ≤ ∑ wave ∈ waves, integerWaveNormSq wave *
        complexCoordinateAmplitudeSq (wholePath initial length time wave) := by
      apply Finset.sum_le_sum
      intro wave _
      exact mul_le_mul_of_nonneg_left
        (complexCoordinateVector_norm_sq_le_amplitudeSq _) (integerWaveNormSq_nonneg wave)
    _ ≤ _ := summable.sum_le_tsum waves (fun wave _ =>
      mul_nonneg (integerWaveNormSq_nonneg wave) (complexCoordinateAmplitudeSq_nonneg _))

theorem transverse_gradient_summable :
    Summable fun wave : IntegerWavevector => wholeSpaceTimeVorticityGradientDensity
      (duration initial length)
      (transverseSpaceTimeInclusion (duration initial length) (transverseLimit initial length)) wave := by
  rw [transverse_inclusion]
  exact gradient_summable initial length

theorem transverse_fourierReality_ae :
    ∀ᵐ time ∂(commonTimeMeasure (duration initial length)),
      FiniteStateFourierReality (transverseLimit initial length time).1 := by
  filter_upwards [transverse_eq_wholePath_ae initial length, fourierReality_ae initial length] with
    time equal reality
  exact equal.symm ▸ reality

end
end SaturationMonoid.NavierStokes.WholePrefixState
