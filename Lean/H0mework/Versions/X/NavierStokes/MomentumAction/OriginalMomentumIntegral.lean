import H0mework.Versions.X.NavierStokes.MomentumAction.ReceiptMomentumIntegral
import H0mework.Versions.X.NavierStokes.SourceAction.ReceiptProfile
import H0mework.Versions.X.NavierStokes.NormControl.Splice
import H0mework.NavierStokes.MacroRuntime.GlobalAbsoluteVelocity
import H0mework.NavierStokes.PhysicalReadout.EndpointVelocity

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalMomentumIntegral

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open NativeEndpointVelocityCarrier NativeStressSource NativeTimeJetCarrier NativeFullOrderTime NativeReceiptTimeProfile

noncomputable section

variable {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
  (bounded : BddAbove (range (elapsedTime initial)))

include bounded in
theorem accumulation_pos : 0 < wholeRestartVelocityAccumulationTime initial := by
  simpa only [elapsedTime_zero] using elapsedTime_lt_wholeRestartVelocityAccumulationTime initial bounded 0

def velocity (time : ℝ) : WholeRestartVelocityEndpointState :=
  sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice initial bounded
    (projIcc (0 : ℝ) (wholeRestartVelocityAccumulationTime initial + 1)
      (by linarith [accumulation_pos initial bounded]) time)

theorem velocity_norm_le (time : ℝ) :
    ‖velocity initial bounded time‖ ≤ ‖puncturedWholeVelocityEuclideanState initial.initialState‖ :=
  NativeNormControl.splice_velocity_norm_le_initial initial bounded _

theorem row_continuous (wave : IntegerWavevector) : Continuous fun time => wholeVelocity (velocity initial bounded time) wave := by
  by_cases nonzero : wave ≠ 0
  · have source := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Coordinate => ℂ)).continuous.comp
      ((sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_coordinate_continuous
        initial bounded ⟨wave, nonzero⟩).comp (continuous_projIcc
          (a := 0) (b := wholeRestartVelocityAccumulationTime initial + 1)
          (h := by linarith [accumulation_pos initial bounded])))
    convert source using 1
    funext time coordinate
    exact wholeVelocity_nonzero _ ⟨wave, nonzero⟩ coordinate
  · have atZero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simpa only [wholeVelocity_zero] using continuous_const (X := ℝ) (y := (0 : ComplexCoordinateVector))

theorem velocity_eq_prefix (length : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (WholePrefixState.duration initial length)) :
    velocity initial bounded time = receiptVelocity (WholePrefixReceipt.receipt initial length) time := by
  have before : time < wholeRestartVelocityAccumulationTime initial :=
    inside.2.trans_lt (elapsedTime_lt_wholeRestartVelocityAccumulationTime initial bounded (length + 1))
  have wholeInside : time ∈ Icc (0 : ℝ) (wholeRestartVelocityAccumulationTime initial + 1) :=
    ⟨inside.1, by linarith⟩
  rw [velocity, projIcc_of_mem _ wholeInside,
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt initial bounded _ before,
    wholeRestartBoundedPreAccumulationVelocityTrajectory,
    wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix initial bounded _ (length + 1) inside.2,
    receiptVelocity, projIcc_of_mem _ inside]
  rfl

theorem local_momentum_chart (wave : IntegerWavevector) (time : ℝ)
    (inside : time ∈ Ioo (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) :
    ∃ length : ℕ, time ∈ Ioo (0 : ℝ) (WholePrefixState.duration initial length) ∧
      (∀ᶠ actual in 𝓝 time,
        wholeVelocity (velocity initial bounded actual) wave = receiptVelocityRow (WholePrefixReceipt.receipt initial length) wave actual ∧
        momentumAt nu (velocity initial bounded actual) wave = receiptMomentumAction (WholePrefixReceipt.receipt initial length) wave actual) := by
  let length := wholeRestartPreAccumulationCoverIndex initial bounded ⟨time, inside.1.le, inside.2⟩
  have covered := wholeRestartPreAccumulationCoverIndex_spec initial bounded ⟨time, inside.1.le, inside.2⟩
  have below : time < WholePrefixState.duration initial length :=
    covered.trans_le ((elapsedTime_strictMono initial).monotone (Nat.le_succ length))
  refine ⟨length, ⟨inside.1, below⟩, ?_⟩
  filter_upwards [Ioo_mem_nhds inside.1 below] with actual member
  rw [velocity_eq_prefix initial bounded length actual ⟨member.1.le, member.2.le⟩]
  exact ⟨receipt_row _ wave ⟨actual, member.1.le, member.2.le⟩,
    receipt_action _ wave ⟨actual, member.1.le, member.2.le⟩⟩

theorem row_hasDerivAt (wave : IntegerWavevector) (time : ℝ)
    (inside : time ∈ Ioo (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) :
    HasDerivAt (fun actual => wholeVelocity (velocity initial bounded actual) wave)
      (momentumAt nu (velocity initial bounded time) wave) time := by
  obtain ⟨length, within, chart⟩ := local_momentum_chart initial bounded wave time inside
  have atTime := chart.self_of_nhds
  rw [atTime.2]
  exact (receipt_velocity_row_hasDerivAt (WholePrefixReceipt.receipt initial length) wave
    ⟨time, within.1.le, within.2.le⟩).congr_of_eventuallyEq (chart.mono fun _ same => same.1)

theorem action_continuousOn (wave : IntegerWavevector) :
    ContinuousOn (fun actual => momentumAt nu (velocity initial bounded actual) wave)
      (Ioo (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) := by
  intro time inside
  obtain ⟨length, _, chart⟩ := local_momentum_chart initial bounded wave time inside
  exact ((receiptMomentumAction_continuous (WholePrefixReceipt.receipt initial length) wave).continuousAt.congr_of_eventuallyEq
    (chart.mono fun _ same => same.2)).continuousWithinAt

theorem action_integrable (wave : IntegerWavevector) :
    IntervalIntegrable (fun actual => momentumAt nu (velocity initial bounded actual) wave) volume
      0 (wholeRestartVelocityAccumulationTime initial) := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (accumulation_pos initial bounded).le).mpr
  have finite : volume (Ioo (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) < ⊤ :=
    (measure_mono Ioo_subset_Icc_self).trans_lt (isCompact_Icc.measure_lt_top (μ := volume))
  exact IntegrableOn.of_bound finite
    ((action_continuousOn initial bounded wave).aestronglyMeasurable measurableSet_Ioo)
    (‖projectedDivergenceCLM wave‖ * ‖puncturedWholeVelocityEuclideanState initial.initialState‖ ^ 2 +
      |nu.coeff * integerWaveViscousMultiplier wave| * ‖puncturedWholeVelocityEuclideanState initial.initialState‖)
    (Eventually.of_forall fun actual => momentum_norm_le nu _ wave _ (velocity_norm_le initial bounded actual))

theorem pre_accumulation_write : ∀ wave : IntegerWavevector,
    IntervalIntegrable (fun actual => momentumAt nu (velocity initial bounded actual) wave) volume
      0 (wholeRestartVelocityAccumulationTime initial) ∧
    ∀ time ∈ Icc (0 : ℝ) (wholeRestartVelocityAccumulationTime initial),
      wholeVelocity (velocity initial bounded time) wave - wholeVelocity (velocity initial bounded 0) wave =
        ∫ actual in 0..time, momentumAt nu (velocity initial bounded actual) wave := by
  intro wave
  have paid := action_integrable initial bounded wave
  refine ⟨paid, ?_⟩
  intro time inside
  have restricted : IntervalIntegrable (fun actual => momentumAt nu (velocity initial bounded actual) wave) volume 0 time :=
    paid.mono_set (by rw [uIcc_of_le inside.1, uIcc_of_le (accumulation_pos initial bounded).le]; exact Icc_subset_Icc le_rfl inside.2)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1
    (row_continuous initial bounded wave).continuousOn
    (fun actual member => row_hasDerivAt initial bounded wave actual ⟨member.1, member.2.trans_le inside.2⟩) restricted).symm

theorem velocity_initial : velocity initial bounded 0 = puncturedWholeVelocityEuclideanState initial.initialState := by
  rw [velocity_eq_prefix initial bounded 0 0 ⟨le_rfl, (WholePrefixState.duration_pos initial 0).le⟩,
    receiptVelocity, projIcc_of_mem _ ⟨le_rfl, (WholePrefixState.duration_pos initial 0).le⟩,
    (WholePrefixReceipt.receipt initial 0).wholePath_initial]

theorem velocity_endpoint : velocity initial bounded (wholeRestartVelocityAccumulationTime initial) =
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger initial bounded).family.endpointReceipt.velocityEndpoint := by
  have inside : wholeRestartVelocityAccumulationTime initial ∈
      Icc (0 : ℝ) (wholeRestartVelocityAccumulationTime initial + 1) :=
    ⟨(accumulation_pos initial bounded).le, by linarith⟩
  rw [velocity, projIcc_of_mem _ inside,
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_ge initial bounded _ le_rfl]
  exact sourceGeneratedWholeRestartVelocityEndpointAbsolutePhysicalPath_initial initial bounded

theorem original_endpoint_primitive (wave : IntegerWavevector) :
    wholeVelocity (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger initial bounded).family.endpointReceipt.velocityEndpoint wave -
      wholeBiotSavartVelocityState initial.initialState wave =
        ∫ actual in 0..wholeRestartVelocityAccumulationTime initial, momentumAt nu (velocity initial bounded actual) wave := by
  have write := (pre_accumulation_write initial bounded wave).2 (wholeRestartVelocityAccumulationTime initial)
    ⟨(accumulation_pos initial bounded).le, le_rfl⟩
  simpa only [velocity_initial, velocity_endpoint, wholeVelocity_punctured] using write

end
end SaturationMonoid.NavierStokes.NativeOriginalMomentumIntegral
