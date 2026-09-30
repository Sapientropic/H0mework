import H0mework.Versions.X.NavierStokes.MomentumAction.NegativeFourMomentum
import H0mework.Versions.X.NavierStokes.MacroAction.FiniteMacroMomentum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeGlobalHilbertAction

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeEndpointVelocityCarrier NativeMomentumIntegral NativeFiniteMacroMomentum
open NativeNegativeFourMomentum

noncomputable section

variable {nu : Viscosity}

def sourceState (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : WholeRestartVelocityEndpointState :=
  embed (NativeAbsoluteEventualControl.velocity seed time)

def sourceAction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : WholeRestartVelocityEndpointState :=
  actionState nu (NativeAbsoluteEventualControl.velocity seed time)

def sourceBudget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  actionBudget nu ‖puncturedWholeVelocityEuclideanState seed.initialState‖

theorem sourceAction_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ‖sourceAction seed time‖ ≤ sourceBudget seed :=
  actionState_norm_le nu _ _ (NativeAbsoluteEventualControl.velocity_norm_le seed time)

theorem sourceState_reconstruct (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : NonzeroIntegerWavevector) :
    integerWaveNormSq wave.1 ^ 2 • sourceState seed time wave = NativeAbsoluteEventualControl.velocity seed time wave :=
  embed_reconstruct _ wave

theorem sourceAction_reconstruct (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : NonzeroIntegerWavevector) :
    integerWaveNormSq wave.1 ^ 2 • sourceAction seed time wave =
      euclideanCoordinateRow (action nu (NativeAbsoluteEventualControl.velocity seed time) wave.1) := by
  rw [sourceAction, actionState_apply]
  change integerWaveNormSq wave.1 ^ 2 • (weight wave.1 •
    euclideanCoordinateRow (action nu (NativeAbsoluteEventualControl.velocity seed time) wave.1)) = _
  rw [weight, smul_smul, ← mul_pow, mul_inv_cancel₀ (integerWaveNormSq_pos wave.2).ne', one_pow, one_smul]

theorem action_measurable_on_interval (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    AEStronglyMeasurable (sourceAction seed) (volume.restrict (Icc (0 : ℝ) horizon)) := by
  let partialSum (observed : Finset NonzeroIntegerWavevector) (time : ℝ) : WholeRestartVelocityEndpointState :=
    ∑ wave ∈ observed, lp.single 2 wave (sourceAction seed time wave)
  have coordinate (wave : NonzeroIntegerWavevector) :
      AEStronglyMeasurable (fun time => sourceAction seed time wave) (volume.restrict (Icc (0 : ℝ) horizon)) := by
    have integrable := (intervalIntegrable_iff_integrableOn_Icc_of_le nonnegative).mp
      (source_absolute_writes seed horizon nonnegative wave.1).1
    exact (weightedRowCLM wave.1).continuous.comp_aestronglyMeasurable integrable.aestronglyMeasurable
  have measurable (observed : Finset NonzeroIntegerWavevector) :
      AEStronglyMeasurable (partialSum observed) (volume.restrict (Icc (0 : ℝ) horizon)) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous
      |>.comp_aestronglyMeasurable (coordinate wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset NonzeroIntegerWavevector)) measurable
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (sourceAction seed time)

theorem sourceAction_aestronglyMeasurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (sourceAction seed) (volume.restrict (Ici (0 : ℝ))) := by
  have cover : (⋃ index : ℕ, Icc (0 : ℝ) (index : ℝ)) = Ici (0 : ℝ) := by
    ext time
    constructor
    · intro inside
      obtain ⟨index, member⟩ := mem_iUnion.mp inside
      exact member.1
    · intro nonnegative
      obtain ⟨index, bound⟩ := exists_nat_ge time
      exact mem_iUnion.mpr ⟨index, nonnegative, bound⟩
  rw [← cover]
  exact AEStronglyMeasurable.iUnion (fun index : ℕ => action_measurable_on_interval seed index (Nat.cast_nonneg index))

theorem sourceAction_Linfty (seed : GeneratedWholeRestartCurrent nu) :
    MemLp (sourceAction seed) ∞ (volume.restrict (Ici (0 : ℝ))) ∧
      eLpNorm (sourceAction seed) ∞ (volume.restrict (Ici (0 : ℝ))) ≤ ENNReal.ofReal (sourceBudget seed) := by
  have bounded : ∀ᵐ time ∂volume.restrict (Ici (0 : ℝ)), ‖sourceAction seed time‖ ≤ sourceBudget seed :=
    Eventually.of_forall (sourceAction_bound seed)
  exact ⟨memLp_top_of_bound (sourceAction_aestronglyMeasurable seed) _ bounded,
    eLpNormEssSup_le_of_ae_bound bounded⟩

theorem sourceAction_intervalIntegrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    IntervalIntegrable (sourceAction seed) volume 0 horizon := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le nonnegative).mpr
  exact IntegrableOn.of_bound (isCompact_Icc.measure_lt_top (μ := volume))
    (action_measurable_on_interval seed horizon nonnegative) (sourceBudget seed)
    (Eventually.of_forall (sourceAction_bound seed))

theorem source_integral_write (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) :
    sourceState seed b - sourceState seed a = ∫ time in a..b, sourceAction seed time := by
  have integrable := (sourceAction_intervalIntegrable seed a a_nonnegative).symm.trans
    (sourceAction_intervalIntegrable seed b b_nonnegative)
  apply lp.ext
  funext wave
  have evaluate := (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).intervalIntegral_comp_comm integrable
  change sourceState seed b wave - sourceState seed a wave =
    (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave)
      (∫ time in a..b, sourceAction seed time)
  rw [← evaluate]
  change sourceState seed b wave - sourceState seed a wave = ∫ time in a..b, sourceAction seed time wave
  simp only [sourceAction, actionState_apply]
  have rawIntegrable := (source_absolute_writes seed a a_nonnegative wave.1).1.symm.trans
    (source_absolute_writes seed b b_nonnegative wave.1).1
  rw [(weightedRowCLM wave.1).intervalIntegral_comp_comm rawIntegrable]
  have original : row (NativeAbsoluteEventualControl.velocity seed b) wave.1 -
      row (NativeAbsoluteEventualControl.velocity seed a) wave.1 =
      ∫ time in a..b, action nu (NativeAbsoluteEventualControl.velocity seed time) wave.1 :=
    source_momentum_write seed a b a_nonnegative b_nonnegative wave.1
  rw [← original, map_sub, weightedRowCLM_row, weightedRowCLM_row]
  rfl

theorem sourceState_dist_le (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ)
    (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) :
    dist (sourceState seed b) (sourceState seed a) ≤ sourceBudget seed * |b - a| := by
  rw [dist_eq_norm, source_integral_write seed a b a_nonnegative b_nonnegative]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun time _ => sourceAction_bound seed time)

end
end SaturationMonoid.NavierStokes.NativeGlobalHilbertAction
