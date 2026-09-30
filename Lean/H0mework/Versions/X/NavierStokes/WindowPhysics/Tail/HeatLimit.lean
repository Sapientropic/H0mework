import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Moments
import H0mework.Versions.X.NavierStokes.SourceHeat.SpatialZero

/-! The generated tail budget controls the original window uniformly down to zero heat. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTailHeatLimit
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeFullOrderAction NativeFullOrderSynthesis NativeEndpointVelocityCarrier
open NativeWindowTailMoments NativeForwardWindowJets
noncomputable section
variable {nu : Viscosity}

theorem amplitude_decay (seed : GeneratedWholeRestartCurrent nu) (horizon time : ℝ)
    (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (rank order : ℕ) (wave : IntegerWavevector) :
    frequencySize wave ^ order * vorticityRowAmplitude (wholeVelocity (jet seed rank time).fst) wave ≤
      (3 * velocityBudget seed horizon rank (order + 4)) * decay wave := by
  let value := wholeVelocity (jet seed rank time).fst
  let weight := frequencySize wave ^ order
  let bound := velocityBudget seed horizon rank (order + 4) * decay wave
  have weight0 : 0 ≤ weight := pow_nonneg (frequencySize_nonneg wave) order
  have bound0 : 0 ≤ bound := by
    dsimp only [bound, velocityBudget, decay]
    exact mul_nonneg (mul_nonneg (integral_nonneg fun shift => norm_nonneg _)
      (Real.sqrt_nonneg _)) (sq_nonneg _)
  have row : ‖weight • value wave‖ ≤ bound := by
    apply (pi_norm_le_iff_of_nonneg bound0).mpr
    intro coordinate
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg weight0]
    exact window_velocity_decay seed horizon time inside rank order wave coordinate
  rw [norm_smul, Real.norm_of_nonneg weight0] at row
  have amplitude := NativeFixedFilterGlobalControl.amplitude_le_three_norm value wave
  calc
    _ ≤ weight * (3 * ‖value wave‖) := mul_le_mul_of_nonneg_left amplitude weight0
    _ = 3 * (weight * ‖value wave‖) := by ring
    _ ≤ 3 * bound := mul_le_mul_of_nonneg_left row (by norm_num)
    _ = _ := by dsimp only [bound]; ring

theorem velocity_moments (seed : GeneratedWholeRestartCurrent nu) (horizon time : ℝ)
    (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon) (rank order : ℕ) :
    Summable fun wave => frequencySize wave ^ order *
      vorticityRowAmplitude (wholeVelocity (jet seed rank time).fst) wave :=
  (decay_summable.mul_left (3 * velocityBudget seed horizon rank (order + 4))).of_nonneg_of_le
    (fun wave => mul_nonneg (pow_nonneg (frequencySize_nonneg wave) order) (vorticityRowAmplitude_nonneg _ _))
    (amplitude_decay seed horizon time inside rank order)

theorem velocity_jets_uniform_zero (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (rank order : ℕ) :
    TendstoUniformly (fun lag : ℝ≥0 => fun pair :
        Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon × PhysicalSpace =>
      iteratedFDeriv ℝ order
        (spatialField (wholeVelocity (NativeWindowHeatEvolution.jet seed lag rank pair.1).fst)) pair.2)
      (fun pair => iteratedFDeriv ℝ order (spatialField (wholeVelocity (jet seed rank pair.1).fst)) pair.2)
      (𝓝 0) := by
  apply NativeHeatSpatialZero.family_jets_uniform_zero (family := fun time :
      Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon => (jet seed rank time).fst)
    nu (envelope := fun order wave => (3 * velocityBudget seed horizon rank (order + 4)) * decay wave)
  · intro order
    exact decay_summable.mul_left _
  · intro order wave
    dsimp only [velocityBudget, decay]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg
      (integral_nonneg fun shift => norm_nonneg _) (Real.sqrt_nonneg _))) (sq_nonneg _)
  · intro time order wave
    exact amplitude_decay seed horizon time time.property rank order wave

theorem velocity_jets_bound (seed : GeneratedWholeRestartCurrent nu) (horizon time : ℝ)
    (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (rank order : ℕ) (lag : ℝ≥0) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order
      (spatialField (wholeVelocity (NativeWindowHeatEvolution.jet seed lag rank time).fst)) point‖ ≤
        (2 * Real.pi) ^ order *
          ((3 * velocityBudget seed horizon rank (order + 4)) * ∑' wave, decay wave) := by
  refine (NativeHeatSpatialZero.jet_bound nu lag (jet seed rank time).fst
    (velocity_moments seed horizon time inside rank) order point).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← tsum_mul_left]
  exact (velocity_moments seed horizon time inside rank order).tsum_le_tsum
    (amplitude_decay seed horizon time inside rank order) (decay_summable.mul_left _)

end
end SaturationMonoid.NavierStokes.NativeWindowTailHeatLimit
