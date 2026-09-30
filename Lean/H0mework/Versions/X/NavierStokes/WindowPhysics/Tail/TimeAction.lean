import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Physical
import H0mework.Versions.X.NavierStokes.SourcePairing.SpacetimeEquation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeTailTimeAction

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFullOrderAction NativeFullOrderSynthesis NativeEndpointVelocityCarrier
open NativeWindowTailMoments NativeWindowSpacetimeFourier NativeWindowSpacetimeVelocity
open NativeViewPhysicalTime NativeViewPhysicalEquation

noncomputable section
variable {nu : Viscosity}

theorem scalarWord_mode_bound (seed : GeneratedWholeRestartCurrent nu) (horizon time : ℝ)
    (inside : time ∈ Icc (NativeAbsoluteEventualControl.startTime seed - 1) horizon)
    (coordinate : Coordinate) (order : ℕ) (wave : IntegerWavevector) (space : PhysicalSpace) :
    ‖coefficient seed 0 coordinate order wave time * monomial wave space‖ ≤
      velocityBudget seed horizon order 4 * decay wave := by
  rw [norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) (NativeWindowFourierProduct.monomial_norm_le wave space)).trans
  simpa only [coefficient, NativeWindowHeatEvolution.velocityJet, NativeZeroHeatWindow.jet_zero,
    pow_zero, one_mul] using window_velocity_decay seed horizon time inside order 0 wave coordinate

theorem scalarWord_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (inside : NativeAbsoluteEventualControl.startTime seed - 1 < time)
    (coordinate : Coordinate) (order : ℕ) (space : PhysicalSpace) :
    Summable fun wave => coefficient seed 0 coordinate order wave time * monomial wave space :=
  (decay_summable.mul_left (velocityBudget seed time order 4)).of_norm_bounded
    (fun wave => scalarWord_mode_bound seed time time ⟨inside.le, le_rfl⟩ coordinate order wave space)

theorem scalarWord_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (inside : NativeAbsoluteEventualControl.startTime seed - 1 < time)
    (coordinate : Coordinate) (order : ℕ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => scalarWord seed 0 coordinate order (sample, space))
      (scalarWord seed 0 coordinate (order + 1) (time, space)) time := by
  let interval := Ioo (NativeAbsoluteEventualControl.startTime seed - 1) (time + 1)
  have member : time ∈ interval := ⟨inside, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected
    (decay_summable.mul_left (velocityBudget seed (time + 1) (order + 1) 4)) isOpen_Ioo
    (convex_Ioo _ _).isPreconnected
    (fun wave sample _ => (coefficient_hasDerivAt seed 0 coordinate order wave sample).mul_const
      (monomial wave space))
    (fun wave sample sampleInside => scalarWord_mode_bound seed (time + 1) sample
      ⟨sampleInside.1.le, sampleInside.2.le⟩ coordinate (order + 1) wave space)
    member (scalarWord_summable seed time inside coordinate order space) member

theorem velocityWord_coordinate (seed : GeneratedWholeRestartCurrent nu) (pair : Spacetime)
    (inside : NativeAbsoluteEventualControl.startTime seed - 1 < pair.1)
    (coordinate : Coordinate) (order : ℕ) :
    velocityWord seed 0 order pair coordinate = (scalarWord seed 0 coordinate order pair).re := by
  have paid : Summable fun wave =>
      ‖wholeVelocity (NativeWindowHeatEvolution.velocityJet seed 0 order pair.1) wave coordinate‖ := by
    simpa only [pow_zero, one_mul, NativeWindowHeatEvolution.velocityJet, NativeZeroHeatWindow.jet_zero] using
      (window_velocity_absolute_moment seed pair.1 pair.1 ⟨inside.le, le_rfl⟩ order 0 coordinate).1
  exact congrArg Complex.re (NativeWindowFourierProduct.series_apply _ paid (circlePoint pair.2))

theorem velocityWord_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (inside : NativeAbsoluteEventualControl.startTime seed - 1 < time)
    (order : ℕ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => velocityWord seed 0 order (sample, space))
      (velocityWord seed 0 (order + 1) (time, space)) time := by
  have coordinates : HasDerivAt (fun sample => fun coordinate =>
      (scalarWord seed 0 coordinate order (sample, space)).re)
      (fun coordinate => (scalarWord seed 0 coordinate (order + 1) (time, space)).re) time :=
    hasDerivAt_pi.mpr fun coordinate => Complex.reCLM.hasFDerivAt.comp_hasDerivAt time
      (scalarWord_hasDerivAt seed time inside coordinate order space)
  have generated := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    time coordinates
  have derivative_same :
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℝ)).symm.toContinuousLinearMap
        (fun coordinate => (scalarWord seed 0 coordinate (order + 1) (time, space)).re) =
        velocityWord seed 0 (order + 1) (time, space) := by
    apply PiLp.ext
    intro coordinate
    exact (velocityWord_coordinate seed (time, space) inside coordinate (order + 1)).symm
  rw [derivative_same] at generated
  apply generated.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds inside] with sample member
  apply PiLp.ext
  intro coordinate
  exact velocityWord_coordinate seed (sample, space) member coordinate order

theorem momentumField_eq (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (inside : NativeAbsoluteEventualControl.startTime seed - 1 < time) (space : PhysicalSpace) :
    momentumField seed 0 (time, space) = velocityWord seed 0 1 (time, space) := by
  have valid : -1 < time := by linarith [NativeAbsoluteEventualControl.startTime_nonnegative seed]
  apply PiLp.ext
  intro coordinate
  rw [velocityWord_coordinate seed (time, space) inside coordinate 1]
  simp only [momentumField, scalarWord, coefficient, momentum_row seed 0 time valid]

theorem physical_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (inside : NativeAbsoluteEventualControl.startTime seed - 1 < time) (space : PhysicalSpace) :
    HasDerivAt (fun sample => NativeWindowSpacetimeVelocity.jointField seed 0 (sample, space))
      (momentumField seed 0 (time, space)) time := by
  rw [momentumField_eq seed time inside space]
  exact velocityWord_hasDerivAt seed time inside 0 space

end
end SaturationMonoid.NavierStokes.NativeTailTimeAction
