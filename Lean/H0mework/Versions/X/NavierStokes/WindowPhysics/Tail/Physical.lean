import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Moments
import H0mework.Versions.X.NavierStokes.WindowPhysics.SpacetimeResidual
import H0mework.Versions.X.NavierStokes.SourceHeat.WindowZero
import H0mework.Versions.X.NavierStokes.WindowPhysics.LocalFourier

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowTailPhysical

open Set Filter MeasureTheory Function
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativeFullOrderAction NativeFullOrderSynthesis NativeEndpointVelocityCarrier
open NativeForwardWindowJets NativeWindowTailMoments NativeWindowSpacetimeFourier NativeWindowLocalFourier

noncomputable section
variable {nu : Viscosity}

def support (seed : GeneratedWholeRestartCurrent nu) : Set Spacetime :=
  Ioi (NativeAbsoluteEventualControl.startTime seed - 1) ×ˢ univ

theorem support_open (seed : GeneratedWholeRestartCurrent nu) : IsOpen (support seed) :=
  isOpen_Ioi.prod isOpen_univ

theorem velocity_scalar_smooth (seed : GeneratedWholeRestartCurrent nu) (coordinate : Coordinate) :
    ContDiffOn ℝ ∞ (scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 coordinate)) (support seed) := by
  intro point inside
  apply (local_scalar_smooth (NativeWindowSpacetimeVelocity.coefficient seed 0 coordinate)
    (NativeWindowSpacetimeVelocity.coefficient_hasDerivAt seed 0 coordinate)
    (NativeAbsoluteEventualControl.startTime seed - 1)
    (fun H rank order => velocityBudget seed H rank (order + 4)) ?_ ?_ point inside.1).contDiffWithinAt
  · intro H rank order
    exact mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (Real.sqrt_nonneg _)
  · intro H time member rank order wave
    simpa only [NativeWindowSpacetimeVelocity.coefficient, NativeWindowHeatEvolution.velocityJet,
      NativeZeroHeatWindow.jet_zero] using
      window_velocity_decay seed H time member rank order wave coordinate

theorem stress_scalar_smooth (seed : GeneratedWholeRestartCurrent nu) (entry : Coordinate × Coordinate) :
    ContDiffOn ℝ ∞ (scalarField (NativeWindowSpacetimeStress.coefficient seed 0 entry)) (support seed) := by
  intro point inside
  apply (local_scalar_smooth (NativeWindowSpacetimeStress.coefficient seed 0 entry)
    (NativeWindowSpacetimeStress.coefficient_hasDerivAt seed 0 entry)
    (NativeAbsoluteEventualControl.startTime seed - 1)
    (fun H rank order => stressBudget seed H rank (order + 4)) ?_ ?_ point inside.1).contDiffWithinAt
  · intro H rank order
    exact mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (Real.sqrt_nonneg _)
  · intro H time member rank order wave
    simpa only [NativeWindowSpacetimeStress.coefficient, NativeZeroHeatWindow.jet_zero] using
      window_stress_decay seed H time member rank order wave entry.1 entry.2

theorem velocity_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (inside : NativeAbsoluteEventualControl.startTime seed - 1 < time) (coordinate : Coordinate) :
    Summable fun wave => ‖wholeVelocity (NativeWindowHeatEvolution.source seed 0 time).fst wave coordinate‖ := by
  have paid := (window_velocity_absolute_moment seed time time ⟨inside.le, le_rfl⟩ 0 0 coordinate).1
  simpa only [pow_zero, one_mul, NativeForwardWindowJets.jet_zero, NativeZeroHeatWindow.source_zero] using paid

theorem stress_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (inside : NativeAbsoluteEventualControl.startTime seed - 1 < time) (entry : Coordinate × Coordinate) :
    Summable fun wave => ‖NativeCompleteStressCarrier.read
      (NativeWindowHeatEvolution.source seed 0 time).snd wave entry.1 entry.2‖ := by
  have paid := (window_stress_absolute_moment seed time time ⟨inside.le, le_rfl⟩ 0 0 entry.1 entry.2).1
  simpa only [pow_zero, one_mul, NativeForwardWindowJets.jet_zero, NativeZeroHeatWindow.source_zero] using paid

theorem velocity_coordinate (seed : GeneratedWholeRestartCurrent nu) (pair : Spacetime)
    (inside : pair ∈ support seed) (coordinate : Coordinate) :
    NativeWindowSpacetimeVelocity.jointField seed 0 pair coordinate =
      (scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 coordinate) pair).re := by
  rw [NativeWindowSpacetimeVelocity.jointField_source]
  have written := NativeWindowFourierProduct.series_apply
    (fun wave => wholeVelocity (NativeWindowHeatEvolution.source seed 0 pair.1).fst wave coordinate)
    (velocity_summable seed pair.1 inside.1 coordinate) (circlePoint pair.2)
  apply congrArg Complex.re
  exact written

theorem velocity_smooth (seed : GeneratedWholeRestartCurrent nu) :
    ContDiffOn ℝ ∞ (NativeWindowSpacetimeVelocity.jointField seed 0) (support seed) := by
  have smooth : ContDiffOn ℝ ∞ (fun pair => WithLp.toLp 2 fun coordinate : Coordinate =>
      (scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 coordinate) pair).re) (support seed) := by
    apply PiLp.contDiff_toLp.comp_contDiffOn
    exact contDiffOn_pi.mpr fun coordinate =>
      Complex.reCLM.contDiff.comp_contDiffOn (velocity_scalar_smooth seed coordinate)
  apply smooth.congr
  intro pair inside
  apply PiLp.ext
  exact velocity_coordinate seed pair inside

theorem stressTensor_smooth (seed : GeneratedWholeRestartCurrent nu) :
    ContDiffOn ℝ ∞ (NativeWindowSpacetimeStress.jointTensor seed 0) (support seed) := by
  apply PiLp.contDiff_toLp.comp_contDiffOn
  exact contDiffOn_pi.mpr fun entry => stress_scalar_smooth seed entry

theorem stress_smooth (seed : GeneratedWholeRestartCurrent nu) :
    ContDiffOn ℝ ∞ (NativeWindowSpacetimeStress.jointField seed 0) (support seed) := by
  apply PiLp.contDiff_toLp.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro entry
  exact Complex.reCLM.contDiff.comp_contDiffOn
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate × Coordinate => ℂ) entry).contDiff.comp_contDiffOn
      (stressTensor_smooth seed))

theorem residual_coordinate (seed : GeneratedWholeRestartCurrent nu) (pair : Spacetime)
    (inside : pair ∈ support seed) (entry : Coordinate × Coordinate) :
    NativeWindowSpacetimeResidual.jointTensor seed 0 pair entry =
      NativeWindowSpacetimeStress.jointTensor seed 0 pair entry +
        scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 entry.2) pair *
          scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 entry.1) pair := by
  have stressModes := NativeWindowFourierProduct.modulated_summable _
    (stress_summable seed pair.1 inside.1 entry) pair.2
  have quadraticModes := NativeWindowFourierProduct.modulated_summable _
    (NativeWindowFourierProduct.quadratic_summable _
      (velocity_summable seed pair.1 inside.1) entry.1 entry.2).norm pair.2
  rw [NativeWindowSpacetimeResidual.jointTensor_source, NativeWindowSpacetimeStress.jointTensor_source]
  simp only [NativeCompleteCorrectionRead.residual, Pi.sub_apply, sub_mul]
  rw [stressModes.tsum_sub quadraticModes,
    NativeWindowFourierProduct.quadratic_synthesis _ (velocity_summable seed pair.1 inside.1), sub_neg_eq_add]
  congr 1

theorem residualTensor_smooth (seed : GeneratedWholeRestartCurrent nu) :
    ContDiffOn ℝ ∞ (NativeWindowSpacetimeResidual.jointTensor seed 0) (support seed) := by
  have smooth : ContDiffOn ℝ ∞ (fun pair => WithLp.toLp 2 fun entry : Coordinate × Coordinate =>
      scalarField (NativeWindowSpacetimeStress.coefficient seed 0 entry) pair +
        scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 entry.2) pair *
          scalarField (NativeWindowSpacetimeVelocity.coefficient seed 0 entry.1) pair) (support seed) := by
    apply PiLp.contDiff_toLp.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro entry
    exact (stress_scalar_smooth seed entry).add
      ((velocity_scalar_smooth seed entry.2).mul (velocity_scalar_smooth seed entry.1))
  apply smooth.congr
  intro pair inside
  apply PiLp.ext
  exact residual_coordinate seed pair inside

theorem residual_smooth (seed : GeneratedWholeRestartCurrent nu) :
    ContDiffOn ℝ ∞ (NativeWindowSpacetimeResidual.jointField seed 0) (support seed) := by
  apply PiLp.contDiff_toLp.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro entry
  exact Complex.reCLM.contDiff.comp_contDiffOn
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate × Coordinate => ℂ) entry).contDiff.comp_contDiffOn
      (residualTensor_smooth seed))

theorem velocity_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ support seed) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      MemLp (iteratedFDeriv ℝ order (NativeWindowSpacetimeVelocity.jointField seed 0)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (NativeWindowSpacetimeVelocity.jointField seed 0)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp_on _ (velocity_smooth seed) (support_open seed) order exponent compact contained

theorem stress_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ support seed) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      MemLp (iteratedFDeriv ℝ order (NativeWindowSpacetimeStress.jointField seed 0)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (NativeWindowSpacetimeStress.jointField seed 0)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp_on _ (stress_smooth seed) (support_open seed) order exponent compact contained

theorem residual_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ support seed) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      MemLp (iteratedFDeriv ℝ order (NativeWindowSpacetimeResidual.jointField seed 0)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (NativeWindowSpacetimeResidual.jointField seed 0)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp_on _ (residual_smooth seed) (support_open seed) order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativeWindowTailPhysical
