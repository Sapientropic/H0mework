import H0mework.NavierStokes.WindowPhysics.SpacetimeVelocity
import H0mework.NavierStokes.WindowPhysics.SpacetimeFourierProduct
import H0mework.NavierStokes.WindowPhysics.SpacetimeStress

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowSpacetimeResidual

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeFullOrderAction NativeFullOrderSynthesis NativeWindowSpacetimeFourier NativeWindowFourierProduct

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem residualValue_read (value : FullSpace) :
    NativeCompleteStressCarrier.read (NativeCompleteHeatTransport.residualValue value) =
      NativeCompleteCorrectionRead.residual value := by
  funext wave output input
  change NativeCompleteStressCarrier.readCLM wave output input
    (value.snd - NativeCompleteStressBilinear.mixed (wholeVelocity value.fst) (wholeVelocity value.fst)) = _
  rw [map_sub, NativeCompleteStressCarrier.readCLM_apply, NativeCompleteStressCarrier.readCLM_apply,
    NativeCompleteStressBilinear.mixed_read, NativeHigherTimeJets.mixedFlux_diagonal]
  rfl

variable {nu : Viscosity}

def residual (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : NativeCompleteStressCarrier.Space :=
  NativeCompleteHeatTransport.residualValue (NativeWindowHeatEvolution.source seed lag time)

theorem residual_read (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    NativeCompleteStressCarrier.read (residual seed lag time) =
      NativeCompleteCorrectionRead.residual (NativeWindowHeatEvolution.source seed lag time) :=
  residualValue_read _

theorem velocity_summable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (coordinate : Coordinate) :
    Summable fun wave => ‖wholeVelocity (NativeWindowHeatEvolution.source seed lag time).fst wave coordinate‖ := by
  have generated : Summable fun wave => ‖NativeWindowSpacetimeVelocity.coefficient seed lag coordinate 0 wave time‖ := by
    apply (decay_summable.mul_left (NativeWindowSpacetimeVelocity.coefficientBudget seed lag 0 0)).of_nonneg_of_le
      (fun _ => norm_nonneg _)
    intro wave
    simpa only [pow_zero, one_mul] using
      NativeWindowSpacetimeVelocity.coefficient_decay seed lag positive coordinate 0 0 wave time
  simpa only [NativeWindowSpacetimeVelocity.coefficient, NativeWindowHeatEvolution.velocityJet,
    NativeWindowHeatEvolution.jet_zero] using generated

theorem stress_summable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (entry : Coordinate × Coordinate) :
    Summable fun wave => ‖NativeCompleteStressCarrier.read (NativeWindowHeatEvolution.source seed lag time).snd wave entry.1 entry.2‖ := by
  have generated : Summable fun wave => ‖NativeWindowSpacetimeStress.coefficient seed lag entry 0 wave time‖ := by
    apply (decay_summable.mul_left (NativeWindowSpacetimeStress.coefficientBudget seed lag 0 0)).of_nonneg_of_le
      (fun _ => norm_nonneg _)
    intro wave
    simpa only [pow_zero, one_mul] using
      NativeWindowSpacetimeStress.coefficient_decay seed lag positive entry 0 0 wave time
  simpa only [NativeWindowSpacetimeStress.coefficient, NativeWindowHeatEvolution.jet_zero] using generated

theorem residual_summable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (entry : Coordinate × Coordinate) :
    Summable fun wave => ‖NativeCompleteStressCarrier.read (residual seed lag time) wave entry.1 entry.2‖ := by
  simp only [residual_read, NativeCompleteCorrectionRead.residual, Pi.sub_apply]
  exact ((stress_summable seed lag positive time entry).of_norm.sub
    (quadratic_summable _ (velocity_summable seed lag positive time) entry.1 entry.2)).norm

def jointTensor (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime) :
    EuclideanSpace ℂ (Coordinate × Coordinate) := WithLp.toLp 2 fun entry =>
  ∑' wave, NativeCompleteStressCarrier.read (residual seed lag pair.1) wave entry.1 entry.2 * monomial wave pair.2

theorem jointTensor_source (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime)
    (entry : Coordinate × Coordinate) :
    jointTensor seed lag pair entry = ∑' wave,
      NativeCompleteCorrectionRead.residual (NativeWindowHeatEvolution.source seed lag pair.1) wave entry.1 entry.2 * monomial wave pair.2 := by
  change (∑' wave, NativeCompleteStressCarrier.read (residual seed lag pair.1) wave entry.1 entry.2 * monomial wave pair.2) = _
  rw [residual_read]

theorem jointTensor_coordinate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (pair : Spacetime) (entry : Coordinate × Coordinate) :
    jointTensor seed lag pair entry = NativeWindowSpacetimeStress.jointTensor seed lag pair entry +
      scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag entry.2) pair *
        scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag entry.1) pair := by
  have stressModes := modulated_summable _ (stress_summable seed lag positive pair.1 entry) pair.2
  have quadraticModes := modulated_summable _
    (quadratic_summable _ (velocity_summable seed lag positive pair.1) entry.1 entry.2).norm pair.2
  rw [jointTensor_source, NativeWindowSpacetimeStress.jointTensor_source]
  simp only [NativeCompleteCorrectionRead.residual, Pi.sub_apply, sub_mul]
  rw [stressModes.tsum_sub quadraticModes,
    quadratic_synthesis _ (velocity_summable seed lag positive pair.1), sub_neg_eq_add]
  congr 1

theorem jointTensor_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag) :
    ContDiff ℝ ∞ (jointTensor seed lag) := by
  have same : jointTensor seed lag = fun pair => WithLp.toLp 2 fun entry : Coordinate × Coordinate =>
      scalarField (NativeWindowSpacetimeStress.coefficient seed lag entry) pair +
        scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag entry.2) pair *
          scalarField (NativeWindowSpacetimeVelocity.coefficient seed lag entry.1) pair := by
    funext pair
    apply PiLp.ext
    exact jointTensor_coordinate seed lag positive pair
  rw [same]
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro entry
  exact (NativeWindowSpacetimeStress.scalar_smooth seed lag positive entry).add
    ((NativeWindowSpacetimeVelocity.scalar_smooth seed lag positive entry.2).mul
      (NativeWindowSpacetimeVelocity.scalar_smooth seed lag positive entry.1))

theorem jointTensor_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ MemLp (iteratedFDeriv ℝ order (jointTensor seed lag)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (jointTensor seed lag)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (jointTensor_smooth seed lag positive) order exponent compact

def jointField (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime) :
    EuclideanSpace ℝ (Coordinate × Coordinate) := WithLp.toLp 2 fun entry => (jointTensor seed lag pair entry).re

theorem jointField_source (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime)
    (entry : Coordinate × Coordinate) :
    jointField seed lag pair entry = (∑' wave,
      NativeCompleteCorrectionRead.residual (NativeWindowHeatEvolution.source seed lag pair.1) wave entry.1 entry.2 * monomial wave pair.2).re := by
  change (jointTensor seed lag pair entry).re = _
  rw [jointTensor_source]

theorem jointField_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag) :
    ContDiff ℝ ∞ (jointField seed lag) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro entry
  exact Complex.reCLM.contDiff.comp
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate × Coordinate => ℂ) entry).contDiff.comp
      (jointTensor_smooth seed lag positive))

theorem jointField_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ MemLp (iteratedFDeriv ℝ order (jointField seed lag)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (jointField seed lag)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (jointField_smooth seed lag positive) order exponent compact

def torusField (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ)
    (entry : Coordinate × Coordinate) : C(Torus, ℂ) :=
  series fun wave => NativeCompleteStressCarrier.read (residual seed lag time) wave entry.1 entry.2

theorem torusField_jointTensor (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (space : PhysicalSpace) (entry : Coordinate × Coordinate) :
    torusField seed lag time entry (circlePoint space) = jointTensor seed lag (time, space) entry :=
  series_apply _ (residual_summable seed lag positive time entry) (circlePoint space)

theorem torusField_fourier (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (entry : Coordinate × Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (torusField seed lag time entry) wave =
      NativeCompleteCorrectionRead.residual (NativeWindowHeatEvolution.source seed lag time) wave entry.1 entry.2 := by
  rw [torusField, series_fourier _ (residual_summable seed lag positive time entry), residual_read]

end
end SaturationMonoid.NavierStokes.NativeWindowSpacetimeResidual
