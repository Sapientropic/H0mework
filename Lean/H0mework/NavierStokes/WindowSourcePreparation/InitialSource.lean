import H0mework.NavierStokes.WindowSourcePreparation.Source
import H0mework.NavierStokes.SourceAction.Initial
import H0mework.NavierStokes.SourceAction.Synthesis

set_option autoImplicit false
open scoped BigOperators ENNReal Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowPreparationInitial

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent RationalVorticityEvaluator.ButterflyStackedExpansionMaterial
open NativeEndpointVelocityCarrier NativePhysicalFourier NativePhysicalContinuous NativeFullOrderSynthesis
open NativeFullOrderAction NativeFullOrderInitial

noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def velocity : ComplexVorticityHilbertState :=
  wholeVelocity (NativeForwardWindowSource.source stackedShortCurrent (-2)).fst

theorem velocity_original : velocity = wholeBiotSavartVelocityState stackedSeedState := by
  rw [velocity, NativeWindowPreparationSource.initial_velocity, wholeVelocity_punctured]
  rfl

theorem square_moments (order : ℕ) : Summable (fun wave => frequencySize wave ^ (2 * order) *
    complexCoordinateAmplitudeSq (velocity wave)) := by
  rw [velocity_original]
  simpa only [wholeBiotSavartVelocityState_apply, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    using stacked_initial_moment_summable order

theorem square_budget (order : ℕ) : (∑' wave, frequencySize wave ^ (2 * order) *
    complexCoordinateAmplitudeSq (velocity wave)) = initialMomentBudget order := by
  rw [velocity_original]
  simpa only [wholeBiotSavartVelocityState_apply, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    using stacked_initial_moment_eq_budget order

theorem moments (order : ℕ) : Summable (fun wave => frequencySize wave ^ order * amplitude velocity wave) :=
  summable_moment_of_square velocity order (square_moments (order + 2))

theorem amplitude_summable : Summable (amplitude velocity) := by
  simpa only [pow_zero, one_mul] using moments 0

theorem reality : FiniteStateFourierReality velocity := by
  rw [velocity_original]
  exact NativePhysicalSource.velocity_reality stackedSeedState (butterflyFirstStackPhysicalState_reality (-1))

def torusVelocity : C(Torus, PhysicalSpace) := continuousField velocity
def field : PhysicalSpace → PhysicalSpace := spatialField velocity

theorem field_original (point : PhysicalSpace) : field point = torusVelocity (circlePoint point) := rfl

theorem field_smooth : ContDiff ℝ ∞ field := spatialField_smooth velocity moments

def budget (order : ℕ) : ℝ := (2 * Real.pi) ^ order *
  ((initialMomentBudget (order + 2) + ∑' wave, decay wave) / 2)

theorem derivative_bound (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order field point‖ ≤ budget order := by
  have paid := spatialField_bound_of_square velocity square_moments order point
  rwa [square_budget] at paid

theorem word_read (order : ℕ) (point : PhysicalSpace) (directions : Fin order → PhysicalSpace) :
    iteratedFDeriv ℝ order field point directions =
      ∑' wave, value velocity wave ((∏ index, phase wave (directions index)) •
        (Complex.I ^ order * UnitAddTorus.mFourier wave (circlePoint point))) :=
  spatialField_word_eq velocity moments order point directions

theorem word_bound (order : ℕ) (point : PhysicalSpace) (directions : Fin order → PhysicalSpace) :
    ‖iteratedFDeriv ℝ order field point directions‖ ≤ budget order * ∏ index, ‖directions index‖ :=
  ((iteratedFDeriv ℝ order field point).le_opNorm directions).trans
    (mul_le_mul_of_nonneg_right (derivative_bound order point) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem all_order_Lp (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order field) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order field) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (budget order) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have continuous := field_smooth.continuous_iteratedFDeriv (m := order)
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  have bound : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order field point‖ ≤ budget order :=
    Eventually.of_forall (derivative_bound order)
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable _ bound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bound⟩

theorem velocity_fourier (coordinate : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => (torusVelocity point coordinate : ℂ)) wave = velocity wave coordinate := by
  have paid : Summable (fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) := by
    convert! amplitude_summable using 1
  exact continuousField_fourier velocity paid reality coordinate wave

end
end SaturationMonoid.NavierStokes.NativeWindowPreparationInitial
