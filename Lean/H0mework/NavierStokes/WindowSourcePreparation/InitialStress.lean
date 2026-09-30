import H0mework.NavierStokes.WindowSourcePreparation.InitialSource
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
open scoped BigOperators ENNReal Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowPreparationInitial

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativePhysicalFourier NativePhysicalContinuous NativeFullOrderSynthesis
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

abbrev Tensor := EuclideanSpace ℝ (Coordinate × Coordinate)

private def tensorRight (first : PhysicalSpace) : PhysicalSpace →ₗ[ℝ] Tensor where
  toFun last := WithLp.toLp 2 fun entry => -(first entry.1 * last entry.2)
  map_add' left right := by ext entry; simp; ring
  map_smul' scalar last := by ext entry; simp; ring

private def tensorLeft : PhysicalSpace →ₗ[ℝ] (PhysicalSpace →L[ℝ] Tensor) where
  toFun first := (tensorRight first).toContinuousLinearMap
  map_add' left right := by ext last entry; simp [tensorRight]; ring
  map_smul' scalar first := by ext last entry; simp [tensorRight]; ring

def tensorProduct : PhysicalSpace →L[ℝ] PhysicalSpace →L[ℝ] Tensor := tensorLeft.toContinuousLinearMap

theorem tensorProduct_apply (first last : PhysicalSpace) (entry : Coordinate × Coordinate) :
    tensorProduct first last entry = -(first entry.1 * last entry.2) := rfl

def stress (point : PhysicalSpace) : Tensor := tensorProduct (field point) (field point)
def torusStress (point : Torus) : Tensor := tensorProduct (torusVelocity point) (torusVelocity point)

theorem stress_original (point : PhysicalSpace) : stress point = torusStress (circlePoint point) := rfl

theorem stress_smooth : ContDiff ℝ ∞ stress :=
  tensorProduct.contDiff.comp field_smooth |>.clm_apply field_smooth

def stressBudget (order : ℕ) : ℝ := ‖tensorProduct‖ * ∑ rank ∈ Finset.range (order + 1),
  (order.choose rank : ℝ) * budget rank * budget (order - rank)

theorem stress_derivative_bound (order : ℕ) (point : PhysicalSpace) :
    ‖iteratedFDeriv ℝ order stress point‖ ≤ stressBudget order := by
  apply (tensorProduct.norm_iteratedFDeriv_le_of_bilinear field_smooth field_smooth point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).trans
  dsimp only [stressBudget]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg tensorProduct)
  apply Finset.sum_le_sum
  intro rank _
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (derivative_bound rank point) (Nat.cast_nonneg _)
  · exact derivative_bound (order - rank) point
  · exact norm_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (derivative_bound rank point))

theorem stress_all_order_Lp (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace}
    (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order stress) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order stress) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (stressBudget order) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have continuous := stress_smooth.continuous_iteratedFDeriv (m := order)
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  have bound : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order stress point‖ ≤ stressBudget order :=
    Eventually.of_forall (stress_derivative_bound order)
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable _ bound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bound⟩

private theorem scalar_ae (coordinate : Coordinate) :
    scalarField velocity coordinate =ᵐ[volume] fun point => (torusVelocity point coordinate : ℂ) := by
  have paid : Summable (fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) := by
    convert! amplitude_summable using 1
  filter_upwards [continuousField_ae velocity paid, realField_apply velocity,
    scalarField_real velocity reality coordinate] with point continuous actual real
  have component : torusVelocity point coordinate = (scalarField velocity coordinate point).re := by
    rw [torusVelocity, ← continuous, actual]
    rfl
  apply Complex.ext
  · exact component.symm
  · simpa using real

/-- All nine original sigma coefficients, including the zero wave, are read from this product. -/
theorem stress_fourier (output input : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => (torusStress point (output,input) : ℂ)) wave =
      NativeCompleteStressCarrier.read (NativeForwardWindowSource.source stackedShortCurrent (-2)).snd wave output input := by
  rw [NativeWindowPreparationSource.initial_stress]
  change _ = NativeStressSource.quadraticFlux velocity wave output input
  rw [← physical_flux_fourier velocity output input wave]
  apply integral_congr_ae
  filter_upwards [scalar_ae output, scalar_ae input] with point first last
  rw [first, last]
  simp only [torusStress, tensorProduct_apply, Complex.ofReal_neg, Complex.ofReal_mul]
  ring

def residual : PhysicalSpace → Tensor := 0

theorem residual_original : NativeCompleteCorrectionRead.residual
    (NativeForwardWindowSource.source stackedShortCurrent (-2)) = 0 :=
  NativeWindowPreparationSource.initial_residual stackedShortCurrent

theorem residual_fourier (output input : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun _ : Torus => ((0 : Tensor) (output,input) : ℂ)) wave =
      NativeCompleteCorrectionRead.residual (NativeForwardWindowSource.source stackedShortCurrent (-2)) wave output input := by
  rw [residual_original]
  simp [UnitAddTorus.mFourierCoeff]

theorem residual_derivative_zero (order : ℕ) : iteratedFDeriv ℝ order residual = 0 := by
  simp [residual]

end
end SaturationMonoid.NavierStokes.NativeWindowPreparationInitial
