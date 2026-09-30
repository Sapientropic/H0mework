import H0mework.NavierStokes.WindowPhysics.SpacetimeFourier
import H0mework.NavierStokes.SourceReadout.MomentumFlux
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeWindowFourierProduct

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeFullOrderSynthesis
open MeasureTheory

noncomputable section

abbrev Torus := UnitAddTorus Coordinate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def series (coefficient : IntegerWavevector → ℂ) : C(Torus, ℂ) :=
  ∑' wave, coefficient wave • UnitAddTorus.mFourier wave

theorem series_summable (coefficient : IntegerWavevector → ℂ)
    (paid : Summable fun wave => ‖coefficient wave‖) :
    Summable fun wave => coefficient wave • UnitAddTorus.mFourier wave := by
  apply Summable.of_norm
  simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using paid

theorem series_apply (coefficient : IntegerWavevector → ℂ)
    (paid : Summable fun wave => ‖coefficient wave‖) (point : Torus) :
    series coefficient point = ∑' wave, coefficient wave * UnitAddTorus.mFourier wave point := by
  exact (ContinuousMap.evalCLM ℂ point).map_tsum (series_summable coefficient paid)

def fourierRead (wave : IntegerWavevector) : C(Torus, ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : IntegerWavevector => ℂ) 2 wave).comp
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousMap.toLp 2 volume ℂ))

theorem fourierRead_apply (wave : IntegerWavevector) (field : C(Torus, ℂ)) :
    fourierRead wave field = UnitAddTorus.mFourierCoeff field wave := by
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (field.toLp 2 volume ℂ) wave = _
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierCoeff_toLp]

theorem fourierRead_monomial (wave mode : IntegerWavevector) :
    fourierRead wave (UnitAddTorus.mFourier mode) = if mode = wave then 1 else 0 := by
  classical
  change (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (UnitAddTorus.mFourierLp 2 mode) wave = _
  rw [← UnitAddTorus.coe_mFourierBasis, HilbertBasis.repr_self]
  simp [lp.single_apply, Pi.single_apply, eq_comm]

theorem series_fourier (coefficient : IntegerWavevector → ℂ)
    (paid : Summable fun wave => ‖coefficient wave‖) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (series coefficient) wave = coefficient wave := by
  classical
  rw [← fourierRead_apply, series, (fourierRead wave).map_tsum (series_summable coefficient paid)]
  simp only [map_smul, fourierRead_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq wave coefficient

def reindex : IntegerWavevector × IntegerWavevector ≃ IntegerWavevector × IntegerWavevector where
  toFun pair := (pair.2, pair.1 - pair.2)
  invFun pair := (pair.1 + pair.2, pair.1)
  left_inv pair := by ext coordinate <;> simp
  right_inv pair := by ext coordinate <;> simp

theorem monomial_norm_le (wave : IntegerWavevector) (point : PhysicalSpace) : ‖monomial wave point‖ ≤ 1 := by
  exact ((UnitAddTorus.mFourier wave).norm_coe_le_norm (circlePoint point)).trans_eq UnitAddTorus.mFourier_norm

theorem modulated_summable (coefficient : IntegerWavevector → ℂ)
    (paid : Summable fun wave => ‖coefficient wave‖) (point : PhysicalSpace) :
    Summable fun wave => coefficient wave * monomial wave point := by
  apply paid.of_norm_bounded
  intro wave
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (monomial_norm_le wave point)

theorem convolution_summable (left right : IntegerWavevector → ℂ)
    (leftPaid : Summable fun wave => ‖left wave‖) (rightPaid : Summable fun wave => ‖right wave‖) :
    Summable fun wave => ∑' first, left first * right (wave - first) := by
  have paired := summable_mul_of_summable_norm leftPaid rightPaid
  have changed := reindex.summable_iff.mpr paired
  exact changed.prod

theorem convolution_synthesis (left right : IntegerWavevector → ℂ)
    (leftPaid : Summable fun wave => ‖left wave‖) (rightPaid : Summable fun wave => ‖right wave‖)
    (point : PhysicalSpace) :
    (∑' wave, (∑' first, left first * right (wave - first)) * monomial wave point) =
      (∑' wave, left wave * monomial wave point) * (∑' wave, right wave * monomial wave point) := by
  have leftModes := modulated_summable left leftPaid point
  have rightModes := modulated_summable right rightPaid point
  have paired := summable_mul_of_summable_norm leftModes.norm rightModes.norm
  have changed := reindex.summable_iff.mpr paired
  simp only [Function.comp_def] at changed
  rw [tsum_mul_tsum_of_summable_norm leftModes.norm rightModes.norm, ← reindex.tsum_eq, changed.tsum_prod]
  apply tsum_congr
  intro wave
  rw [← tsum_mul_right]
  apply tsum_congr
  intro first
  change (left first * right (wave - first)) * monomial wave point =
    (left first * monomial first point) * (right (wave - first) * monomial (wave - first) point)
  have characters : monomial first point * monomial (wave - first) point = monomial wave point := by
    unfold monomial
    rw [← UnitAddTorus.mFourier_add, add_sub_cancel]
  rw [← characters]
  ring

theorem quadratic_summable (velocity : ComplexVorticityHilbertState)
    (paid : ∀ coordinate : Coordinate, Summable fun wave => ‖velocity wave coordinate‖)
    (output input : Coordinate) :
    Summable fun wave => NativeStressSource.quadraticFlux velocity wave output input := by
  exact (convolution_summable (fun wave => velocity wave input) (fun wave => velocity wave output)
    (paid input) (paid output)).neg

theorem quadratic_synthesis (velocity : ComplexVorticityHilbertState)
    (paid : ∀ coordinate : Coordinate, Summable fun wave => ‖velocity wave coordinate‖)
    (output input : Coordinate) (point : PhysicalSpace) :
    (∑' wave, NativeStressSource.quadraticFlux velocity wave output input * monomial wave point) =
      -((∑' wave, velocity wave input * monomial wave point) *
        (∑' wave, velocity wave output * monomial wave point)) := by
  simp only [NativeStressSource.quadraticFlux, neg_mul, tsum_neg]
  rw [convolution_synthesis _ _ (paid input) (paid output)]

end
end SaturationMonoid.NavierStokes.NativeWindowFourierProduct
