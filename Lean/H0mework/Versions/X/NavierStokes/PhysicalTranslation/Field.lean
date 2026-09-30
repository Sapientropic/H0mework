import H0mework.Versions.X.NavierStokes.PhysicalTranslation.Spectral

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativePhysicalTranslation

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativePhysicalFourier NativePhysicalGradient NativeSpatialTranslation

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def displacement (direction : Fin 3) (time : ℝ) : Torus := Pi.single direction (time : UnitAddCircle)

theorem character_add (wave : IntegerWavevector) (first second : Torus) :
    UnitAddTorus.mFourier wave (first + second) = UnitAddTorus.mFourier wave first * UnitAddTorus.mFourier wave second := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    smul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem character_neg_neg (wave : IntegerWavevector) (point : Torus) :
    UnitAddTorus.mFourier (-wave) (-point) = UnitAddTorus.mFourier wave point := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply,
    neg_smul, smul_neg, neg_neg]

theorem character_displacement (direction : Fin 3) (time : ℝ) (wave : IntegerWavevector) :
    UnitAddTorus.mFourier wave (displacement direction time) = phase direction time wave := by
  have reduce : UnitAddTorus.mFourier wave (displacement direction time) = fourier (wave direction) (time : UnitAddCircle) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, displacement]
    rw [Finset.prod_eq_single direction]
    · rw [Pi.single_eq_same]
    · intro other _ different
      rw [Pi.single_eq_of_ne different, fourier_eval_zero]
    · simp
  rw [reduce, fourier_coe_apply]
  unfold phase frequency
  congr 1
  push_cast
  ring

def translate (offset : Torus) (value : ScalarField) : ScalarField :=
  Lp.compMeasurePreserving (fun point : Torus => point + offset)
    (measurePreserving_add_right volume offset) value

theorem translate_apply (offset : Torus) (value : ScalarField) :
    translate offset value =ᵐ[volume] fun point => value (point + offset) :=
  Lp.coeFn_compMeasurePreserving value (measurePreserving_add_right volume offset)

theorem translate_fourier (offset : Torus) (value : ScalarField) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (translate offset value) wave =
      UnitAddTorus.mFourier wave offset * UnitAddTorus.mFourierCoeff value wave := by
  have shifted := integral_add_right_eq_self
    (fun point : Torus => UnitAddTorus.mFourier (-wave) (point - offset) * value point) offset (μ := volume)
  simp only [add_sub_cancel_right] at shifted
  calc
    _ = ∫ point : Torus, UnitAddTorus.mFourier (-wave) point * value (point + offset) := by
      apply integral_congr_ae
      filter_upwards [translate_apply offset value] with point actual
      simp only [smul_eq_mul]
      rw [actual]
    _ = ∫ point : Torus, UnitAddTorus.mFourier (-wave) (point - offset) * value point := shifted
    _ = _ := by
      simp_rw [sub_eq_add_neg, character_add, character_neg_neg]
      simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul, mul_assoc, mul_comm _ (UnitAddTorus.mFourier wave offset),
        ← integral_const_mul]

/-- The full Fourier orbit is the actual translation of the same physical L² field. -/
theorem translate_eq_fourier (direction : Fin 3) (time : ℝ) (value : ScalarField) :
    translate (displacement direction time) value =
      (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
        (NativeSpatialTranslation.translate direction time ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr value)) := by
  apply (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext wave
  rw [UnitAddTorus.mFourierBasis_repr, translate_fourier, character_displacement]
  change _ = phase direction time wave * (UnitAddTorus.mFourierBasis (d := Fin 3)).repr value wave
  rw [UnitAddTorus.mFourierBasis_repr]

/-- The original spectral jet is the strong L² derivative of the actual spatial action. -/
theorem source_translation_hasDerivAt (state : ComplexVorticityHilbertState) (direction output : Fin 3) :
    HasDerivAt (fun time => translate (displacement direction time)
      (scalarField (wholeBiotSavartVelocityState state) output)) (field state direction output) 0 := by
  let inverse : ScalarSequence →L[ℝ] ScalarField :=
    ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have derivative := NativeSpatialTranslation.translate_hasDerivAt_zero direction
    (scalarSequence (wholeBiotSavartVelocityState state) output) (sequence state direction output) (fun _ => rfl)
  have physical := inverse.hasFDerivAt.comp_hasDerivAt 0 derivative
  have source (time : ℝ) : translate (displacement direction time) (scalarField (wholeBiotSavartVelocityState state) output) =
      inverse (NativeSpatialTranslation.translate direction time (scalarSequence (wholeBiotSavartVelocityState state) output)) := by
    rw [translate_eq_fourier, scalarField, LinearIsometryEquiv.apply_symm_apply]
    rfl
  simp only [source]
  convert! physical using 1

end
end SaturationMonoid.NavierStokes.NativePhysicalTranslation
