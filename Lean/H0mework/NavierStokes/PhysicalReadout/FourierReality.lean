import Mathlib.Analysis.Fourier.AddCircleMulti

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeFourierReality

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate ENNReal

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

local notation "TorusL2" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

/-- Conjugation of the complete L² field reflects its original Fourier coefficients. -/
theorem mFourierCoeff_star (f : TorusL2) (wave : d → ℤ) :
    mFourierCoeff (star f : TorusL2) wave = conj (mFourierCoeff f (-wave)) := by
  unfold mFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with point equality
  simp only [Pi.star_apply] at equality
  rw [equality, neg_neg, mFourier_neg]
  simp only [smul_eq_mul, map_mul, starRingEnd_apply]

/-- Fourier reality identifies the original L² field with its own conjugate. -/
theorem star_eq_self_of_fourier_reality (f : TorusL2)
    (reality : ∀ wave : d → ℤ, mFourierCoeff f (-wave) = conj (mFourierCoeff f wave)) :
    star f = f := by
  apply (mFourierBasis (d := d)).repr.injective
  apply lp.ext
  funext wave
  rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_star, reality]
  simp

/-- The same complete field is real almost everywhere on normalized torus volume. -/
theorem im_ae_zero_of_fourier_reality (f : TorusL2)
    (reality : ∀ wave : d → ℤ, mFourierCoeff f (-wave) = conj (mFourierCoeff f wave)) :
    ∀ᵐ point ∂(volume : Measure (UnitAddTorus d)), (f point).im = 0 := by
  have conjugate := Lp.coeFn_star f
  rw [star_eq_self_of_fourier_reality f reality] at conjugate
  filter_upwards [conjugate] with point equality
  apply Complex.conj_eq_iff_im.mp
  simpa only [Pi.star_apply, starRingEnd_apply] using equality.symm

/-- Scalar ℓ² source reality survives the actual inverse Fourier isometry. -/
theorem inverseFourier_star_eq_self
    (coefficients : lp (fun _ : d → ℤ => ℂ) 2)
    (reality : ∀ wave : d → ℤ, coefficients (-wave) = conj (coefficients wave)) :
    star ((mFourierBasis (d := d)).repr.symm coefficients) =
      (mFourierBasis (d := d)).repr.symm coefficients := by
  apply star_eq_self_of_fourier_reality
  intro wave
  simpa only [← mFourierBasis_repr, LinearIsometryEquiv.apply_symm_apply] using reality wave

theorem inverseFourier_im_ae_zero
    (coefficients : lp (fun _ : d → ℤ => ℂ) 2)
    (reality : ∀ wave : d → ℤ, coefficients (-wave) = conj (coefficients wave)) :
    ∀ᵐ point ∂(volume : Measure (UnitAddTorus d)),
      (((mFourierBasis (d := d)).repr.symm coefficients) point).im = 0 := by
  apply im_ae_zero_of_fourier_reality
  intro wave
  simpa only [← mFourierBasis_repr, LinearIsometryEquiv.apply_symm_apply] using reality wave

end
end SaturationMonoid.NavierStokes.NativeFourierReality
