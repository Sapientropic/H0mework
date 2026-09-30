import H0mework.Versions.X.NavierStokes.MaterialJets.Jet

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeConstitutiveMaterial

open PhysicsCore DiracExteriorMatterAction
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativeCartanClifford
open NativeCartanConstitutive NativeCartanStressLaw NativeBalancedGaugeEnergy

noncomputable section

theorem cartanBlock_color (velocity : Vector) (direction : Fin 3) :
    cartanBlock velocity direction.succ = ((velocity direction / 2 : ℝ) : ℂ) • colorBlock velocity velocity +
      (((1 - squared velocity) / 4 : ℝ) : ℂ) • colorAction (hermitianBlock velocity) direction := by
  ext row column
  fin_cases direction <;> fin_cases row <;> fin_cases column <;> apply Complex.ext <;>
    simp [cartanBlock, NativeCartanCoordinates.profile, normalizedCurrent, NativePauliJet.density,
      blockAction, bivectorBlock, colorBlock, colorAction, hermitianBlock, pauli, squared,
      Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_six, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

private theorem colorBlock_rankOne (velocity : Vector) (scale diagonal : ℝ) (direction : Fin 3) :
    colorBlock velocity (fun color => scale * velocity color + diagonal * (if direction = color then 1 else 0)) =
      (scale : ℂ) • colorBlock velocity velocity + (diagonal : ℂ) • colorAction (hermitianBlock velocity) direction := by
  simp [colorBlock, Complex.ofReal_add, add_smul, Finset.sum_add_distrib, Complex.ofReal_mul,
    mul_smul, Finset.smul_sum, mul_ite, ite_smul]

def radialDiagonal (velocity : Vector) : ℝ :=
  squared velocity * (squared velocity - 1) / denominator velocity

theorem radial_row (velocity : Vector) (direction : Fin 3) :
    NativeConstitutiveColor.radial velocity direction.succ = fun color =>
      velocity direction * velocity color + radialDiagonal velocity * (if direction = color then 1 else 0) := by
  funext color
  fin_cases direction <;> fin_cases color <;> simp [NativeConstitutiveColor.radial, radialDiagonal]

theorem radial_block (velocity : Vector) (direction : Fin 3) :
    colorBlock velocity (NativeConstitutiveColor.radial velocity direction.succ) =
      (velocity direction : ℂ) • colorBlock velocity velocity +
        (radialDiagonal velocity : ℂ) • colorAction (hermitianBlock velocity) direction := by
  rw [radial_row, colorBlock_rankOne]

/-- The original Cartan reaction on the complete source matter is the same computed radial color-kernel response. -/
theorem cartanBlock_radial (velocity : Vector) (direction : Fin 3) :
    cartanBlock velocity direction.succ + (isotropicCorrection 1 velocity : ℂ) • colorAction (hermitianBlock velocity) direction =
      (1 / 2 : ℂ) • colorBlock velocity (NativeConstitutiveColor.radial velocity direction.succ) := by
  have scalar : (1 - squared velocity) / 4 + isotropicCorrection 1 velocity = radialDiagonal velocity / 2 := by
    simp only [isotropicCorrection, radialDiagonal, one_pow, mul_one]
    field_simp [(denominator_pos velocity).ne']
    simp only [denominator, squared]
    ring
  have scalarComplex : (((1 - squared velocity) / 4 : ℝ) : ℂ) + (isotropicCorrection 1 velocity : ℂ) =
      ((radialDiagonal velocity / 2 : ℝ) : ℂ) := by exact_mod_cast scalar
  rw [cartanBlock_color, radial_block]
  calc
    _ = ((velocity direction / 2 : ℝ) : ℂ) • colorBlock velocity velocity +
        ((((1 - squared velocity) / 4 : ℝ) : ℂ) + (isotropicCorrection 1 velocity : ℂ)) •
          colorAction (hermitianBlock velocity) direction := by module
    _ = _ := by
      rw [scalarComplex]
      push_cast
      module

theorem reaction_spatial (velocity : PhysicalSpace) (direction : Fin 3) :
    NativeCartanCompensation.compensatedIncrement velocity direction.succ =
      ((NativeCanonicalFluidCoframe.scale velocity ^ 2 / 2 : ℝ) : ℂ) •
        NativeSourceColorAction.increment velocity (NativeConstitutiveColor.radial (normalizedVelocity velocity)) direction.succ := by
  rw [NativeCartanCompensation.compensatedIncrement, NativeCartanConstitutive.source_increment,
    correction_spatial, NativeSourceColorAction.increment_block]
  have diagonal : NativeCanonicalFluidCoframe.diagonal velocity direction.succ =
      (NativeCanonicalFluidCoframe.scale velocity)⁻¹ := by fin_cases direction <;> rfl
  have compensation : NativePauliCoframeAction.compensation velocity direction.succ =
      (NativeCanonicalFluidCoframe.density velocity)⁻¹ := by fin_cases direction <;> rfl
  rw [diagonal, compensation]
  have factor : isotropicCorrection (NativeCanonicalFluidCoframe.scale velocity) (normalizedVelocity velocity) /
      NativeCanonicalFluidCoframe.density velocity = (NativeCanonicalFluidCoframe.scale velocity)⁻¹ *
        isotropicCorrection 1 (normalizedVelocity velocity) := by
    rw [← NativeCanonicalFluidCoframe.scale_cube]
    unfold isotropicCorrection
    field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne']
  have half : NativeCanonicalFluidCoframe.scale velocity ^ 2 / 2 *
      (NativeCanonicalFluidCoframe.density velocity)⁻¹ = (NativeCanonicalFluidCoframe.scale velocity)⁻¹ * (1 / 2) := by
    rw [← NativeCanonicalFluidCoframe.scale_cube]
    field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne']
  have scaled := congrArg (fun block => (((NativeCanonicalFluidCoframe.scale velocity)⁻¹ : ℝ) : ℂ) • lowerMatter block)
    (cartanBlock_radial (normalizedVelocity velocity) direction)
  simp only [map_add, map_smul, smul_add, smul_smul] at scaled
  rw [factor]
  have coefficient : ((NativeCanonicalFluidCoframe.scale velocity ^ 2 / 2 : ℝ) : ℂ) *
      (((NativeCanonicalFluidCoframe.density velocity)⁻¹ : ℝ) : ℂ) =
      (((NativeCanonicalFluidCoframe.scale velocity)⁻¹ : ℝ) : ℂ) * (1 / 2 : ℂ) := by
    convert congrArg Complex.ofReal half using 1 <;> push_cast <;> rfl
  rw [smul_smul, coefficient]
  simpa only [Complex.ofReal_mul, colorBlock] using scaled

end
end SaturationMonoid.NavierStokes.NativeConstitutiveMaterial
