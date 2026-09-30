import H0mework.NavierStokes.CartanAction.Coordinates

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanConstitutive

open PhysicsCore DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativeCartanClifford
open NativeCartanCoordinates NativePauliPairing NativeCartanMaterialResponse

noncomputable section

def squared (velocity : Vector) : ℝ := ∑ direction, velocity direction ^ 2

def normalizedCurrent (velocity : Vector) : Fin 4 → ℝ :=
  ![NativePauliJet.density velocity, 4 * velocity 0, 4 * velocity 1, 4 * velocity 2]

theorem source_current (velocity : PhysicalSpace) :
    currentVector velocity = normalizedCurrent (normalizedVelocity velocity) := by
  funext direction
  fin_cases direction <;>
    simp [currentVector, normalizedCurrent, ← NativeMaterialJetAction.source_density, normalizedVelocity] <;> ring

def cartanBlock (velocity : Vector) (direction : Fin 4) : Block :=
  blockAction (∑ pair : Fin 6, ((profile (normalizedCurrent velocity) direction pair / 8 : ℝ) : ℂ) •
    bivectorBlock pair) (hermitianBlock velocity)

theorem source_increment (velocity : PhysicalSpace) (direction : Fin 4) :
    increment velocity direction = (NativeCanonicalFluidCoframe.diagonal velocity direction : ℂ) •
      lowerMatter (cartanBlock (normalizedVelocity velocity) direction) := by
  rw [increment, source_matter, spinBlock_action, NativeCartanCoordinates.contorsion_eq]
  simp only [spinBlock, candidate_component, source_current]
  have scale : (∑ pair : Fin 6,
      (((NativeCanonicalFluidCoframe.diagonal velocity direction *
        profile (normalizedCurrent (normalizedVelocity velocity)) direction pair / 4) / 2 : ℝ) : ℂ) •
          bivectorBlock pair) =
      (NativeCanonicalFluidCoframe.diagonal velocity direction : ℂ) •
        ∑ pair : Fin 6, ((profile (normalizedCurrent (normalizedVelocity velocity)) direction pair / 8 : ℝ) : ℂ) •
          bivectorBlock pair := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro pair _
    rw [smul_smul]
    congr 1
    push_cast
    ring
  rw [scale, blockAction_smul, map_smul]
  rfl

theorem inverse_compensation_diagonal (velocity : PhysicalSpace) (direction : Fin 4) :
    (compensation velocity direction)⁻¹ * NativeCanonicalFluidCoframe.diagonal velocity direction =
      NativeCanonicalFluidCoframe.scale velocity ^ 2 := by
  fin_cases direction <;> simp [compensation, NativeCanonicalFluidCoframe.diagonal,
    ← NativeCanonicalFluidCoframe.scale_cube]
  all_goals field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne']

def axialResponse (velocity : Vector) : Block :=
  ((3 / 4 * (1 - squared velocity) : ℝ) : ℂ) •
    (Complex.I • (1 - ∑ direction, (velocity direction : ℂ) • pauli direction))

theorem cartanBlock_response (velocity : Vector) :
    (∑ direction : Fin 4, spinAction (cartanBlock velocity direction) direction) = axialResponse velocity := by
  ext row column
  fin_cases row <;> fin_cases column <;> apply Complex.ext <;>
    simp [cartanBlock, profile, normalizedCurrent, NativePauliJet.density,
      spinAction, spinPrincipal, blockAction, bivectorBlock, hermitianBlock, pauli,
      axialResponse, squared, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four,
      Fin.sum_univ_six, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem response_eq (velocity : PhysicalSpace) :
    response velocity = (NativeCanonicalFluidCoframe.scale velocity ^ 2 : ℂ) •
      axialResponse (normalizedVelocity velocity) := by
  have actual := response_inverse velocity
  rw [actual_derivative_inverse] at actual
  have scalar (direction : Fin 4) : (compensation velocity direction : ℂ)⁻¹ *
      (NativeCanonicalFluidCoframe.diagonal velocity direction : ℂ) =
        ((NativeCanonicalFluidCoframe.scale velocity ^ 2 : ℝ) : ℂ) := by
    norm_cast
    exact inverse_compensation_diagonal velocity direction
  simp only [normalizedDerivative, source_increment, map_smul, spin_action, smul_smul, scalar] at actual
  rw [← Finset.smul_sum, ← map_sum, ← map_smul, cartanBlock_response] at actual
  have injective : Function.Injective lowerMatter := by
    intro first second equality
    rw [lowerMatter_apply, lowerMatter_apply] at equality
    have coordinates (spin : Fin 4) (color : Fin 2) := congrArg
      (fun matter => Stage9C.Material.SpinPair.sourceColorDoubletDual color (matter spin)) equality
    simp only [Stage9C.Material.SpinPair.sourceColorDoubletDual_diracMatter] at coordinates
    ext row column
    fin_cases row
    · fin_cases column
      · exact coordinates 2 0
      · exact coordinates 2 1
    · fin_cases column
      · exact coordinates 3 0
      · exact coordinates 3 1
  simpa only [Complex.ofReal_pow] using (injective actual).symm

def isotropicCorrection (scale : ℝ) (velocity : Vector) : ℝ :=
  -(3 / 4 * scale ^ 2 * (1 - squared velocity) * (1 + squared velocity) / denominator velocity)

theorem response_control (scale : ℝ) (velocity : Vector) :
    control velocity (-((scale ^ 2 : ℝ) : ℂ) • axialResponse velocity) =
      coefficients (fun direction => 3 / 2 * scale ^ 2 * (1 - squared velocity) /
        denominator velocity * velocity direction) 0 (isotropicCorrection scale velocity) := by
  unfold NativePauliControl.control
  congr 1
  · funext direction
    fin_cases direction <;>
      simp [temporal, isotropic, axialResponse, imagScalar, imagVector, pauli,
        squared, denominator, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, pow_two]
    all_goals field_simp [(denominator_pos velocity).ne']
    all_goals ring
  · funext direction
    fin_cases direction <;>
      simp [NativePauliControl.rotation, axialResponse, realVector, imagVector, pauli, squared,
        Fin.sum_univ_three, cross_apply, Complex.mul_re, Complex.mul_im, pow_two] <;> ring
  · simp [isotropic, isotropicCorrection, axialResponse, imagScalar, imagVector, pauli,
      squared, denominator, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, pow_two]
    ring

end
end SaturationMonoid.NavierStokes.NativeCartanConstitutive
