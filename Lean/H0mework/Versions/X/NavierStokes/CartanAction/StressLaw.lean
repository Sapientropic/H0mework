import H0mework.Versions.X.NavierStokes.CartanAction.Constitutive

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanStressLaw

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativeCartanClifford
open NativePauliPairing NativeCartanConstitutive NativeCartanMaterialResponse
open NativeMatterCoframeStress NativeSourceCoframeStress NativeCartanCompensation

noncomputable section

theorem cartanBlock_stress (velocity : Vector) (first second : Fin 3) :
    (blockPair (hermitianBlock velocity) (spinAction (cartanBlock velocity first.succ) second.succ)).im =
      2 * velocity first * velocity second + (1 - squared velocity)^2 / 2 * (if first = second then 1 else 0) := by
  fin_cases first <;> fin_cases second <;>
    simp [cartanBlock, NativeCartanCoordinates.profile, normalizedCurrent, NativePauliJet.density,
      blockPair, spinAction, spinPrincipal, blockAction, bivectorBlock, hermitianBlock, pauli,
      squared, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_six,
      Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem color_stress (velocity : Vector) (first second : Fin 3) :
    (blockPair (hermitianBlock velocity)
      (spinAction (colorAction (hermitianBlock velocity) first) second.succ)).im =
        2 * ((1 - squared velocity) * (if first = second then 1 else 0) +
          2 * velocity first * velocity second) := by
  fin_cases first <;> fin_cases second <;>
    simp [blockPair, spinAction, spinPrincipal, colorAction, hermitianBlock, pauli,
      squared, Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem correction_spatial (velocity : PhysicalSpace) (direction : Fin 3) :
    gaugeIncrement velocity (-response velocity) direction.succ =
      ((isotropicCorrection (NativeCanonicalFluidCoframe.scale velocity) (normalizedVelocity velocity) /
        NativeCanonicalFluidCoframe.density velocity : ℝ) : ℂ) •
        lowerMatter (colorAction (hermitianBlock (normalizedVelocity velocity)) direction) := by
  have coefficients := response_control (NativeCanonicalFluidCoframe.scale velocity) (normalizedVelocity velocity)
  simp only [Complex.ofReal_pow, neg_smul, ← response_eq] at coefficients
  simp only [gaugeIncrement, NativePauliCoframeAction.connection, source_matter,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply,
    gaugePotential_action, coefficients]
  fin_cases direction <;>
    simp [NativePauliControl.coefficients, Fin.sum_univ_three, compensation, smul_smul, div_eq_mul_inv,
      Complex.ofReal_mul, Complex.ofReal_inv, mul_comm]

private theorem scaled_kinetic (velocity : PhysicalSpace) (direction : Fin 4) (scale : ℝ) (block : Block) :
    (NativeCanonicalFluidCoframe.dual velocity
      (Complex.I • diracMatrixMatterAction (diracGamma direction) ((scale : ℂ) • lowerMatter block))).re =
        -scale * (blockPair (hermitianBlock (normalizedVelocity velocity)) (spinAction block direction)).im := by
  simp only [map_smul, smul_comm Complex.I (scale : ℂ)]
  rw [dual_gamma_block]
  simp [smul_eq_mul, Complex.mul_re, Complex.mul_im]

def fluxFactor (velocity : Vector) : ℝ :=
  (3 + 2 * squared velocity + 3 * squared velocity ^ 2) / denominator velocity

def pressure (velocity : Vector) : ℝ :=
  squared velocity * (1 - squared velocity)^2 / denominator velocity

theorem fluxFactor_pos (velocity : Vector) : 0 < fluxFactor velocity := by
  have nonnegative : 0 ≤ squared velocity := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact div_pos (by nlinarith [sq_nonneg (squared velocity)]) (denominator_pos velocity)

/-- Exact constitutive law for the actual Cartan reaction and its original color compensation. -/
theorem reaction_stress (velocity : PhysicalSpace) (first second : Fin 3) :
    NativeCartanStress.reactionStress velocity (Matrix.single first.succ second.succ 1) =
      fluxFactor (normalizedVelocity velocity) * normalizedVelocity velocity first * normalizedVelocity velocity second -
        pressure (normalizedVelocity velocity) * (if first = second then 1 else 0) := by
  rw [NativeCartanStress.reactionStress, responseCovector_spatial]
  simp only [NativeCartanStress.reactionCurrent, kineticCoefficients, compensatedIncrement,
    source_increment, correction_spatial, map_add, smul_add, Complex.add_re, scaled_kinetic,
    cartanBlock_stress, color_stress]
  have diagonal : NativeCanonicalFluidCoframe.diagonal velocity first.succ =
      (NativeCanonicalFluidCoframe.scale velocity)⁻¹ := by
    fin_cases first <;> rfl
  rw [diagonal, isotropicCorrection, ← NativeCanonicalFluidCoframe.scale_cube]
  unfold fluxFactor pressure
  have denom := (denominator_pos (normalizedVelocity velocity)).ne'
  have scale := (NativeCanonicalFluidCoframe.scale_pos velocity).ne'
  field_simp
  unfold denominator squared
  ring

end
end SaturationMonoid.NavierStokes.NativeCartanStressLaw
