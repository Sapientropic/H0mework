import H0mework.Versions.X.NavierStokes.ConstitutiveAction.Material

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeConstitutiveMaterialEnergy

open PhysicsCore DiracExteriorMatterAction StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction
open NativeCartanConstitutive NativeCartanStressLaw NativeBalancedGaugeEnergy NativeConstitutiveMaterial

noncomputable section

private theorem source_increment_smul (velocity : PhysicalSpace) (scale : ℝ)
    (coefficients : Fin 4 → Fin 3 → ℝ) (direction : Fin 4) :
    NativeSourceColorAction.increment velocity (scale • coefficients) direction =
      (scale : ℂ) • NativeSourceColorAction.increment velocity coefficients direction := by
  have entry (index : Fin 4) (color : Fin 3) : (scale • coefficients) index color = scale * coefficients index color := rfl
  simp only [NativeSourceColorAction.increment_block, entry, Complex.ofReal_mul, mul_smul,
    ← Finset.smul_sum, map_smul, smul_comm (compensation velocity direction : ℂ) (scale : ℂ)]

def materialBlock (velocity : PhysicalSpace) (direction : Fin 3) : Block :=
  ((-8 / (NativeCanonicalFluidCoframe.scale velocity * fluxFactor (normalizedVelocity velocity)) : ℝ) : ℂ) •
    colorBlock (normalizedVelocity velocity) (NativeConstitutiveColor.radial (normalizedVelocity velocity) direction.succ)

theorem source_increment (velocity : PhysicalSpace) (direction : Fin 3) :
    NativeConstitutiveFlux.increment velocity direction.succ = lowerMatter (materialBlock velocity direction) := by
  rw [NativeConstitutiveFlux.increment, reaction_spatial, NativeConstitutiveColor.coefficients,
    source_increment_smul, ← add_smul, ← Complex.ofReal_add]
  have total : NativeCanonicalFluidCoframe.scale velocity ^ 2 / 2 + NativeConstitutiveColor.correctionScale velocity =
      -8 * NativeCanonicalFluidCoframe.scale velocity ^ 2 / fluxFactor (normalizedVelocity velocity) := by
    unfold NativeConstitutiveColor.correctionScale
    ring
  rw [total, NativeSourceColorAction.increment_block]
  have spatial : compensation velocity direction.succ = (NativeCanonicalFluidCoframe.density velocity)⁻¹ := by
    fin_cases direction <;> rfl
  rw [spatial, smul_smul, ← Complex.ofReal_mul]
  have scalar : -8 * NativeCanonicalFluidCoframe.scale velocity ^ 2 / fluxFactor (normalizedVelocity velocity) *
      (NativeCanonicalFluidCoframe.density velocity)⁻¹ =
      -8 / (NativeCanonicalFluidCoframe.scale velocity * fluxFactor (normalizedVelocity velocity)) := by
    rw [← NativeCanonicalFluidCoframe.scale_cube]
    field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne']
  rw [scalar, materialBlock, map_smul]
  rfl

theorem radial_energy (velocity : Vector) :
    (∑ direction : Fin 3, squared (NativeConstitutiveColor.radial velocity direction.succ)) =
      2 * squared velocity ^ 2 * (3 + 2 * squared velocity + 3 * squared velocity ^ 2) / denominator velocity ^ 2 := by
  calc
    _ = squared velocity ^ 2 + 2 * radialDiagonal velocity * squared velocity + 3 * radialDiagonal velocity ^ 2 := by
      simp_rw [radial_row]
      simp [squared, Fin.sum_univ_three]
      ring
    _ = _ := by
      unfold radialDiagonal
      field_simp [(denominator_pos velocity).ne']
      simp only [denominator, squared]
      ring

theorem energy_formula (velocity : PhysicalSpace) :
    (∑ direction, energy (materialBlock velocity direction)) =
      128 * NativeCanonicalFluidCoframe.scale velocity * squared (normalizedVelocity velocity)^2 /
        (3 + 2 * squared (normalizedVelocity velocity) + 3 * squared (normalizedVelocity velocity)^2) := by
  simp only [materialBlock, energy_smul, colorBlock_energy, ← mul_assoc, ← Finset.mul_sum]
  rw [radial_energy, ← NativeMaterialJetAction.source_density, ← NativeCanonicalFluidCoframe.scale_cube]
  unfold fluxFactor
  have numerator : 0 < 3 + 2 * squared (normalizedVelocity velocity) + 3 * squared (normalizedVelocity velocity)^2 := by
    have nonnegative : 0 ≤ squared (normalizedVelocity velocity) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne', (denominator_pos (normalizedVelocity velocity)).ne']
  ring

private theorem scale_le_density (velocity : PhysicalSpace) :
    NativeCanonicalFluidCoframe.scale velocity ≤ NativeCanonicalFluidCoframe.density velocity := by
  have large : 1 ≤ NativeCanonicalFluidCoframe.density velocity := by
    unfold NativeCanonicalFluidCoframe.density
    nlinarith [sq_nonneg ‖velocity‖]
  by_cases small : NativeCanonicalFluidCoframe.scale velocity ≤ 1
  · exact small.trans large
  have square : 1 ≤ NativeCanonicalFluidCoframe.scale velocity ^ 2 := by nlinarith
  have product := mul_le_mul_of_nonneg_left square (NativeCanonicalFluidCoframe.scale_pos velocity).le
  nlinarith [NativeCanonicalFluidCoframe.scale_cube velocity]

/-- The complete constitutive matter increment consumes the original velocity energy. -/
theorem energy_bound (velocity : PhysicalSpace) :
    (∑ direction, energy (materialBlock velocity direction)) ≤ 8 * ‖velocity‖ ^ 2 := by
  rw [energy_formula]
  have nonnegative : 0 ≤ squared (normalizedVelocity velocity) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have numerator : 0 < 3 + 2 * squared (normalizedVelocity velocity) + 3 * squared (normalizedVelocity velocity)^2 := by positivity
  have scale := scale_le_density velocity
  rw [NativeMaterialJetAction.source_density] at scale
  change NativeCanonicalFluidCoframe.scale velocity ≤ 2 * (1 + squared (normalizedVelocity velocity)) at scale
  have product : NativeCanonicalFluidCoframe.scale velocity * squared (normalizedVelocity velocity) ≤
      3 + 2 * squared (normalizedVelocity velocity) + 3 * squared (normalizedVelocity velocity)^2 := by
    have bound := mul_le_mul_of_nonneg_right scale nonnegative
    nlinarith [sq_nonneg (squared (normalizedVelocity velocity))]
  have norm : ‖velocity‖ ^ 2 = 16 * squared (normalizedVelocity velocity) := by
    simp [EuclideanSpace.norm_sq_eq, squared, normalizedVelocity, Fin.sum_univ_three]
    ring
  rw [norm]
  apply (div_le_iff₀ numerator).2
  have paid := mul_le_mul_of_nonneg_left product (show 0 ≤ 128 * squared (normalizedVelocity velocity) by positivity)
  nlinarith

theorem full_material_bound (velocity : PhysicalSpace) :
    (∑ direction : Fin 3, ‖matterCoordinateEquiv (NativeConstitutiveFlux.increment velocity direction.succ)‖ ^ 2) ≤
      8 * ‖materialEmbedding‖ ^ 2 * ‖velocity‖ ^ 2 := by
  simp only [source_increment]
  calc
    _ ≤ ∑ direction : Fin 3, ‖materialEmbedding‖ ^ 2 * energy (materialBlock velocity direction) :=
      Finset.sum_le_sum fun _ _ => full_material_energy _
    _ = _ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (energy_bound velocity) (sq_nonneg _)).trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeConstitutiveMaterialEnergy
