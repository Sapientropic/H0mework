import H0mework.NavierStokes.MaterialJets.Geometry

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeCovariantMaterialEnergy

open PhysicsCore StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativeMaterialJetAction
open NativeCartanConstitutive NativeBalancedJetCoefficients NativeBalancedGaugeEnergy
open NativeGeometricMaterial

noncomputable section

def covariantBlock (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 3) : Block :=
  NativePauliJet.tangent (normalizedJet derivative direction.succ) +
    NativeGeometricMaterial.spatialBlock (normalizedVelocity velocity) (normalizedJet derivative) direction +
    NativeBalancedGaugeEnergy.spatialBlock (normalizedVelocity velocity) (normalizedJet derivative) direction +
    NativeConstitutiveMaterialEnergy.materialBlock velocity direction

theorem source_derivative (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 3) :
    NativeBalancedMaterialJet.derivative velocity derivative direction.succ = lowerMatter (covariantBlock velocity derivative direction) := by
  rw [NativeBalancedMaterialJet.derivative_split, NativeConstitutiveJet.derivative_split,
    covariantDerivative, freeDerivative, NativeGeometricMaterial.source_increment,
    NativeBalancedMaterialJet.freeCoefficients,
    NativeBalancedGaugeEnergy.source_increment, NativeConstitutiveMaterialEnergy.source_increment]
  simp only [covariantBlock, map_add]
  abel

theorem four_term_energy (first second third fourth : Block) :
    energy (first + second + third + fourth) ≤ 4 * (energy first + energy second + energy third + energy fourth) := by
  have combined := energy_add_le (first + second) (third + fourth)
  rw [← add_assoc] at combined
  linarith [energy_add_le first second, energy_add_le third fourth]

theorem curl_energy_bound (derivative : Fin 4 → Vector) :
    squared (curl derivative) ≤ 2 * ∑ direction : Fin 3, squared (derivative direction.succ) := by
  simp only [squared, curl, Fin.sum_univ_three]
  simp only [Matrix.cons_val]
  change (derivative 2 2 - derivative 3 1)^2 + (derivative 3 0 - derivative 1 2)^2 +
      (derivative 1 1 - derivative 2 0)^2 ≤
    2 * (derivative 1 0 ^ 2 + derivative 1 1 ^ 2 + derivative 1 2 ^ 2 +
      (derivative 2 0 ^ 2 + derivative 2 1 ^ 2 + derivative 2 2 ^ 2) +
      (derivative 3 0 ^ 2 + derivative 3 1 ^ 2 + derivative 3 2 ^ 2))
  nlinarith [sq_nonneg (derivative 2 2 + derivative 3 1), sq_nonneg (derivative 3 0 + derivative 1 2),
    sq_nonneg (derivative 1 1 + derivative 2 0), sq_nonneg (derivative 1 0), sq_nonneg (derivative 2 1),
    sq_nonneg (derivative 3 2)]

private theorem normalized_energy (velocity : PhysicalSpace) : squared (normalizedVelocity velocity) = ‖velocity‖ ^ 2 / 16 := by
  simp [squared, normalizedVelocity, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  ring

/-- Every actual spatial matter derivative is controlled by the original velocity and its complete first jet. -/
theorem block_energy_bound (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    (∑ direction, energy (covariantBlock velocity derivative direction)) ≤
      32 * ‖velocity‖ ^ 2 + 7 / 16 * ‖derivative 0‖ ^ 2 + 2 * ∑ direction : Fin 3, ‖derivative direction.succ‖ ^ 2 := by
  have source : (∑ direction : Fin 3, energy (covariantBlock velocity derivative direction)) ≤
      4 * ((∑ direction : Fin 3, energy (NativePauliJet.tangent (normalizedJet derivative direction.succ))) +
        (∑ direction : Fin 3, energy (NativeGeometricMaterial.spatialBlock (normalizedVelocity velocity) (normalizedJet derivative) direction)) +
        (∑ direction : Fin 3, energy (NativeBalancedGaugeEnergy.spatialBlock (normalizedVelocity velocity) (normalizedJet derivative) direction)) +
        (∑ direction : Fin 3, energy (NativeConstitutiveMaterialEnergy.materialBlock velocity direction))) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro direction _
    exact four_term_energy _ _ _ _
  have geometry := NativeGeometricMaterial.spatial_energy_bound (normalizedVelocity velocity) (normalizedJet derivative)
  have gauge := NativeBalancedGaugeEnergy.spatial_energy_bound (normalizedVelocity velocity) (normalizedJet derivative)
  have reaction := NativeConstitutiveMaterialEnergy.energy_bound velocity
  have curl := curl_energy_bound (normalizedJet derivative)
  rw [show (∑ direction : Fin 4, squared (normalizedJet derivative direction)) =
    squared (normalizedJet derivative 0) + ∑ direction : Fin 3, squared (normalizedJet derivative direction.succ)
      from Fin.sum_univ_succ _] at geometry
  simp only [tangent_energy, normalizedJet, normalized_energy, ← Finset.sum_div, ← Finset.mul_sum] at source geometry gauge curl
  linarith

theorem full_material_bound (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    (∑ direction : Fin 3, ‖matterCoordinateEquiv (NativeBalancedMaterialJet.derivative velocity derivative direction.succ)‖ ^ 2) ≤
      ‖materialEmbedding‖ ^ 2 *
        (32 * ‖velocity‖ ^ 2 + 7 / 16 * ‖derivative 0‖ ^ 2 + 2 * ∑ direction : Fin 3, ‖derivative direction.succ‖ ^ 2) := by
  simp only [source_derivative]
  calc
    _ ≤ ∑ direction : Fin 3, ‖materialEmbedding‖ ^ 2 * energy (covariantBlock velocity derivative direction) :=
      Finset.sum_le_sum fun _ _ => full_material_energy _
    _ = _ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (block_energy_bound velocity derivative) (sq_nonneg _)

end
end SaturationMonoid.NavierStokes.NativeCovariantMaterialEnergy
