import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Source.DiagonalBounds
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Dynamics.SourceGeneratedMaximalCharge
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Source.PreparationEnergy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.SourceBounds

open Propagation.Interface Propagation.Source Recovery.SourcePrimitive Collision
open scoped Matrix ComplexOrder
noncomputable section

theorem negative_lower_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (i : ι) :
    Gershgorin.lowerDiagonal (-H) i = Gershgorin.lowerDiagonal H i - 2 * (H i i).re := by
  simp only [Gershgorin.lowerDiagonal, Matrix.neg_apply, Complex.neg_re, norm_neg]
  ring

theorem source_negative_lower_diagonal (i : Basis) :
    Gershgorin.lowerDiagonal (-activeMatrix electronicSource) i =
      ((sourceGershDiagonal i - 2 * activeNumerator electronicSource i i : ℤ) : ℝ) / 1000000000000000 := by
  rw [negative_lower_diagonal, source_lowerDiagonal]
  norm_num [activeMatrix, Complex.div_re, Int.cast_sub, Int.cast_mul]
  ring

theorem gramUpperMargin_read :
    (∑ i : Basis, Gershgorin.lowerDiagonal (-activeMatrix electronicSource) i *
      ∑ j : Basis, ‖initialDensityMatrix electronicSource i j‖ ^ 2) +
      2 * Preparation.gramMass (initialDensityMatrix electronicSource) =
        (gramUpperMargin : ℝ) / 1000000000000000000000000000000000000000 := by
  simp only [source_negative_lower_diagonal, source_density_rowNorm, source_gramMass_rowRead,
    gramUpperMargin, Int.cast_sum, Finset.sum_div, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [(sourceRows_cache_exact i).1, (sourceRows_cache_exact i).2, diagonal_exact i]
  push_cast
  ring

theorem source_gram_mean_lt_two :
    energy (activeMatrix electronicSource) (Preparation.normalizedGram (initialDensityMatrix electronicSource)) < 2 := by
  have margin : (0 : ℝ) < (gramUpperMargin : ℝ) / 1000000000000000000000000000000000000000 :=
    div_pos (Int.cast_pos.mpr gramUpperMargin_positive) (by norm_num)
  rw [← gramUpperMargin_read] at margin
  have weighted : -2 < (Preparation.gramMass (initialDensityMatrix electronicSource))⁻¹ *
      ∑ i : Basis, Gershgorin.lowerDiagonal (-activeMatrix electronicSource) i *
        ∑ j : Basis, ‖initialDensityMatrix electronicSource i j‖ ^ 2 := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (lt_div_iff₀ sourceGramMass_positive).mpr
    linarith
  have lower := weighted.trans_le (Gershgorin.normalizedGram_lower _ _
    (Propagation.Dynamics.activeMatrix_hermitian electronicSource).neg)
  rw [Maximum.negative_energy] at lower
  linarith

theorem source_system_gram_mean : energy Thermal.Source.energyHamiltonian Thermal.Source.systemCurrent =
    energy (activeMatrix electronicSource) (Preparation.normalizedGram (initialDensityMatrix electronicSource)) := by
  have invariant := Work.Capacity.energy_unitary_conjugation (activeMatrix electronicSource)
    (Preparation.preparedDensity (Preparation.collisionCurrentTime : ℝ)) (star Preparation.sourceEnergyFrame)
  change energy (Quantum.conjugation (star Preparation.sourceEnergyFrame) (activeMatrix electronicSource))
    (Quantum.conjugation (star Preparation.sourceEnergyFrame)
      (Preparation.preparedDensity (Preparation.collisionCurrentTime : ℝ))) = _ at invariant
  rw [Powered.Source.sourceHamiltonian_in_shared_frame, Powered.Source.sourceCoordinates_as_conjugation] at invariant
  exact invariant.trans (PreparationEnergy.preparedDensity_energy _)

theorem source_system_mean_lt_two : energy Thermal.Source.energyHamiltonian Thermal.Source.systemCurrent < 2 := by
  rw [source_system_gram_mean]
  exact source_gram_mean_lt_two

end
end LAlanine40K2025.Thermal.Recovery.Charging.SourceBounds
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
