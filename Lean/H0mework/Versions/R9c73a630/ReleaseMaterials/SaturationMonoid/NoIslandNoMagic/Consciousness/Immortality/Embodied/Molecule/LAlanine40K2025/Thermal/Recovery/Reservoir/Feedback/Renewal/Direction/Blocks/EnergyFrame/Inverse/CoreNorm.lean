import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Norm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] numericProjector numericLoadHamiltonian numericEnvironmentRead loadInteraction

theorem numeric_projector_norm : ‖numericProjector‖ ≤ 1 := by
  unfold numericProjector
  exact (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (ι := PairController) (κ := Fin 2)) Donor.calculatedDonor).trans
    (Donor.basis_projector_norm ((Donor.calculatedTop,Donor.calculatedTop),(1 : Fin 2)))

theorem numeric_core_norm : ‖numericCoreInverse‖ ≤ 2000000000 := by
  have env : ‖Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead‖ ≤ 12 :=
    (NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := PairController) (κ := Fin 2)) _).trans numeric_environment_norm
  have core : ‖numericLoadHamiltonian-(Real.sin BasisInverse.actualAngle : ℂ)^2 •
      Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead‖ ≤ 259 := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul]
    have h := mul_le_mul source_sin_square env (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    linarith [numeric_Hamiltonian_norm]
  have left : ‖numericProjector*loadInteraction‖ ≤ 1 := by
    exact (norm_mul_le numericProjector loadInteraction).trans (by nlinarith [numeric_projector_norm,actual_load_interaction_norm,norm_nonneg numericProjector,norm_nonneg loadInteraction])
  have right : ‖loadInteraction*numericProjector‖ ≤ 1 := by
    exact (norm_mul_le loadInteraction numericProjector).trans (by nlinarith [numeric_projector_norm,actual_load_interaction_norm,norm_nonneg numericProjector,norm_nonneg loadInteraction])
  unfold numericCoreInverse
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_smul]
  have first := mul_le_mul source_cos_inverse_square core (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 6000000)
  have second := mul_le_mul plus_coefficient_bound left (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 12000000)
  have third := mul_le_mul minus_coefficient_bound right (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 12000000)
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
