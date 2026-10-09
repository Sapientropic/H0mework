import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Numeric

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] actualProjector numericProjector actualDonor actualHamiltonian numericLoadHamiltonian loadInteraction

def coreErrorBudget : ℝ := ‖((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹‖*
    (126/10^12+‖(Real.sin BasisInverse.actualAngle : ℂ)^2‖*(44/10^12))+
    (‖plusCoefficient‖+‖minusCoefficient‖)*(1/10^9)*‖loadInteraction‖

theorem actual_core_error : ‖actualCoreInverse-numericCoreInverse‖ ≤ coreErrorBudget := by
  let D := actualProjector-numericProjector
  let S := Matrix.kronecker (1 : Matrix PairController PairController ℂ) (sourceEnvironmentRead-numericEnvironmentRead)
  have sbound : ‖S‖ ≤ (44/10^12 : ℝ) :=
    (NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := PairController) (κ := Fin 2)) _).trans original_environment_error
  have split : actualCoreInverse-numericCoreInverse =
      ((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹ •
        ((actualHamiltonian-numericLoadHamiltonian)-(Real.sin BasisInverse.actualAngle : ℂ)^2 • S)+
      plusCoefficient • (D*loadInteraction)+minusCoefficient • (loadInteraction*D) := by
    unfold actualCoreInverse numericCoreInverse
    have tensor : S = Matrix.kronecker (1 : Matrix PairController PairController ℂ) sourceEnvironmentRead-
        Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead := by
      ext i j
      simp only [S,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
      ring
    rw [tensor]
    dsimp only [D]
    simp only [Matrix.sub_mul,Matrix.mul_sub,smul_sub]
    abel
  have first : ‖(actualHamiltonian-numericLoadHamiltonian)-(Real.sin BasisInverse.actualAngle : ℂ)^2 • S‖ ≤
      126/10^12+‖(Real.sin BasisInverse.actualAngle : ℂ)^2‖*(44/10^12) := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul]
    exact add_le_add actual_hamiltonian_distance (mul_le_mul_of_nonneg_left sbound (norm_nonneg _))
  have left : ‖D*loadInteraction‖ ≤ (1/10^9 : ℝ)*‖loadInteraction‖ :=
    (norm_mul_le D loadInteraction).trans (mul_le_mul_of_nonneg_right (show ‖D‖ ≤ (1/10^9 : ℝ) from original_projector_error) (norm_nonneg loadInteraction))
  have right : ‖loadInteraction*D‖ ≤ ‖loadInteraction‖*(1/10^9 : ℝ) :=
    (norm_mul_le loadInteraction D).trans (mul_le_mul_of_nonneg_left (show ‖D‖ ≤ (1/10^9 : ℝ) from original_projector_error) (norm_nonneg loadInteraction))
  rw [split]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_smul]
  unfold coreErrorBudget
  nlinarith [mul_le_mul_of_nonneg_left first (norm_nonneg (((Real.cos BasisInverse.actualAngle : ℂ)^2)⁻¹)),
    mul_le_mul_of_nonneg_left left (norm_nonneg plusCoefficient),mul_le_mul_of_nonneg_left right (norm_nonneg minusCoefficient)]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
