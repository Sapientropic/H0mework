import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Coefficients

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem exchange_square : controllerEnvironmentExchange*controllerEnvironmentExchange =
    Matrix.diagonal (fun i : Fin 2 × Fin 2 => if i=(0,1) ∨ i=(1,0) then 1 else 0) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [controllerEnvironmentExchange,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.single_apply,Matrix.diagonal_apply]

theorem exchange_norm : ‖controllerEnvironmentExchange‖ ≤ 1 := by
  have squareNorm : ‖controllerEnvironmentExchange*controllerEnvironmentExchange‖ ≤ 1 := by
    rw [exchange_square,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    split_ifs <;> simp
  rw [exchange_hermitian.isSelfAdjoint.norm_mul_self] at squareNorm
  nlinarith [norm_nonneg controllerEnvironmentExchange]

def loadRegroup : Matrix (Pair × (Fin 2 × Fin 2)) (Pair × (Fin 2 × Fin 2)) ℂ ≃⋆ₐ[ℂ] LoadedJoint :=
  { Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc Pair (Fin 2) (Fin 2)).symm with
    map_star' := by intro A; rfl
    map_smul' := by intro c A; rfl }

theorem actual_load_interaction_norm : ‖loadInteraction‖ ≤ 1 := by
  change ‖loadRegroup (Matrix.kronecker (1 : Matrix Pair Pair ℂ) controllerEnvironmentExchange)‖ ≤ _
  rw [StarAlgEquiv.norm_map]
  exact (NonUnitalStarAlgHom.norm_apply_le (tensorRight (ι := Pair) (κ := Fin 2 × Fin 2)) _).trans exchange_norm

theorem actual_core_finite_error : ‖actualCoreInverse-numericCoreInverse‖ ≤ (26/1000 : ℝ) := by
  apply actual_core_error.trans
  unfold coreErrorBudget
  have first := mul_le_mul_of_nonneg_right source_cos_inverse_square
    (by positivity : (0 : ℝ) ≤ 126/10^12+‖(Real.sin BasisInverse.actualAngle : ℂ)^2‖*(44/10^12))
  have sum := add_le_add plus_coefficient_bound minus_coefficient_bound
  have product := mul_le_mul_of_nonneg_right sum (by norm_num : (0 : ℝ) ≤ 1/10^9)
  have final := mul_le_mul product actual_load_interaction_norm (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ (12000000+12000000)*(1/10^9))
  nlinarith [source_sin_square]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
