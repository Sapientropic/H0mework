import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Gram

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem state_norm_le_one (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) (normalized : rho.trace=1) : ‖rho‖ ≤ 1 := by
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ _ (star positive.isHermitian.eigenvectorUnitary)) rho
  rw [positive.isHermitian.conjStarAlgAut_star_eigenvectorUnitary,Matrix.l2_opNorm_diagonal] at same
  rw [← same]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro i
  have bound : positive.isHermitian.eigenvalues i ≤ ∑ j,positive.isHermitian.eigenvalues j :=
    Finset.single_le_sum (fun j _ => positive.eigenvalues_nonneg j) (Finset.mem_univ i)
  rw [Thermal.Quantum.eigenvalues_normalized rho positive normalized] at bound
  simpa only [Function.comp_apply,RCLike.norm_ofReal,Real.norm_eq_abs,abs_of_nonneg (positive.eigenvalues_nonneg i)] using bound

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
