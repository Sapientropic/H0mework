import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Spectral.EigenGap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem actual_spectral_residual_small :
    ‖Occupation.residual‖ < (1 / 1000 : ℝ) := by
  rw [Occupation.residual_spectral,Unitary.conjStarAlgAut_apply]
  simp only [← Unitary.coe_star,CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul]
  rw [Occupation.residualDiagonal,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1 / 1000)).2
  intro i
  by_cases occupied : Occupation.occupied i
  · have identity : ‖(Occupation.gamma_hermitian.eigenvalues i : ℂ) - 2‖ =
        |Occupation.gamma_hermitian.eigenvalues i - 2| := by
        norm_cast
    simpa [Occupation.mask,occupied,identity] using occupied_eigenvalue_near_two i occupied
  · simpa [Occupation.mask,occupied,Complex.norm_real] using unoccupied_eigenvalue_near_zero i occupied

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
