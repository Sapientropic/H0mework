import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient
open scoped Matrix BigOperators
noncomputable section

def residualMatrix (i k : Basis) : ℝ :=
  normalizedDensityMatrix i k - 2 * (projector24 i k).re

theorem original_D3_density_expansion (x : Point) :
    sourceDensity x = ∑ i : Basis, ∑ k : Basis,
      normalizedDensityMatrix i k * normalizedOrbital i x * normalizedOrbital k x := by
  rw [← actual_density_preserved actual_gram_positive]
  simp only [normalizedDensity,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem projected_density_expansion (x : Point) :
    projectedDensity x = ∑ i : Basis, ∑ k : Basis,
      (2 * (projector24 i k).re) * normalizedOrbital i x * normalizedOrbital k x := by
  simp only [projectedDensity,oneBodyKernel,Complex.re_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.re_mul_ofReal,Complex.re_mul_ofReal]
  ring

theorem original_D3_spatial_residual (x : Point) :
    densityResidual x = ∑ i : Basis, ∑ k : Basis,
      residualMatrix i k * normalizedOrbital i x * normalizedOrbital k x := by
  rw [densityResidual,original_D3_density_expansion,projected_density_expansion]
  simp only [residualMatrix]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
