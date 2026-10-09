import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.Kernel

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
open scoped BigOperators
noncomputable section

def sourceJ (i j : Basis) : ℝ :=
  ∑ k : Basis, ∑ l : Basis,
    Proxy.Correction.d3AO k l * electronRepulsion k l i j

theorem sourceJ_physical_order (i j : Basis) :
    sourceJ i j = ∑ k : Basis, ∑ l : Basis,
      Proxy.Correction.d3AO k l * electronRepulsion i j k l := by
  unfold sourceJ
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [electronRepulsion_pair_swap k l i j]

theorem sourceJ_symmetric (i j : Basis) : sourceJ i j = sourceJ j i := by
  unfold sourceJ
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [electronRepulsion_second_swap k l i j]

theorem four_center_sourceJ :
    fourCenter Proxy.Correction.d3AO Proxy.Correction.d3AO =
      ∑ i : Basis, ∑ j : Basis,
        Proxy.Correction.d3AO i j * sourceJ i j := by
  simp only [fourCenter,sourceJ,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem original_D3_hartree_AO :
    Interaction.d3HartreeEnergy =
      (1 / 2 : ℝ) * fourCenter Proxy.Correction.d3AO Proxy.Correction.d3AO := by
  unfold Interaction.d3HartreeEnergy
  have same (z : Point × Point) :
      sourceDensity z.1 * sourceDensity z.2 * kernel (z.2 - z.1) =
        pairIntegrand Proxy.Correction.d3AO Proxy.Correction.d3AO z := by
    simp only [pairIntegrand,source_density_ao]
  simp_rw [same]
  rw [pair_integral_four_center]

theorem original_D3_hartree_sourceJ :
    Interaction.d3HartreeEnergy =
      (1 / 2 : ℝ) * ∑ i : Basis, ∑ j : Basis,
        Proxy.Correction.d3AO i j * sourceJ i j := by
  rw [original_D3_hartree_AO,four_center_sourceJ]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
