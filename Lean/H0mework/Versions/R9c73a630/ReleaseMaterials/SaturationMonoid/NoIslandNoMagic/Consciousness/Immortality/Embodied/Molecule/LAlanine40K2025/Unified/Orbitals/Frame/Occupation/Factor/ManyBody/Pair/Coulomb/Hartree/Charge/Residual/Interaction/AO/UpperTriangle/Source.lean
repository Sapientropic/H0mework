import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.Sum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb
open scoped BigOperators
noncomputable section

def sourceJUpper (i j : Basis) : ℝ :=
  (∑ k : Basis, Proxy.Correction.d3AO k k * electronRepulsion k k i j) +
    (∑ k : Basis, ∑ l : Basis,
      if k < l then
        (Proxy.Correction.d3AO k l + Proxy.Correction.d3AO l k) *
          electronRepulsion k l i j else 0)

theorem sourceJ_eq_upper (i j : Basis) : AO.sourceJ i j = sourceJUpper i j := by
  unfold AO.sourceJ sourceJUpper
  rw [full_sum_upper_pair
    (fun k l => Proxy.Correction.d3AO k l * electronRepulsion k l i j)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  split_ifs with h
  · rw [electronRepulsion_first_swap l k i j]
    ring
  · rfl

theorem sourceJUpper_symmetric (i j : Basis) :
    sourceJUpper i j = sourceJUpper j i := by
  rw [← sourceJ_eq_upper, ← sourceJ_eq_upper]
  exact AO.sourceJ_symmetric i j

def hartreeUpper : ℝ := (1 / 2 : ℝ) *
  ((∑ i : Basis, Proxy.Correction.d3AO i i * sourceJUpper i i) +
    (∑ i : Basis, ∑ j : Basis,
      if i < j then
        (Proxy.Correction.d3AO i j + Proxy.Correction.d3AO j i) *
          sourceJUpper i j else 0))

theorem original_hartree_eq_upper :
    Interaction.d3HartreeEnergy = hartreeUpper := by
  rw [AO.original_D3_hartree_sourceJ]
  simp only [sourceJ_eq_upper]
  unfold hartreeUpper
  congr 1
  rw [full_sum_upper_pair
    (fun i j => Proxy.Correction.d3AO i j * sourceJUpper i j)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · rw [sourceJUpper_symmetric j i]
    ring
  · rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
