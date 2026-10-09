import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Integrability

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource SourceCoulomb MeasureTheory
open scoped BigOperators
noncomputable section

def pairInteraction (i j k l : Basis) : ℝ :=
  ∫ z : Point × Point,
    sourcePair i j z.1 * sourcePair k l z.2 * kernel (z.2 - z.1)

theorem pair_interaction_source (i j k l : Basis) :
    pairInteraction i j k l = electronRepulsion i j k l := by
  unfold pairInteraction electronRepulsion
  congr 1
  funext z
  rw [← source_pair_exact i j z.1,← source_pair_exact k l z.2]

theorem pair_interaction_integrable (i j k l : Basis) :
    Integrable (fun z : Point × Point =>
      sourcePair i j z.1 * sourcePair k l z.2 * kernel (z.2 - z.1)) := by
  convert quartet_integrable i j k l using 1
  funext z
  rw [← source_pair_exact i j z.1,← source_pair_exact k l z.2]

theorem original_primitive_integrable (i j k l : Basis)
    (left right nextLeft nextRight : Term)
    (hleft : left ∈ sourceTerms i) (hright : right ∈ sourceTerms j)
    (hnextLeft : nextLeft ∈ sourceTerms k) (hnextRight : nextRight ∈ sourceTerms l) :
    Integrable (fun z : Point × Point =>
      pairShape left right z.1 * pairShape nextLeft nextRight z.2 *
        kernel (z.2 - z.1)) :=
  pair_kernel_integrable left right nextLeft nextRight
    (source_exponents_positive i left hleft) (source_exponents_positive j right hright)
    (source_exponents_positive k nextLeft hnextLeft)
    (source_exponents_positive l nextRight hnextRight)

theorem sourceJ_pair_normal_form (i j : Basis) :
    AO.sourceJ i j =
      ∑ k : Basis, ∑ l : Basis,
        Proxy.Correction.d3AO k l * pairInteraction k l i j := by
  simp only [AO.sourceJ,pair_interaction_source]

theorem original_hartree_pair_normal_form :
    Interaction.d3HartreeEnergy = (1 / 2 : ℝ) *
      ∑ i : Basis, ∑ j : Basis,
        Proxy.Correction.d3AO i j *
          (∑ k : Basis, ∑ l : Basis,
            Proxy.Correction.d3AO k l * pairInteraction k l i j) := by
  rw [AO.original_D3_hartree_sourceJ]
  simp only [sourceJ_pair_normal_form]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
