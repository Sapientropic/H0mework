import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair.Finite
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
open scoped BigOperators
noncomputable section

structure Material where
  parent : AO.Material
  pairField : Basis → Basis → Point → ℝ
  primitiveQuartet : Basis → Basis → Basis → Basis → ℝ
  primitiveJ : Matrix Basis Basis ℝ

def material : Material where
  parent := AO.material
  pairField := sourcePair
  primitiveQuartet := pairInteractionFinite
  primitiveJ := Matrix.of (fun i j =>
    ∑ k : Basis, ∑ l : Basis,
      Proxy.Correction.d3AO k l * pairInteractionFinite k l i j)

theorem parent_identity : material.parent = AO.material := rfl
theorem pair_field_exact (i j : Basis) (x : Point) :
    ao i x * ao j x = material.pairField i j x := source_pair_exact i j x
theorem primitive_quartet_exact (i j k l : Basis) :
    material.primitiveQuartet i j k l = electronRepulsion i j k l :=
  (pair_interaction_finite i j k l).symm.trans (pair_interaction_source i j k l)
theorem primitive_source_integrable (i j k l : Basis)
    (left right nextLeft nextRight : Term)
    (hleft : left ∈ sourceTerms i) (hright : right ∈ sourceTerms j)
    (hnextLeft : nextLeft ∈ sourceTerms k) (hnextRight : nextRight ∈ sourceTerms l) :
    Integrable (fun z : Point × Point =>
      pairShape left right z.1 * pairShape nextLeft nextRight z.2 *
        kernel (z.2 - z.1)) :=
  original_primitive_integrable i j k l left right nextLeft nextRight
    hleft hright hnextLeft hnextRight
theorem source_J_from_primitives (i j : Basis) :
    material.parent.jPotential i j = material.primitiveJ i j :=
  sourceJ_primitive_finite i j
theorem hartree_from_primitives :
    material.parent.hartree = (1 / 2 : ℝ) *
      ∑ i : Basis, ∑ j : Basis,
        material.parent.densityAO i j * material.primitiveJ i j :=
  original_hartree_primitive_finite

structure Closure : Prop where
  parent : AO.Closure
  parentIdentity : type_of% parent_identity
  pairField : type_of% pair_field_exact
  quartet : type_of% primitive_quartet_exact
  integrability : type_of% primitive_source_integrable
  potential : type_of% source_J_from_primitives
  energy : type_of% hartree_from_primitives

theorem sourceGeneratedClosure : Closure :=
  ⟨AO.sourceGeneratedClosure,parent_identity,pair_field_exact,
    primitive_quartet_exact,primitive_source_integrable,
    source_J_from_primitives,hartree_from_primitives⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
