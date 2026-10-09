import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.J

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
open scoped BigOperators
noncomputable section

structure Material where
  parent : SourceJoin.Material
  heatQuartet : Basis → Basis → Basis → Basis → ℝ
  heatTargetJ : Matrix Basis Basis ℝ
  heatHartree : ℝ

def material : Material where
  parent := SourceJoin.material
  heatQuartet := pairInteractionHeatFinite
  heatTargetJ := Matrix.of targetHeatJ
  heatHartree := (1 / 2 : ℝ) *
    ∑ i : Basis, ∑ j : Basis,
      Proxy.Correction.d3AO i j *
        (∑ k : Basis, ∑ l : Basis,
          Proxy.Correction.d3AO k l * pairInteractionHeatFinite k l i j)

theorem parent_identity : material.parent = SourceJoin.material := rfl

theorem quartet_exact (i j k l : Basis) :
    material.heatQuartet i j k l = electronRepulsion i j k l :=
  (electron_repulsion_heat_finite i j k l).symm

theorem target_J_exact (i j : Basis) :
    material.heatTargetJ i j = material.parent.targetJ i j :=
  (target_heat_J_exact i j).symm

theorem hartree_exact :
    material.heatHartree = Interaction.d3HartreeEnergy :=
  original_hartree_heat_finite.symm

structure Closure : Prop where
  parent : SourceJoin.Closure
  kernel : type_of% kernel_laplace
  nullDiagonal : type_of% product_diagonal_null
  heatIntegrability : type_of% primitive_heat_integrable
  primitiveFubini : type_of% primitive_interaction_heat_swapped
  sourcePrimitive : type_of% source_primitive_heat
  sourceQuartet : type_of% electron_repulsion_heat_finite
  sourceTargetJ : type_of% target_heat_J_exact
  sourceHartree : type_of% original_hartree_heat_finite
  parentIdentity : type_of% parent_identity
  quartet : type_of% quartet_exact
  targetJ : type_of% target_J_exact
  hartree : type_of% hartree_exact

theorem sourceGeneratedClosure : Closure :=
  ⟨SourceJoin.sourceGeneratedClosure,kernel_laplace,product_diagonal_null,
    primitive_heat_integrable,primitive_interaction_heat_swapped,
    source_primitive_heat,electron_repulsion_heat_finite,
    target_heat_J_exact,original_hartree_heat_finite,
    parent_identity,quartet_exact,target_J_exact,hartree_exact⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
