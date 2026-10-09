import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.TargetClass
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SFamily
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : Axis.Material
  sBases : Finset Basis
  sAddresses : Finset (Fin 4851)
  sTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := Axis.material
  sBases := Axis.sourceSBases
  sAddresses := Axis.sourceSTargetAddresses
  sTargetJ := Axis.targetSHeatJ

theorem parent_identity : material.parent = Axis.material := rfl
theorem s_basis_count : material.sBases.card = 32 := Axis.source_s_bases_card
theorem s_address_count : material.sAddresses.card = 528 := Axis.source_s_target_address_count

theorem source_J_s_class (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    material.parent.parent.heatTargetJ i j = material.sTargetJ i j := by
  change Laplace.targetHeatJ i j = Axis.targetSHeatJ i j
  exact (Laplace.target_heat_J_exact i j).symm.trans
    (Axis.target_s_heat_J_exact i j hi hj)

structure Closure : Prop where
  parent : Axis.Closure
  genericPair : type_of% Axis.s_pair_shape
  genericHeat : type_of% Axis.s_heat_inner_closed
  genericPrimitive : type_of% Axis.s_primitive_outer
  sourceBases : type_of% Axis.source_s_bases_card
  allSourceQuartets : type_of% Axis.source_s_bases_quartet
  targetAddresses : type_of% Axis.source_s_target_address_count
  targetJ : type_of% Axis.target_s_heat_J_exact
  parentIdentity : type_of% parent_identity
  basisCount : type_of% s_basis_count
  addressCount : type_of% s_address_count
  sourcePotential : type_of% source_J_s_class

theorem sourceGeneratedClosure : Closure :=
  ⟨Axis.sourceGeneratedClosure,Axis.s_pair_shape,Axis.s_heat_inner_closed,
    Axis.s_primitive_outer,Axis.source_s_bases_card,
    Axis.source_s_bases_quartet,Axis.source_s_target_address_count,
    Axis.target_s_heat_J_exact,parent_identity,s_basis_count,
    s_address_count,source_J_s_class⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SFamily
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
