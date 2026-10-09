import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.MixedTarget
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : Moment.Material
  crossQuartet : ℝ
  analyticCrossQuartet : ℝ
  targetJ1414Rest : ℝ

def material : Material where
  parent := Moment.material
  crossQuartet := electronRepulsion 3 2 14 14
  analyticCrossQuartet := Moment.originalP0SCrossQuartet
  targetJ1414Rest := Moment.targetHeatJ1414Rest

theorem parent_identity : material.parent = Moment.material := rfl
theorem cross_quartet_exact :
    material.crossQuartet = material.analyticCrossQuartet :=
  Moment.original_p0_s_cross_quartet

theorem target_J1414_cross_component :
    SourceJoin.material.targetJ 14 14 =
      (SourceJoin.sourceCoefficientAt (196 : Fin 4851) : ℝ) *
        material.analyticCrossQuartet + material.targetJ1414Rest :=
  (Laplace.target_heat_J_exact 14 14).trans
    Moment.target_heat_J1414_mixed_component

structure Closure : Prop where
  parent : Moment.Closure
  mixedSpatial : type_of% Moment.spatial_p0_mixed_factor
  mixedHeat : type_of% Moment.p0_s_heat_inner_closed
  primitive : type_of% Moment.p0_s_primitive_outer
  sourceCensus : type_of% Moment.original_p0_s_cross_census
  sourceQuartet : type_of% Moment.original_p0_s_cross_quartet
  targetComponent : type_of% Moment.target_heat_J1414_mixed_component
  parentIdentity : type_of% parent_identity
  quartet : type_of% cross_quartet_exact
  targetJ : type_of% target_J1414_cross_component

theorem sourceGeneratedClosure : Closure :=
  ⟨Moment.sourceGeneratedClosure,Moment.spatial_p0_mixed_factor,
    Moment.p0_s_heat_inner_closed,Moment.p0_s_primitive_outer,
    Moment.original_p0_s_cross_census,Moment.original_p0_s_cross_quartet,
    Moment.target_heat_J1414_mixed_component,parent_identity,
    cross_quartet_exact,target_J1414_cross_component⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
