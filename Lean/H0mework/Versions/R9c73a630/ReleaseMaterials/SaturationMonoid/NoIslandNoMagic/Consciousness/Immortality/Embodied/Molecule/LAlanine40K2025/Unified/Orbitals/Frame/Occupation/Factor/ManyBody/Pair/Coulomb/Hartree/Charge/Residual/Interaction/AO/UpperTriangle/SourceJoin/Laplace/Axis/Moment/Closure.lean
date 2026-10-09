import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.TargetP0
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.SFamily.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : Axis.SFamily.Material
  p0Quartet : ℝ
  reducedTargetJ22 : ℝ

def material : Material where
  parent := Axis.SFamily.material
  p0Quartet := electronRepulsion 3 2 2 2
  reducedTargetJ22 := targetHeatJ22WithoutP0

theorem parent_identity : material.parent = Axis.SFamily.material := rfl
theorem actual_p0_quartet_zero : material.p0Quartet = 0 := original_p0_ERI_zero

theorem target_J22_reduced :
    material.parent.parent.parent.heatTargetJ 2 2 =
      material.reducedTargetJ22 := by
  change Laplace.targetHeatJ 2 2 = targetHeatJ22WithoutP0
  exact target_heat_J22_p0_erase

structure Closure : Prop where
  parent : Axis.SFamily.Closure
  gaussianFirst : type_of% shifted_gaussian_first
  coupledFirst : type_of% coupled_axis_first_pair
  spatialOdd : type_of% spatial_p0_same_centre_zero
  sourceP0 : type_of% original_p0_source
  sourceQuartet : type_of% original_p0_ERI_zero
  targetAddress : type_of% original_p0_target_address
  targetZero : type_of% original_p0_target_term_zero
  targetErase : type_of% target_heat_J22_p0_erase
  parentIdentity : type_of% parent_identity
  quartet : type_of% actual_p0_quartet_zero
  targetJ : type_of% target_J22_reduced

theorem sourceGeneratedClosure : Closure :=
  ⟨Axis.SFamily.sourceGeneratedClosure,shifted_gaussian_first,
    coupled_axis_first_pair,spatial_p0_same_centre_zero,
    original_p0_source,original_p0_ERI_zero,
    original_p0_target_address,original_p0_target_term_zero,
    target_heat_J22_p0_erase,parent_identity,
    actual_p0_quartet_zero,target_J22_reduced⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
