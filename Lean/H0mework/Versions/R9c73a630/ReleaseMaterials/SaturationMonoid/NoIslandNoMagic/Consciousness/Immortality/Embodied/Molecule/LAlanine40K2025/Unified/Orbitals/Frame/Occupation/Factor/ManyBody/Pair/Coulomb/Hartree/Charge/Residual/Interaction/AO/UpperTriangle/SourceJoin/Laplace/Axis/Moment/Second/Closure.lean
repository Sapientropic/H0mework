import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second.Target
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : AnyAxis.Material
  sBases : Finset Basis
  dAddress : Fin 4851
  analyticQuartet : Basis → Basis → ℝ
  combinedTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := AnyAxis.material
  sBases := Axis.sourceSBases
  dAddress := dAddress
  analyticQuartet := sourceDSQuartet
  combinedTargetJ := targetP3DHeatJ

theorem parent_identity : material.parent = AnyAxis.material := rfl
theorem s_basis_count : material.sBases.card = 32 := Axis.source_s_bases_card
theorem original_d_address_identity : material.dAddress = (204 : Fin 4851) := rfl

theorem quartet_exact (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    electronRepulsion 11 2 i j = material.analyticQuartet i j :=
  source_d_s_bases_quartet i j hi hj

theorem target_J_p3d (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    SourceJoin.material.targetJ i j = material.combinedTargetJ i j :=
  target_p3d_J i j hi hj

structure Closure : Prop where
  parent : AnyAxis.Closure
  gaussianSecond : type_of% gaussian_second_simple
  shiftedSecond : type_of% shifted_gaussian_second
  coupledSecond : type_of% coupled_axis_second_pair
  spatialSecond : type_of% spatial_d2_mixed_factor
  sourceD : type_of% original_d11_raw
  sourceCensus : type_of% original_d11_census
  sourceQuartet : type_of% source_d_s_bases_quartet
  targetAddress : type_of% original_d_address
  noPOverlap : type_of% d_address_not_p
  targetCombined : type_of% target_p3d_J
  parentIdentity : type_of% parent_identity
  basisCount : type_of% s_basis_count
  addressIdentity : type_of% original_d_address_identity
  quartet : type_of% quartet_exact
  targetJ : type_of% target_J_p3d

theorem sourceGeneratedClosure : Closure :=
  ⟨AnyAxis.sourceGeneratedClosure,gaussian_second_simple,
    shifted_gaussian_second,coupled_axis_second_pair,
    spatial_d2_mixed_factor,original_d11_raw,
    original_d11_census,source_d_s_bases_quartet,
    original_d_address,d_address_not_p,target_p3d_J,
    parent_identity,s_basis_count,original_d_address_identity,
    quartet_exact,target_J_p3d⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
