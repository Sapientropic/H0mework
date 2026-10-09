import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis.TargetAll
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Mixed.Family.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : Mixed.Family.Material
  sBases : Finset Basis
  pAddresses : Finset (Fin 4851)
  analyticQuartet : Fin 3 → Basis → Basis → ℝ
  tripleTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := Mixed.Family.material
  sBases := Axis.sourceSBases
  pAddresses := pAddresses
  analyticQuartet := sourcePAxisSQuartet
  tripleTargetJ := targetThreePHeatJ

theorem parent_identity : material.parent = Mixed.Family.material := rfl
theorem s_basis_count : material.sBases.card = 32 := Axis.source_s_bases_card
theorem p_address_count : material.pAddresses.card = 3 := p_addresses_card

theorem quartet_exact (axis : Fin 3) (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    electronRepulsion (pBasis axis) 2 i j = material.analyticQuartet axis i j :=
  source_p_axis_s_bases_quartet axis i j hi hj

theorem target_J_three_p (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    SourceJoin.material.targetJ i j = material.tripleTargetJ i j :=
  target_three_p_J i j hi hj

structure Closure : Prop where
  parent : Mixed.Family.Closure
  sourceAxes : type_of% original_p_axes_raw
  sourceCensus : type_of% original_p_axes_census
  spatialMoment : type_of% spatial_p_mixed_factor
  sourceQuartet : type_of% source_p_axis_s_bases_quartet
  originalAddresses : type_of% p_axis_target_address
  addressCard : type_of% p_addresses_card
  addressComplete : type_of% p_axis_at_address_complete
  addressSound : type_of% p_axis_at_address_sound
  targetAll : type_of% target_three_p_J
  parentIdentity : type_of% parent_identity
  basisCount : type_of% s_basis_count
  pCount : type_of% p_address_count
  quartet : type_of% quartet_exact
  targetJ : type_of% target_J_three_p

theorem sourceGeneratedClosure : Closure :=
  ⟨Mixed.Family.sourceGeneratedClosure,
    original_p_axes_raw,original_p_axes_census,
    spatial_p_mixed_factor,source_p_axis_s_bases_quartet,
    p_axis_target_address,p_addresses_card,
    p_axis_at_address_complete,p_axis_at_address_sound,
    target_three_p_J,parent_identity,s_basis_count,
    p_address_count,quartet_exact,target_J_three_p⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.AnyAxis
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
