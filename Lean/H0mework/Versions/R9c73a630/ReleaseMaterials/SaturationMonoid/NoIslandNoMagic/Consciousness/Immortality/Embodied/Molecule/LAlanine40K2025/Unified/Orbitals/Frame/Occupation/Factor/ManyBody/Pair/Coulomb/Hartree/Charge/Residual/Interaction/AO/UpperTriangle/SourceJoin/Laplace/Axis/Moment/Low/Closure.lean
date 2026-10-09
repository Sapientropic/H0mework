import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Target
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Second.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : Second.Material
  sBases : Finset Basis
  lowAddresses : Finset (Fin 4851)
  analyticQuartet : Fin 11 → Basis → Basis → ℝ
  combinedTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := Second.material
  sBases := Axis.sourceSBases
  lowAddresses := lowAddresses
  analyticQuartet := sourceLowQuartet
  combinedTargetJ := targetLowHeatJ

theorem parent_identity : material.parent = Second.material := rfl
theorem s_basis_count : material.sBases.card = 32 := Axis.source_s_bases_card
theorem low_address_count : material.lowAddresses.card = 11 := low_addresses_card

theorem quartet_exact (slot : Fin 11) (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    electronRepulsion (lowBasis slot) 2 i j = material.analyticQuartet slot i j :=
  source_low_s_bases_quartet slot i j hi hj

theorem target_J_low_class (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    SourceJoin.material.targetJ i j = material.combinedTargetJ i j :=
  target_low_J i j hi hj

theorem prior_p3d_same_source (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    material.parent.combinedTargetJ i j = material.combinedTargetJ i j :=
  (Second.target_p3d_J i j hi hj).symm.trans (target_low_J i j hi hj)

structure Closure : Prop where
  parent : Second.Closure
  axisMoment : type_of% axis_low_integral
  spatialMoment : type_of% spatial_low_factor
  originalSource : type_of% original_low_raw
  sourceQuartet : type_of% source_low_s_bases_quartet
  originalAddresses : type_of% low_target_address
  addressCard : type_of% low_addresses_card
  addressComplete : type_of% low_at_address_complete
  addressSound : type_of% low_at_address_sound
  targetAll : type_of% target_low_J
  parentIdentity : type_of% parent_identity
  basisCount : type_of% s_basis_count
  lowCount : type_of% low_address_count
  quartet : type_of% quartet_exact
  targetJ : type_of% target_J_low_class
  sameSource : type_of% prior_p3d_same_source

theorem sourceGeneratedClosure : Closure :=
  ⟨Second.sourceGeneratedClosure,axis_low_integral,spatial_low_factor,
    original_low_raw,source_low_s_bases_quartet,
    low_target_address,low_addresses_card,
    low_at_address_complete,low_at_address_sound,target_low_J,
    parent_identity,s_basis_count,low_address_count,
    quartet_exact,target_J_low_class,prior_p3d_same_source⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
