import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High.Target
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : SFamily.Material
  sBases : Finset Basis
  sourceAddresses : Finset (Fin 4851)
  analyticQuartet : Basis → Basis → Basis → Basis → ℝ
  combinedTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := SFamily.material
  sBases := Axis.sourceSBases
  sourceAddresses := allSourceAddresses
  analyticQuartet := sourceHighQuartet
  combinedTargetJ := targetHighJ

theorem parent_identity : material.parent = SFamily.material := rfl
theorem s_basis_count : material.sBases.card = 32 := Axis.source_s_bases_card
theorem source_address_count : material.sourceAddresses.card = 4851 :=
  all_source_addresses_card

theorem quartet_exact (sourceLeft sourceRight i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    electronRepulsion sourceLeft sourceRight i j =
      material.analyticQuartet sourceLeft sourceRight i j :=
  source_high_s_targets_quartet sourceLeft sourceRight i j hi hj

theorem target_J_all_source (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    SourceJoin.material.targetJ i j = material.combinedTargetJ i j := by
  simpa only [material] using target_high_J i j hi hj

theorem parent_same_source (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    material.parent.combinedTargetJ i j = material.combinedTargetJ i j := by
  simpa only [material, SFamily.material] using
    prior_s_family_same_source i j hi hj

structure Closure : Prop where
  parent : SFamily.Closure
  gaussianFourth : type_of% gauss_fourth
  rawMoment : type_of% raw_moment_integral
  polynomial : type_of% shifted_pair_gaussian_integral
  coupledAxis : type_of% axis_pair_integral
  spatial : type_of% spatial_pair_factor
  sourceQuartet : type_of% source_high_s_targets_quartet
  addressCount : type_of% all_source_addresses_card
  targetAll : type_of% target_high_J
  parentIdentity : type_of% parent_identity
  basisCount : type_of% s_basis_count
  installedCount : type_of% source_address_count
  quartet : type_of% quartet_exact
  targetJ : type_of% target_J_all_source
  sameSource : type_of% parent_same_source

theorem sourceGeneratedClosure : Closure :=
  ⟨SFamily.sourceGeneratedClosure,gauss_fourth,raw_moment_integral,
    shifted_pair_gaussian_integral,axis_pair_integral,spatial_pair_factor,
    source_high_s_targets_quartet,all_source_addresses_card,target_high_J,
    parent_identity,s_basis_count,source_address_count,
    quartet_exact,target_J_all_source,parent_same_source⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.High
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
