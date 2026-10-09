import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Target
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Low.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

theorem prior_low_same_source (i j : Basis)
    (hi : i ∈ Axis.sourceSBases) (hj : j ∈ Axis.sourceSBases) :
    Low.targetLowHeatJ i j = targetShiftHeatJ i j := by
  rw [← Low.target_low_J i j hi hj, target_shift_J i j hi hj]

structure Material where
  parent : Low.Material
  sBases : Finset Basis
  shiftAddresses : Finset (Fin 4851)
  analyticQuartet : Basis → Basis → Basis → ℝ
  combinedTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := Low.material
  sBases := Axis.sourceSBases
  shiftAddresses := shiftAddresses
  analyticQuartet := sourceShiftQuartet
  combinedTargetJ := targetShiftHeatJ

theorem parent_identity : material.parent = Low.material := rfl
theorem s_basis_count : material.sBases.card = 32 := Axis.source_s_bases_card
theorem shift_address_count : material.shiftAddresses.card = 96 := shift_addresses_card

theorem quartet_exact (basis i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    electronRepulsion basis 2 i j = material.analyticQuartet basis i j :=
  source_shift_s_bases_quartet basis i j hi hj

theorem target_J_shift_class (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    SourceJoin.material.targetJ i j = material.combinedTargetJ i j := by
  simpa only [material] using target_shift_J i j hi hj

theorem parent_low_same_source (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    material.parent.combinedTargetJ i j = material.combinedTargetJ i j := by
  simpa only [material, Low.material] using prior_low_same_source i j hi hj

structure Closure : Prop where
  parent : Low.Closure
  axisMoment : type_of% axis_shift_integral
  spatialMoment : type_of% spatial_shift_factor
  originalSource : type_of% all_original_low_degree_raw
  sourceQuartet : type_of% source_shift_s_bases_quartet
  originalAddresses : type_of% shift_target_address
  addressCard : type_of% shift_addresses_card
  addressComplete : type_of% shift_at_address_complete
  addressSound : type_of% shift_at_address_sound
  targetAll : type_of% target_shift_J
  parentIdentity : type_of% parent_identity
  basisCount : type_of% s_basis_count
  shiftCount : type_of% shift_address_count
  quartet : type_of% quartet_exact
  targetJ : type_of% target_J_shift_class
  sameSource : type_of% parent_low_same_source

theorem sourceGeneratedClosure : Closure :=
  ⟨Low.sourceGeneratedClosure,axis_shift_integral,spatial_shift_factor,
    all_original_low_degree_raw,source_shift_s_bases_quartet,
    shift_target_address,shift_addresses_card,
    shift_at_address_complete,shift_at_address_sound,target_shift_J,
    parent_identity,s_basis_count,shift_address_count,
    quartet_exact,target_J_shift_class,parent_low_same_source⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
