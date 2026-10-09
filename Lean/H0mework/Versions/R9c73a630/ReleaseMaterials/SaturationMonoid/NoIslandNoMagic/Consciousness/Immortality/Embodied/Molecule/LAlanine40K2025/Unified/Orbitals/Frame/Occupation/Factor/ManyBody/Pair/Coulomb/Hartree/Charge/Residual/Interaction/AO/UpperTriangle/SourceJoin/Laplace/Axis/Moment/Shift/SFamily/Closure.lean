import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily.Census
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.Closure

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement.SourceFiniteData
noncomputable section

structure Material where
  parent : Shift.Material
  sBases : Finset Basis
  sourceAddresses : Finset (Fin 4851)
  analyticQuartet : Basis → Basis → Basis → Basis → ℝ
  combinedTargetJ : Basis → Basis → ℝ

def material : Material where
  parent := Shift.material
  sBases := Axis.sourceSBases
  sourceAddresses := sourceSAddresses
  analyticQuartet := sourceSRightQuartet
  combinedTargetJ := targetSHeatJ

theorem parent_identity : material.parent = Shift.material := rfl
theorem s_basis_count : material.sBases.card = 32 := Axis.source_s_bases_card
theorem source_address_count : material.sourceAddresses.card = 2640 := source_s_address_count

theorem quartet_exact (basis sBasis i j : Basis)
    (hs : sBasis ∈ material.sBases)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    electronRepulsion basis sBasis i j =
      material.analyticQuartet basis sBasis i j :=
  source_s_right_bases_quartet basis sBasis i j hs hi hj

theorem target_J_s_class (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    SourceJoin.material.targetJ i j = material.combinedTargetJ i j := by
  simpa only [material] using target_s_source_J i j hi hj

theorem parent_shift_same_source (i j : Basis)
    (hi : i ∈ material.sBases) (hj : j ∈ material.sBases) :
    material.parent.combinedTargetJ i j = material.combinedTargetJ i j := by
  simpa only [material, Shift.material] using
    (Shift.target_J_shift_class i j hi hj).symm.trans
      (target_s_source_J i j hi hj)

structure Closure : Prop where
  parent : Shift.Closure
  pairShape : type_of% s_right_pair_shape
  heatInner : type_of% s_right_heat_inner_closed
  sourceQuartet : type_of% source_s_right_bases_quartet
  sourceClassification : type_of% source_s_addresses_exact
  addressCount : type_of% source_s_address_count
  targetAll : type_of% target_s_source_J
  parentIdentity : type_of% parent_identity
  basisCount : type_of% s_basis_count
  installedCount : type_of% source_address_count
  quartet : type_of% quartet_exact
  targetJ : type_of% target_J_s_class
  sameSource : type_of% parent_shift_same_source

theorem sourceGeneratedClosure : Closure :=
  ⟨Shift.sourceGeneratedClosure,s_right_pair_shape,
    s_right_heat_inner_closed,source_s_right_bases_quartet,
    source_s_addresses_exact,source_s_address_count,target_s_source_J,
    parent_identity,s_basis_count,source_address_count,
    quartet_exact,target_J_s_class,parent_shift_same_source⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Axis.Moment.Shift.SFamily
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
