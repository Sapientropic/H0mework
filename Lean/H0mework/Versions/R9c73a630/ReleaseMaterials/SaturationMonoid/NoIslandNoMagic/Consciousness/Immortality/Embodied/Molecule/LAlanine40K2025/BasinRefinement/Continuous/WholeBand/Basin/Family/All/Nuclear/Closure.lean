import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.FullU

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
open LAlanine40K2025.UnifiedOrbitals LAlanine40K2025.UnifiedAction
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory
open scoped BigOperators
noncomputable section

structure Material where
  parent : OneBody.Material
  nuclearCharge : Fin 13 → ℝ
  nuclearPosition : Fin 13 → Point
  zoneAttraction : Option (Fin 13) → Fin 13 → ℝ
  zoneOneBody : Option (Fin 13) → ℝ
  repulsion : ℝ

def material : Material where
  parent := OneBody.material
  nuclearCharge := nuclearCharge
  nuclearPosition := nuclearPosition
  zoneAttraction := zoneAttraction
  zoneOneBody := zoneOneBody
  repulsion := totalRepulsion

theorem parent_same_source : material.parent=OneBody.material := rfl
theorem nuclearCharge_same_source (a : Fin 13) :
    material.nuclearCharge a=nuclearCharge a := rfl
theorem nuclearPosition_same_source (a : Fin 13) :
    material.nuclearPosition a=nuclearPosition a := rfl
theorem zoneAttraction_same_source (z : Option (Fin 13)) (a : Fin 13) :
    material.zoneAttraction z a=zoneAttraction z a := rfl
theorem zoneOneBody_same_source (z : Option (Fin 13)) :
    material.zoneOneBody z=zoneOneBody z := rfl
theorem repulsion_same_source : material.repulsion=totalRepulsion := rfl

structure Closure : Prop where
  parent : OneBody.Closure
  parentIdentity : type_of% parent_same_source
  chargeIdentity : type_of% nuclearCharge_same_source
  positionIdentity : type_of% nuclearPosition_same_source
  zoneAttractionIdentity : type_of% zoneAttraction_same_source
  zoneOneBodyIdentity : type_of% zoneOneBody_same_source
  repulsionIdentity : type_of% repulsion_same_source
  positionTableSource : type_of% position_table_same_source
  nuclearFrameReadout : type_of% nuclear_same_frame_readout
  chargeCensus : type_of% charge_census
  totalNuclearCharge : type_of% total_nuclear_charge
  positionsDistinct : type_of% nuclear_positions_distinct
  basisOnNuclei : type_of% basis_centres_on_nuclei
  shiftedOffNuclei : type_of% shifted_centres_off_nuclei
  zoneAttractionSum : type_of% zone_attraction_sum
  attractionOriginalAO : type_of% total_attraction_original_ao
  nuclearPairsAccount : type_of% nuclearPairs_same_account
  oneBodyNuclearTotal : type_of% one_body_nuclear_total
  partitionNeutral : type_of% partition_charge_neutral
  fullUKineticJoin : type_of% full_U_kinetic_zone_join

theorem sourceGeneratedClosure : Closure :=
  ⟨OneBody.sourceGeneratedClosure,
    parent_same_source,nuclearCharge_same_source,nuclearPosition_same_source,
    zoneAttraction_same_source,zoneOneBody_same_source,repulsion_same_source,
    position_table_same_source,nuclear_same_frame_readout,charge_census,
    total_nuclear_charge,nuclear_positions_distinct,basis_centres_on_nuclei,
    shifted_centres_off_nuclei,zone_attraction_sum,total_attraction_original_ao,
    nuclearPairs_same_account,one_body_nuclear_total,partition_charge_neutral,
    full_U_kinetic_zone_join⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
