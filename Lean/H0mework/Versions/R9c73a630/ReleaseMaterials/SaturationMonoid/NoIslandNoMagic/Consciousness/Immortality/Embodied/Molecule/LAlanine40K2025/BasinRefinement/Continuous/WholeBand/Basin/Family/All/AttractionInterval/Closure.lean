import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.Total

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AttractionInterval
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
noncomputable section

structure Material where
  parent : AnalyticAttraction.Material
  aoInterval : Basis → Basis → Pair
  totalInterval : Pair

def material : Material where
  parent := AnalyticAttraction.material
  aoInterval := UnifiedOrbitals.Attraction.aoAttractionInterval
  totalInterval := UnifiedOrbitals.Attraction.totalAttractionInterval

theorem parent_same_source : material.parent = AnalyticAttraction.material := rfl

theorem ao_interval_same_source (i j : Basis) :
    material.aoInterval i j = UnifiedOrbitals.Attraction.aoAttractionInterval i j := rfl

theorem total_interval_same_source :
    material.totalInterval = UnifiedOrbitals.Attraction.totalAttractionInterval := rfl

theorem original_ao_enclosed (i j : Basis) :
    Holds (material.aoInterval i j) (Nuclear.aoAttraction i j) :=
  UnifiedOrbitals.Attraction.ao_attraction_interval_contains i j

theorem original_zone_total_enclosed :
    Holds material.totalInterval
      (∑ z : Option (Fin 13), ∑ a : Fin 13,
        (AnalyticAttraction.Runtime.readMaterial
          AnalyticAttraction.Runtime.afterFirst).parent.parent.parent.zoneAttraction z a) :=
  UnifiedOrbitals.Attraction.actual_zone_total_interval_contains
    AnalyticAttraction.Runtime.afterFirst

structure Closure : Prop where
  parent : AnalyticAttraction.Closure
  parentIdentity : type_of% parent_same_source
  aoIdentity : type_of% ao_interval_same_source
  totalIdentity : type_of% total_interval_same_source
  boysLow : type_of% UnifiedOrbitals.Attraction.boys_low_interval_contains
  boysHigh : type_of% UnifiedOrbitals.Attraction.boys_high_interval_contains
  sourceBoys : type_of% UnifiedOrbitals.Attraction.source_boys_interval_contains
  sourceReuse : type_of% UnifiedOrbitals.Attraction.source_boys_interval_reuses_geometry
  primitive : type_of% UnifiedOrbitals.Attraction.primitive_attraction_interval_contains
  ao : type_of% original_ao_enclosed
  total : type_of% original_zone_total_enclosed

theorem sourceGeneratedClosure : Closure :=
  ⟨AnalyticAttraction.sourceGeneratedClosure,
    parent_same_source,ao_interval_same_source,total_interval_same_source,
    UnifiedOrbitals.Attraction.boys_low_interval_contains,
    UnifiedOrbitals.Attraction.boys_high_interval_contains,
    UnifiedOrbitals.Attraction.source_boys_interval_contains,
    UnifiedOrbitals.Attraction.source_boys_interval_reuses_geometry,
    UnifiedOrbitals.Attraction.primitive_attraction_interval_contains,
    original_ao_enclosed,original_zone_total_enclosed⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AttractionInterval
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
