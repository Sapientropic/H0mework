import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AtomicIQA.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AnalyticAttraction
open LAlanine40K2025.UnifiedOrbitals
open SourceFiniteData
noncomputable section

structure Material where
  parent : AtomicIQA.Material
  analyticNuclearAO : Basis → Basis → ℝ

def material : Material where
  parent := AtomicIQA.material
  analyticNuclearAO := UnifiedOrbitals.Attraction.sourceNuclearAttractionFinite

theorem parent_same_source : material.parent = AtomicIQA.material := rfl

theorem analytic_nuclear_ao_same_source (i j : Basis) :
    material.analyticNuclearAO i j =
      UnifiedOrbitals.Attraction.sourceNuclearAttractionFinite i j := rfl

theorem original_ao_consumes_analytic (i j : Basis) :
    Nuclear.aoAttraction i j = material.analyticNuclearAO i j :=
  UnifiedOrbitals.Attraction.source_ao_attraction_finite i j

theorem all_zones_consume_analytic :
    (∑ z : Option (Fin 13), ∑ a : Fin 13,
      (Nuclear.Runtime.readMaterial Nuclear.Runtime.afterFirst).zoneAttraction z a) =
      ∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℝ) * material.analyticNuclearAO i j := by
  simpa only [material] using UnifiedOrbitals.Attraction.source_zone_attraction_finite

structure Closure : Prop where
  parent : AtomicIQA.Closure
  parentIdentity : type_of% parent_same_source
  analyticIdentity : type_of% analytic_nuclear_ao_same_source
  primitiveIntegral : type_of% UnifiedOrbitals.Attraction.primitive_attraction_closed
  aoIntegral : type_of% UnifiedOrbitals.Attraction.ao_attraction_finite
  sourceAO : type_of% original_ao_consumes_analytic
  allZones : type_of% all_zones_consume_analytic

theorem sourceGeneratedClosure : Closure :=
  ⟨AtomicIQA.sourceGeneratedClosure,parent_same_source,
    analytic_nuclear_ao_same_source,
    UnifiedOrbitals.Attraction.primitive_attraction_closed,
    UnifiedOrbitals.Attraction.ao_attraction_finite,
    original_ao_consumes_analytic,all_zones_consume_analytic⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AnalyticAttraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
