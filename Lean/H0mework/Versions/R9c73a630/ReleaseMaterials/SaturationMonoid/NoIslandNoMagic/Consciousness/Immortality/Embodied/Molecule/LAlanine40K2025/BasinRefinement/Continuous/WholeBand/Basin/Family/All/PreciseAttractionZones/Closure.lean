import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.PreciseTarget

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionZones
open LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
open scoped BigOperators
noncomputable section

structure Material where
  parent : PreciseAttractionComplete.Material
  zoneAttraction : Option (Fin 13) → Fin 13 → ℝ
  nuclearAttraction : Fin 13 → ℝ

def material : Material where
  parent := PreciseAttractionComplete.material
  zoneAttraction := Nuclear.PreciseTarget.zoneAttraction
  nuclearAttraction := Nuclear.PreciseTarget.nuclearAttraction

theorem parent_same_source : material.parent = PreciseAttractionComplete.material := rfl
theorem zones_same_source (z : Option (Fin 13)) (a : Fin 13) :
    material.zoneAttraction z a = Nuclear.PreciseTarget.zoneAttraction z a := rfl
theorem nuclei_same_source (a : Fin 13) :
    material.nuclearAttraction a = Nuclear.PreciseTarget.nuclearAttraction a := rfl

theorem zone_total_actual :
    (∑ z : Option (Fin 13), ∑ a : Fin 13, material.zoneAttraction z a) =
      material.parent.actualWeighted :=
  Nuclear.PreciseTarget.zone_total_same_actual

theorem zone_total_independent :
    |(∑ z : Option (Fin 13), ∑ a : Fin 13, material.zoneAttraction z a) -
      material.parent.independentWeighted| ≤ (1/10^9 : ℝ) := by
  rw [zone_total_actual]
  exact UnifiedOrbitals.Attraction.Precise.complete_attraction_within_independent

theorem zone_coordinate_residual :
    Holds UnifiedOrbitals.Attraction.Precise.totalCoordinateResidualInterval
      ((∑ z : Option (Fin 13), ∑ a : Fin 13, material.zoneAttraction z a) -
        (∑ z : Option (Fin 13), ∑ a : Fin 13, Nuclear.zoneAttraction z a)) :=
  Nuclear.PreciseTarget.precise_zone_residual_contains

structure Closure : Prop where
  parent : PreciseAttractionComplete.Closure
  parentIdentity : type_of% parent_same_source
  zoneIdentity : type_of% zones_same_source
  nucleusIdentity : type_of% nuclei_same_source
  exactTotal : type_of% zone_total_actual
  independentTotal : type_of% zone_total_independent
  coordinateResidual : type_of% zone_coordinate_residual
  targetCentre : type_of% Nuclear.PreciseTarget.centre_same_target

theorem sourceGeneratedClosure : Closure :=
  ⟨PreciseAttractionComplete.sourceGeneratedClosure,parent_same_source,
    zones_same_source,nuclei_same_source,zone_total_actual,zone_total_independent,
    zone_coordinate_residual,Nuclear.PreciseTarget.centre_same_target⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionZones
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
