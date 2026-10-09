import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AttractionInterval.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Regression

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttraction
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
noncomputable section

structure Material where
  parent : AttractionInterval.Material
  preciseNucleus : Fin 13 → Fin 3 → ℚ
  preciseAO : Basis → Basis → Pair
  preciseTotal : Pair
  aoCoordinateResidual : Basis → Basis → Pair
  totalCoordinateResidual : Pair

def material : Material where
  parent := AttractionInterval.material
  preciseNucleus := UnifiedOrbitals.Attraction.Precise.nucleus
  preciseAO := UnifiedOrbitals.Attraction.Precise.aoInterval
  preciseTotal := UnifiedOrbitals.Attraction.Precise.totalInterval
  aoCoordinateResidual := UnifiedOrbitals.Attraction.Precise.aoCoordinateResidualInterval
  totalCoordinateResidual := UnifiedOrbitals.Attraction.Precise.totalCoordinateResidualInterval

theorem parent_same_source : material.parent = AttractionInterval.material := rfl

theorem position_same_source (a : Fin 13) (k : Fin 3) :
    material.preciseNucleus a k = UnifiedOrbitals.Attraction.Precise.nucleus a k := rfl

theorem ao_same_source (i j : Basis) :
    material.preciseAO i j = UnifiedOrbitals.Attraction.Precise.aoInterval i j := rfl

theorem total_same_source :
    material.preciseTotal = UnifiedOrbitals.Attraction.Precise.totalInterval := rfl

theorem residual_same_source (i j : Basis) :
    material.aoCoordinateResidual i j =
      UnifiedOrbitals.Attraction.Precise.aoCoordinateResidualInterval i j := rfl

theorem total_residual_same_source :
    material.totalCoordinateResidual =
      UnifiedOrbitals.Attraction.Precise.totalCoordinateResidualInterval := rfl

structure Closure : Prop where
  parent : AttractionInterval.Closure
  parentIdentity : type_of% parent_same_source
  positionIdentity : type_of% position_same_source
  aoIdentity : type_of% ao_same_source
  totalIdentity : type_of% total_same_source
  residualIdentity : type_of% residual_same_source
  totalResidualIdentity : type_of% total_residual_same_source
  reentryPosition : type_of% UnifiedOrbitals.Attraction.Precise.same_reentry_target
  positionResolution : type_of% UnifiedOrbitals.Attraction.Precise.ledger_rounding_residual
  gaussianCentres : type_of% UnifiedOrbitals.Attraction.Precise.all_term_centres_precise
  preciseAOIntegral : type_of% UnifiedOrbitals.Attraction.Precise.ao_interval_contains
  preciseTotalIntegral : type_of% UnifiedOrbitals.Attraction.Precise.total_interval_contains
  aoTransport : type_of% UnifiedOrbitals.Attraction.Precise.ao_coordinate_residual_contains
  totalTransport : type_of% UnifiedOrbitals.Attraction.Precise.total_coordinate_residual_contains
  roundedDisjoint : type_of% UnifiedOrbitals.Attraction.Precise.rounded_row03_separated
  preciseRecorded : type_of% UnifiedOrbitals.Attraction.Precise.precise_row03_recorded
  nonzeroCoordinateEffect : type_of% UnifiedOrbitals.Attraction.Precise.actual_coordinate_effect_nonzero

theorem sourceGeneratedClosure : Closure :=
  ⟨AttractionInterval.sourceGeneratedClosure,
    parent_same_source,position_same_source,ao_same_source,total_same_source,
    residual_same_source,total_residual_same_source,
    UnifiedOrbitals.Attraction.Precise.same_reentry_target,
    UnifiedOrbitals.Attraction.Precise.ledger_rounding_residual,
    UnifiedOrbitals.Attraction.Precise.all_term_centres_precise,
    UnifiedOrbitals.Attraction.Precise.ao_interval_contains,
    UnifiedOrbitals.Attraction.Precise.total_interval_contains,
    UnifiedOrbitals.Attraction.Precise.ao_coordinate_residual_contains,
    UnifiedOrbitals.Attraction.Precise.total_coordinate_residual_contains,
    UnifiedOrbitals.Attraction.Precise.rounded_row03_separated,
    UnifiedOrbitals.Attraction.Precise.precise_row03_recorded,
    UnifiedOrbitals.Attraction.Precise.actual_coordinate_effect_nonzero⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
