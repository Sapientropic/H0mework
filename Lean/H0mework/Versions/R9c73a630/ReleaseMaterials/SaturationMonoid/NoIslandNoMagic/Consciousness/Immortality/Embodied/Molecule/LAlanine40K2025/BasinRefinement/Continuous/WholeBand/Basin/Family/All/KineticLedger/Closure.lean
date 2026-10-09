import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Ledger

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.KineticLedger
open LAlanine40K2025.UnifiedOrbitals
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory
open scoped BigOperators
noncomputable section

structure Material where
  parent : Nuclear.Material
  zoneKinetic : Option (Fin 13) → ℝ
  kineticIntegralNano : ℤ

def material : Material where
  parent := Nuclear.material
  zoneKinetic := OneBody.zoneKinetic
  kineticIntegralNano :=
    (Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral

theorem parent_same_source : material.parent=Nuclear.material := rfl
theorem zoneKinetic_same_source (z : Option (Fin 13)) :
    material.zoneKinetic z=OneBody.zoneKinetic z := rfl
theorem kineticIntegral_same_source :
    material.kineticIntegralNano=
      (Reentry.Source.stepReadout.nuclear.targetLedger.integral .kinetic).independentIntegral := rfl

structure Closure : Prop where
  parent : Nuclear.Closure
  parentIdentity : type_of% parent_same_source
  zoneKineticIdentity : type_of% zoneKinetic_same_source
  kineticIntegralIdentity : type_of% kineticIntegral_same_source
  kineticRowsWithin : type_of% UnifiedOrbitals.Kinetic.kinetic_error
  kineticPairExpansion : type_of% UnifiedOrbitals.Kinetic.kinetic_pair_expansion
  kineticTargetRowSum : type_of% UnifiedOrbitals.Kinetic.kinetic_target_row_sum
  recordedCell : type_of% UnifiedOrbitals.Kinetic.recorded_kinetic_at_target
  rowWeightBound : type_of% UnifiedOrbitals.Kinetic.kinetic_row_weight_bound
  recordedSumWithin : type_of% UnifiedOrbitals.Kinetic.recorded_kinetic_sum_within
  contractWithinRecorded : type_of% UnifiedOrbitals.Kinetic.kinetic_contract_within_recorded
  zoneKineticLedger : type_of% UnifiedOrbitals.Kinetic.zone_kinetic_ledger
  counterfactualRow : type_of% UnifiedOrbitals.Kinetic.kinetic_counterfactual_row

theorem sourceGeneratedClosure : Closure :=
  ⟨Nuclear.sourceGeneratedClosure,
    parent_same_source,zoneKinetic_same_source,kineticIntegral_same_source,
    UnifiedOrbitals.Kinetic.kinetic_error,
    UnifiedOrbitals.Kinetic.kinetic_pair_expansion,
    UnifiedOrbitals.Kinetic.kinetic_target_row_sum,
    UnifiedOrbitals.Kinetic.recorded_kinetic_at_target,
    UnifiedOrbitals.Kinetic.kinetic_row_weight_bound,
    UnifiedOrbitals.Kinetic.recorded_kinetic_sum_within,
    UnifiedOrbitals.Kinetic.kinetic_contract_within_recorded,
    UnifiedOrbitals.Kinetic.zone_kinetic_ledger,
    UnifiedOrbitals.Kinetic.kinetic_counterfactual_row⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.KineticLedger
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
