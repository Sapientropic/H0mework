import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.PreciseWholeSpace
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAttractionComplete.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Attraction

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear.PreciseTarget
open LAlanine40K2025.UnifiedOrbitals
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory SourceCoulomb
open scoped BigOperators
noncomputable section

def zoneAttraction (z : Option (Fin 13)) (a : Fin 13) : ℝ :=
  ∫ x in region z, -nuclearCharge a *
    (sourceDensity x * kernel (x - centre a))

theorem zone_attraction_sum (a : Fin 13) :
    ∑ z : Option (Fin 13), zoneAttraction z a = nuclearAttraction a := by
  have h := integral_iUnion_fintype (s := region) all_regions_measurable
    OneBody.regions_disjoint
    (fun _ => (zone_attraction_integrable a).integrableOn)
  rw [OneBody.regions_cover] at h
  simpa only [setIntegral_univ,zoneAttraction,nuclearAttraction] using h.symm

theorem zone_total_same_actual :
    (∑ z : Option (Fin 13), ∑ a : Fin 13, zoneAttraction z a) =
      UnifiedOrbitals.Attraction.Precise.totalIntegral := by
  calc
    _ = ∑ a : Fin 13, ∑ z : Option (Fin 13), zoneAttraction z a := Finset.sum_comm
    _ = ∑ a : Fin 13, nuclearAttraction a := by
      apply Finset.sum_congr rfl
      intro a _
      exact zone_attraction_sum a
    _ = _ := nuclear_total_original_ao

theorem precise_minus_rounded_zones :
    (∑ z : Option (Fin 13), ∑ a : Fin 13, zoneAttraction z a) -
      (∑ z : Option (Fin 13), ∑ a : Fin 13, Nuclear.zoneAttraction z a) =
        UnifiedOrbitals.Attraction.Precise.totalIntegral -
          UnifiedOrbitals.Attraction.Precise.roundedTotalIntegral := by
  rw [zone_total_same_actual,UnifiedOrbitals.Attraction.Precise.rounded_total_same_zones]

theorem precise_zone_residual_contains :
    Holds UnifiedOrbitals.Attraction.Precise.totalCoordinateResidualInterval
      ((∑ z : Option (Fin 13), ∑ a : Fin 13, zoneAttraction z a) -
        (∑ z : Option (Fin 13), ∑ a : Fin 13, Nuclear.zoneAttraction z a)) := by
  rw [precise_minus_rounded_zones]
  exact UnifiedOrbitals.Attraction.Precise.total_coordinate_residual_contains

theorem runtime_zone_total_same_actual
    (runtime : LivingRuntimeState PreciseAttractionComplete.Runtime.process) :
    (∑ z : Option (Fin 13), ∑ a : Fin 13, zoneAttraction z a) =
      (PreciseAttractionComplete.Runtime.readMaterial runtime).actualWeighted := by
  rw [(PreciseAttractionComplete.Runtime.material_read runtime).2]
  exact zone_total_same_actual

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear.PreciseTarget
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
