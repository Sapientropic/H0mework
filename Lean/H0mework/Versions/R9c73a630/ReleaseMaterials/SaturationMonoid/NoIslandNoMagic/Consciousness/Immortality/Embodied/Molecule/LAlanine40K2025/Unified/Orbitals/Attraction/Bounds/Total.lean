import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.AO
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AnalyticAttraction.Runtime.Consumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceFiniteData
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceSignedEvaluator
open scoped BigOperators
noncomputable section

def densityPair (i j : Basis) : Pair :=
  (densityMatrix i j,densityMatrix i j)

def totalAttractionInterval : Pair :=
  ∑ i : Basis, ∑ j : Basis,
    mul (densityPair i j) (aoAttractionInterval i j)

theorem total_attraction_interval_contains :
    Holds totalAttractionInterval
      (∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℝ) * Nuclear.aoAttraction i j) := by
  unfold totalAttractionInterval
  apply finset_sum_holds
  intro i _
  apply finset_sum_holds
  intro j _
  have density : Holds (densityPair i j) (densityMatrix i j : ℝ) := by
    simp [densityPair,Holds]
  exact mul_holds _ _ _ _ density (ao_attraction_interval_contains i j)

theorem actual_zone_total_interval_contains
    (runtime : _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingRuntimeState
      AnalyticAttraction.Runtime.process) :
    Holds totalAttractionInterval
      (∑ z : Option (Fin 13), ∑ a : Fin 13,
        (AnalyticAttraction.Runtime.readMaterial runtime).parent.parent.parent.zoneAttraction z a) := by
  have source := AnalyticAttraction.Runtime.actual_zone_attraction_analytic runtime
  have replace :
      (∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℝ) *
          (AnalyticAttraction.Runtime.readMaterial runtime).analyticNuclearAO i j) =
      ∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℝ) * Nuclear.aoAttraction i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← AnalyticAttraction.Runtime.actual_analytic_ao runtime i j]
  rw [source,replace]
  exact total_attraction_interval_contains

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
