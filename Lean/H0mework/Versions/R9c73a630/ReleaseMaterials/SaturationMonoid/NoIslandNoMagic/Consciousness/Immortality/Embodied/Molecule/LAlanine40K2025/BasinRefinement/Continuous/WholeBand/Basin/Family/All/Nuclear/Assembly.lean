import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Attraction
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Repulsion

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
open LAlanine40K2025.UnifiedOrbitals
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory
open scoped BigOperators
noncomputable section

/-- One-body energy of zone `z`: gradient kinetic part plus every recorded
    nucleus's electron–nuclear attraction restricted to that zone. -/
def zoneOneBody (z : Option (Fin 13)) : ℝ :=
  OneBody.zoneKinetic z + ∑ a : Fin 13, zoneAttraction z a

/-- Complete one-body plus nuclear bookkeeping: fourteen zones of kinetic and
    attraction, plus the pairwise nuclear repulsion, contract exactly to the
    original AO kinetic-plus-attraction sums plus the same repulsion. -/
theorem one_body_nuclear_total :
    ∑ z : Option (Fin 13), zoneOneBody z + totalRepulsion =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        (UnifiedOrbitals.kinetic i j + aoAttraction i j) + totalRepulsion := by
  have ksum : ∑ z : Option (Fin 13), OneBody.zoneKinetic z =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) *
        UnifiedOrbitals.kinetic i j := by
    rw [OneBody.zone_kinetic_sum,OneBody.total_kinetic_original_ao]
  have asum : ∑ z : Option (Fin 13), ∑ a : Fin 13, zoneAttraction z a =
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ) * aoAttraction i j := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => zone_attraction_sum a)]
    exact total_attraction_original_ao
  simp only [zoneOneBody]
  rw [Finset.sum_add_distrib,ksum,asum]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The fourteen zones' electron population reproduces the total nuclear
    charge within the source's rounding window. -/
theorem partition_charge_neutral :
    |∑ z : Option (Fin 13), OneBody.zonePopulation z - ∑ a : Fin 13, nuclearCharge a| ≤
      (1 : ℝ) / 10^9 := by
  rw [total_nuclear_charge]
  exact OneBody.zone_population_total

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
