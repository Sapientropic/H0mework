import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Integral
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Recorded
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.Total

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceSignedEvaluator
open scoped BigOperators
noncomputable section

def totalInterval : Pair :=
  ∑ i : Basis, ∑ j : Basis,
    mul (densityPair i j) (aoInterval i j)

theorem total_interval_contains : Holds totalInterval totalIntegral := by
  unfold totalInterval totalIntegral
  apply finset_sum_holds
  intro i _
  apply finset_sum_holds
  intro j _
  have density : Holds (densityPair i j) (densityMatrix i j : ℝ) := by
    simp [densityPair,Holds]
  exact mul_holds _ _ _ _ density (ao_interval_contains i j)

def aoCoordinateResidualInterval (i j : Basis) : Pair :=
  sub (aoInterval i j) (aoAttractionInterval i j)

theorem ao_coordinate_residual_contains (i j : Basis) :
    Holds (aoCoordinateResidualInterval i j)
      (aoIntegral i j - Nuclear.aoAttraction i j) :=
  sub_holds _ _ _ _ (ao_interval_contains i j)
    (ao_attraction_interval_contains i j)

def roundedTotalIntegral : ℝ :=
  ∑ i : Basis, ∑ j : Basis,
    (densityMatrix i j : ℝ) * Nuclear.aoAttraction i j

theorem rounded_total_same_zones :
    roundedTotalIntegral = ∑ z : Option (Fin 13), ∑ a : Fin 13,
      Nuclear.zoneAttraction z a := by
  calc
    roundedTotalIntegral = ∑ a : Fin 13, Nuclear.nuclearAttraction a := by
      exact Nuclear.total_attraction_original_ao.symm
    _ = ∑ z : Option (Fin 13), ∑ a : Fin 13,
        Nuclear.zoneAttraction z a := by
      rw [show (∑ z : Option (Fin 13), ∑ a : Fin 13,
        Nuclear.zoneAttraction z a) =
          ∑ a : Fin 13, ∑ z : Option (Fin 13),
            Nuclear.zoneAttraction z a from Finset.sum_comm]
      exact (Finset.sum_congr rfl (fun a _ => Nuclear.zone_attraction_sum a)).symm

def totalCoordinateResidualInterval : Pair :=
  sub totalInterval totalAttractionInterval

theorem total_coordinate_residual_contains :
    Holds totalCoordinateResidualInterval
      (totalIntegral - roundedTotalIntegral) :=
  sub_holds _ _ _ _ total_interval_contains
    total_attraction_interval_contains

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
