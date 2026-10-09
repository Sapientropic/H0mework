import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.UniformBudget
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Ledger

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
noncomputable section

theorem total_within_independent_of_uniform_budget (ε : ℝ) (nonnegative : 0 ≤ ε)
    (row : ∀ a : Fin 4851,
      |aoIntegral (targetLeft a.val) (targetRight a.val) -
        (recordedAttraction (targetLeft a.val) (targetRight a.val) : ℝ)| ≤ ε) :
    |totalIntegral - independentElectronNuclear| ≤ 200 * ε + 2/10^10 := by
  calc
    _ ≤ |totalIntegral - recordedAttractionSum| +
        |recordedAttractionSum - independentElectronNuclear| := by
      have split : totalIntegral - independentElectronNuclear =
          (totalIntegral - recordedAttractionSum) +
            (recordedAttractionSum - independentElectronNuclear) := by ring
      rw [split]
      exact abs_add_le _ _
    _ ≤ 200 * ε + 2/10^10 :=
      add_le_add (total_within_recorded_of_uniform_budget ε nonnegative row)
        recorded_attraction_sum_real_within

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
