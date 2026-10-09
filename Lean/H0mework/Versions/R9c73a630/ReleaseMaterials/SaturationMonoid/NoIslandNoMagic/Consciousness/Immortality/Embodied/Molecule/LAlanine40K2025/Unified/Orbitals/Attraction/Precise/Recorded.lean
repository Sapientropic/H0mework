import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.AO
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Recorded

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
noncomputable section

def PreciseResidual (i j : Basis) (error : ℚ) : Prop :=
  recordedAttraction i j - error ≤ (aoInterval i j).1 ∧
    (aoInterval i j).2 ≤ recordedAttraction i j + error

theorem actual_precise_ao_error (i j : Basis) (error : ℚ)
    (residual : PreciseResidual i j error) :
    |aoIntegral i j - (recordedAttraction i j : ℝ)| ≤ (error : ℝ) := by
  have source := ao_interval_contains i j
  rcases residual with ⟨lower,upper⟩
  have lowerReal : (recordedAttraction i j : ℝ) - error ≤
      ((aoInterval i j).1 : ℝ) := by exact_mod_cast lower
  have upperReal : ((aoInterval i j).2 : ℝ) ≤
      (recordedAttraction i j : ℝ) + error := by exact_mod_cast upper
  rw [abs_le]
  constructor <;> linarith [source.1,source.2]

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
