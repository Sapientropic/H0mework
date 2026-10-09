import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.Reifier

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem vcell13_13_residual_two :
    PreciseResidual (13 : Basis) (13 : Basis) (2/10^12 : ℚ) := by
  unfold PreciseResidual
  decide +kernel

theorem vcell13_13_residual_one_fails :
    ¬ PreciseResidual (13 : Basis) (13 : Basis) (1/10^12 : ℚ) := by
  unfold PreciseResidual
  decide +kernel

theorem vcell13_13_actual_two :
    |aoIntegral (13 : Basis) (13 : Basis) -
      (recordedAttraction (13 : Basis) (13 : Basis) : ℝ)| ≤
        ((2/10^12 : ℚ) : ℝ) :=
  actual_precise_ao_error 13 13 (2/10^12) vcell13_13_residual_two

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
