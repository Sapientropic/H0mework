import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Total

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.BasinRefinement.SourceFiniteData
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
noncomputable section

/-- The picobohr-centred Root164 interval is strictly below the original
    report at AO(0,3), even after two picohartree of room. -/
theorem rounded_row03_separated :
    (aoAttractionInterval (0 : Basis) (3 : Basis)).2 + 2/10^12 <
      recordedAttraction (0 : Basis) (3 : Basis) := by
  decide +kernel

/-- The full target-frame coordinates restore the original report row. -/
theorem precise_row03_recorded :
    PreciseResidual (0 : Basis) (3 : Basis) (1/10^12) := by
  unfold PreciseResidual
  constructor <;> decide +kernel

theorem actual_coordinate_effect_nonzero :
    Nuclear.aoAttraction (0 : Basis) (3 : Basis) <
      aoIntegral (0 : Basis) (3 : Basis) := by
  have rounded := ao_attraction_interval_contains (0 : Basis) (3 : Basis)
  have precise := ao_interval_contains (0 : Basis) (3 : Basis)
  have gap : ((aoAttractionInterval (0 : Basis) (3 : Basis)).2 : ℝ) +
      (2/10^12 : ℝ) < (recordedAttraction (0 : Basis) (3 : Basis) : ℝ) := by
    have h : (((aoAttractionInterval (0 : Basis) (3 : Basis)).2 +
        (2/10^12 : ℚ) : ℚ) : ℝ) <
        (recordedAttraction (0 : Basis) (3 : Basis) : ℝ) :=
      (Rat.cast_lt (K := ℝ)).mpr rounded_row03_separated
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using h
  have centre : (recordedAttraction (0 : Basis) (3 : Basis) : ℝ) -
      (1/10^12 : ℝ) ≤ ((aoInterval (0 : Basis) (3 : Basis)).1 : ℝ) := by
    have h : (((recordedAttraction (0 : Basis) (3 : Basis) -
        (1/10^12 : ℚ) : ℚ) : ℝ)) ≤
        ((aoInterval (0 : Basis) (3 : Basis)).1 : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr precise_row03_recorded.1
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow,
      Rat.cast_one] using h
  linarith [rounded.2,precise.1]

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
