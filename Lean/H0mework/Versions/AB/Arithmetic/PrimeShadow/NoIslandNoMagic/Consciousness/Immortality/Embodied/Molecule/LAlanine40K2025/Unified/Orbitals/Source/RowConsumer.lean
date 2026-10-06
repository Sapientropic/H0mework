import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Kernel
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Recorded
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Residual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.OriginalMetric
open BasinRefinement SourceFiniteData SourceSignedEvaluator
noncomputable section

theorem actual_row_contains (b c : Basis) (row : List Summand)
    (computed : RowComputed radialMaterial b c row) :
    Holds (rowInterval radialMaterial row) (overlap b c) :=
  original_row_contains radialMaterial b c row computed (fun s _ => original_radial_contains s.kernel)

theorem actual_row_error (b c : Basis) (row : List Summand)
    (computed : RowComputed radialMaterial b c row)
    (residual : RecordedResidual (rowInterval radialMaterial row) (recordedOverlap b c) (1/10^12)) :
    |overlap b c-(recordedOverlap b c : ℝ)| ≤ (1/10^12 : ℚ) :=
  actual_recorded_residual _ _ _ _ (actual_row_contains b c row computed) residual

end
end LAlanine40K2025.UnifiedOrbitals.OriginalMetric
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
