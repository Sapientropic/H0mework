import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Recorded
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Kernel
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Residual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Kinetic
open BasinRefinement SourceFiniteData SourceSignedEvaluator
open LAlanine40K2025.UnifiedOrbitals OriginalMetric
noncomputable section

/-- Each computed kinetic row contains the actual matrix element. -/
theorem actual_kinetic_row_contains (b c : Basis) (row : List Summand)
    (computed : KineticRowComputed radialMaterial b c row) :
    Holds (rowInterval radialMaterial row) (kinetic b c) :=
  kinetic_row_contains radialMaterial b c row computed
    (fun s _ => original_radial_contains s.kernel)

/-- The generated row proves the kinetic integral matches the ledger record. -/
theorem actual_kinetic_row_error (b c : Basis) (row : List Summand)
    (computed : KineticRowComputed radialMaterial b c row)
    (residual : RecordedResidual (rowInterval radialMaterial row)
      (recordedKinetic b c) (1/10^12)) :
    |kinetic b c-(recordedKinetic b c : ℝ)| ≤ ((1/10^12 : ℚ) : ℝ) :=
  actual_recorded_residual _ _ _ _
    (actual_kinetic_row_contains b c row computed) residual

end
end LAlanine40K2025.UnifiedOrbitals.Kinetic
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
