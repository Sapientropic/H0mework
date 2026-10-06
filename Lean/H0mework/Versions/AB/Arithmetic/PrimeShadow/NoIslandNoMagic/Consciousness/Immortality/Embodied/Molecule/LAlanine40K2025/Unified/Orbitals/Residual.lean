import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Rows

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceSignedEvaluator

def RecordedResidual (interval : Pair) (recorded error : ℚ) : Prop :=
  recorded-error ≤ interval.1 ∧ interval.2 ≤ recorded+error

theorem actual_recorded_residual (interval : Pair) (recorded error : ℚ) (value : ℝ)
    (actual : Holds interval value) (computed : RecordedResidual interval recorded error) :
    |value-(recorded : ℝ)| ≤ (error : ℝ) := by
  have lower : (recorded : ℝ)-(error : ℝ) ≤ (interval.1 : ℝ) := by exact_mod_cast computed.1
  have upper : (interval.2 : ℝ) ≤ (recorded : ℝ)+(error : ℝ) := by exact_mod_cast computed.2
  exact abs_le.mpr ⟨by linarith [actual.1],by linarith [actual.2]⟩

end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
