import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionEnergy
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionPreparations
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Charge.Consumer
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Coulomb

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open BasinRefinement SourceGaussianModel SourceFiniteData MeasureTheory
open scoped InnerProductSpace
noncomputable section

theorem original_U_section_metric_residual (uTime : ℝ) (b c : Basis) :
    ‖(∫ x : Point, inner ℂ (scalarSection b 1 (spatialSlice uTime x))
      (scalarSection c 1 (spatialSlice uTime x))) - (UnifiedOrbitals.OriginalMetric.recordedOverlap b c : ℂ)‖ ≤
      (1/10^12 : ℝ) := by
  rw [original_section_metric]
  have equality : (UnifiedOrbitals.overlap b c : ℂ) -
      (UnifiedOrbitals.OriginalMetric.recordedOverlap b c : ℂ) =
      (UnifiedOrbitals.overlap b c-(UnifiedOrbitals.OriginalMetric.recordedOverlap b c : ℝ) : ℝ) := by
    push_cast
    rfl
  rw [equality,Complex.norm_real,Real.norm_eq_abs]
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using
    UnifiedOrbitals.OriginalMetric.original_overlap_error b c

theorem original_U_section_charge (uTime : ℝ) :
    ‖(∫ x : Point, sectionDensity 1 (spatialSlice uTime x)) - 48‖ ≤ (1/10^9 : ℝ) := by
  rw [original_section_charge]
  have equality : ((∫ x : Point, ContinuousGradient.sourceDensity x : ℝ) : ℂ)-48 =
      ((∫ x : Point, ContinuousGradient.sourceDensity x)-48 : ℝ) := by push_cast; rfl
  rw [equality,Complex.norm_real,Real.norm_eq_abs]
  exact UnifiedOrbitals.OriginalMetric.Charge.actual_whole_space_charge

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
