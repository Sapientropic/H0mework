import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Charge.Assembly
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Overlap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.OriginalMetric.Charge
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient MeasureTheory
noncomputable section

/-- All space is integrated from the original Gaussian/D3 source; the finite band is not a coverage premise. -/
theorem actual_whole_space_charge :
    |(∫ x : Point, sourceDensity x)-48| ≤ (1/10^9 : ℝ) := by
  have metric := Metric.actual_charge_error recordedOverlap (1/10^12)
    (fun b c => by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using original_overlap_error b c)
  rw [recorded_charge_computed,absolute_sum_computed] at metric
  have densityBound : (densityAbsoluteSum : ℝ) ≤ 200 := by exact_mod_cast density_absolute_bound
  have sourceBound : |(recordedCharge : ℝ)-48| ≤ (1/10^10 : ℝ) := by
    have h : ((|recordedCharge-48| : ℚ) : ℝ) ≤ ((1/10^10 : ℚ) : ℝ) :=
      Rat.cast_le.mpr recorded_charge_bound
    simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat,Rat.cast_div,Rat.cast_one,Rat.cast_pow] using h
  have total := (abs_add_le ((∫ x : Point, sourceDensity x)-(recordedCharge : ℝ))
    ((recordedCharge : ℝ)-48)).trans (add_le_add metric sourceBound)
  rw [sub_add_sub_cancel] at total
  nlinarith

end
end LAlanine40K2025.UnifiedOrbitals.OriginalMetric.Charge
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
