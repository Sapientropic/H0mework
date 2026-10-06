import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Sections
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Metric.Charge
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient MeasureTheory
open scoped InnerProductSpace
noncomputable section

theorem original_section_pair_integrable (time : ℝ) (b c : Basis) :
    Integrable (fun x : Point => inner ℂ
      (scalarSection b 1 (spatialSlice time x)) (scalarSection c 1 (spatialSlice time x))) := by
  simp_rw [slice_pair]
  exact (UnifiedOrbitals.source_product_integrable b c zeroJet zeroJet).ofReal

theorem original_section_metric (time : ℝ) (b c : Basis) :
    (∫ x : Point, inner ℂ (scalarSection b 1 (spatialSlice time x))
      (scalarSection c 1 (spatialSlice time x))) = (UnifiedOrbitals.overlap b c : ℂ) := by
  simp_rw [slice_pair]
  exact integral_complex_ofReal

theorem original_section_density_integrable (time : ℝ) :
    Integrable (fun x : Point => sectionDensity 1 (spatialSlice time x)) := by
  simp_rw [original_D3_section_density,slice_coordinates]
  exact (GlobalSource.source_bilinear_integrable zeroJet zeroJet).ofReal

theorem original_section_charge (time : ℝ) :
    (∫ x : Point, sectionDensity 1 (spatialSlice time x)) = (∫ x : Point, sourceDensity x : ℝ) := by
  simp_rw [original_D3_section_density,slice_coordinates]
  exact integral_complex_ofReal

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
