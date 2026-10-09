import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.SourceFaces

/-! Direct consumption of Mathlib's divergence theorem on the original parameter box. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary

open SourceGaussianModel WholeCellPartition Set MeasureTheory
open scoped BigOperators
noncomputable section

theorem flux_divergence_continuous (smooth : ContDiff ℝ 1 pulledFlux) :
    Continuous (fun p => ∑ i : Fin 3, fderiv ℝ pulledFlux p (Pi.single i 1) i) := by
  have derivativeContinuous : Continuous (fderiv ℝ pulledFlux) := smooth.continuous_fderiv (by norm_num)
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).comp
    (derivativeContinuous.clm_apply continuous_const))

theorem netFlux_eq_integral_divergence (smooth : ContDiff ℝ 1 pulledFlux) :
    netFlux = ∫ p in fullDomain, ∑ i : Fin 3, fderiv ℝ pulledFlux p (Pi.single i 1) i := by
  rw [netFlux_eq_front_minus_back]
  exact (integral_divergence_of_hasFDerivAt_off_countable fullLower fullUpper
    (fun i => Rat.cast_le.mpr (full_ordered i).le) pulledFlux (fderiv ℝ pulledFlux)
    ∅ countable_empty smooth.continuous.continuousOn
    (fun p _ => (smooth.differentiable (by norm_num) p).hasFDerivAt)
    ((flux_divergence_continuous smooth).continuousOn.integrableOn_compact full_compact)).symm

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
