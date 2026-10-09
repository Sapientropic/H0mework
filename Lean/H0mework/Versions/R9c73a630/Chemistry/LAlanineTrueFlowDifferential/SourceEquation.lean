import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator

/-!
The original full flow satisfies the path-space Volterra equation. The Picard converse
consumes the derivative of that same actual flow on the original closed time interval.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual Set
noncomputable section

/-- The actual trajectory is a fixed point of its original source-gradient integral equation. -/
theorem actualPath_integral_equation (p : BandPoint) :
    actualPath p = pathConst (ContinuousParameterMap.initialMap 0 4 p.val) +
      volterra (pathGradient (actualPath p)) := by
  apply ContinuousMap.ext
  intro t
  have htime : uIcc (0 : ℝ) (t : ℝ) ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) :=
    uIcc_subset_Icc (by constructor <;> norm_num) t.property
  have hpicard := ODE.picard_eq_of_hasDerivAt
    (f := fun _ => sourceGradient) (t₀ := 0) (t := (t : ℝ))
    (α := fullFlow p) (u := univ)
    ((sourceGradient_contDiff 1).continuous.comp continuous_snd).continuousOn
    (fun s hs => (fullFlow_original p s (htime hs)).mono htime)
    (fun _ _ => mem_univ _)
  change fullFlow p t = ContinuousParameterMap.initialMap 0 4 p.val +
    ∫ s in 0..(t : ℝ), extendPath (pathGradient (actualPath p)) s
  calc
    fullFlow p t = ContinuousParameterMap.initialMap 0 4 p.val +
        ∫ s in 0..(t : ℝ), sourceGradient (fullFlow p s) := by
      simpa only [ODE.picard_apply, fullFlow_starts] using hpicard.symm
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      exact (extendPath_coe (pathGradient (actualPath p)) ⟨s, htime hs⟩).symm

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
