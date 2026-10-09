import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledPath
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeContinuation TrueTubeWholeActual Set
noncomputable section

/-- The source time scaling preserves the actual orbit's integral equation on the whole window. -/
theorem scaledActualPath_integral_equation (p : BandPoint) :
    scaledActualPath p = pathConst (ContinuousParameterMap.initialMap 0 4 p.val) +
      scaleAt p • volterra (pathGradient (scaledActualPath p)) := by
  let seed := ContinuousParameterMap.initialMap 0 4 p.val
  have actual_eq (t : Time) :
      scaledRawFlow seed (scaleAt p) t.val = scaledActualPath p t :=
    (scaledRawPath_eq_scaledRawFlow seed (scaleAt p) (scaleAt_abs_le_one p) t).symm
  have inside (t : Time) : scaledRawFlow seed (scaleAt p) t.val ∈ sourceCube := by
    rw [actual_eq, scaledActualPath_apply]
    exact fullFlow_stays p _ (scaledTime (scaleAt p) (scaleAt_abs_le_one p) t).property
  apply ContinuousMap.ext
  intro t
  have htime : uIcc (0 : ℝ) (t : ℝ) ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) :=
    uIcc_subset_Icc (by constructor <;> norm_num) t.property
  have hpicard := ODE.picard_eq_of_hasDerivAt
    (f := fun _ z => scaleAt p • sourceGradient z) (t₀ := 0) (t := (t : ℝ))
    (α := scaledRawFlow seed (scaleAt p)) (u := univ)
    (((sourceGradient_contDiff 1).continuous.comp continuous_snd).const_smul (scaleAt p)).continuousOn
    (fun s hs => by
      have h := (scaledRawFlow_extended seed (scaleAt p) (scaleAt_abs_le_one p)
        s (htime hs)).mono htime
      change HasDerivWithinAt (scaledRawFlow seed (scaleAt p))
        (scaleAt p • globalField 1 (scaledRawFlow seed (scaleAt p) s)) (uIcc 0 (t : ℝ)) s at h
      rw [globalField_eq_original 1 _ (inside ⟨s, htime hs⟩)] at h
      simpa only [TrueTubeTrace.signedGradient, TrueTubeChecks.directions.2,
        Rat.cast_one, one_smul] using h)
    (fun _ _ => mem_univ _)
  change scaledActualPath p t = seed + scaleAt p •
    ∫ s in 0..(t : ℝ), extendPath (pathGradient (scaledActualPath p)) s
  calc
    scaledActualPath p t = seed + scaleAt p •
        ∫ s in 0..(t : ℝ), sourceGradient (scaledRawFlow seed (scaleAt p) s) := by
      rw [← actual_eq]
      simpa only [ODE.picard_apply, scaledRawFlow, mul_zero, rawFlow_starts,
        intervalIntegral.integral_smul] using hpicard.symm
    _ = _ := by
      congr 2
      apply intervalIntegral.integral_congr
      intro s hs
      change sourceGradient (scaledRawFlow seed (scaleAt p) s) = _
      rw [actual_eq ⟨s, htime hs⟩]
      exact (extendPath_coe (pathGradient (scaledActualPath p)) ⟨s, htime hs⟩).symm

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
