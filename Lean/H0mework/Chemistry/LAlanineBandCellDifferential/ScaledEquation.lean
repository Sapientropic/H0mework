import H0mework.Chemistry.LAlanineBandCellDifferential.ScaledPath
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeContinuation WholeBandActual WholeBandGeometry WholeBandCell0Continuation TrueFlowDifferential Set
noncomputable section

/-- The source time scaling preserves the actual orbit's integral equation on the whole window. -/
theorem cell0_scaledActualPath_integral_equation (p : Cell0Point) :
    cell0_scaledActualPath p = pathConst (cellSeed 0 p.val) +
      cell0_scaleAt p • volterra (pathGradient (cell0_scaledActualPath p)) := by
  let seed := cellSeed 0 p.val
  have actual_eq (t : Time) :
      scaledRawFlow seed (cell0_scaleAt p) t.val = cell0_scaledActualPath p t :=
    (scaledRawPath_eq_scaledRawFlow seed (cell0_scaleAt p) (cell0_scaleAt_abs_le_one p) t).symm
  have inside (t : Time) : scaledRawFlow seed (cell0_scaleAt p) t.val ∈ sourceCube := by
    rw [actual_eq, cell0_scaledActualPath_apply]
    exact cell0_full_sourceCube p _ (scaledTime (cell0_scaleAt p) (cell0_scaleAt_abs_le_one p) t).property
  apply ContinuousMap.ext
  intro t
  have htime : uIcc (0 : ℝ) (t : ℝ) ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) :=
    uIcc_subset_Icc (by constructor <;> norm_num) t.property
  have hpicard := ODE.picard_eq_of_hasDerivAt
    (f := fun _ z => cell0_scaleAt p • sourceGradient z) (t₀ := 0) (t := (t : ℝ))
    (α := scaledRawFlow seed (cell0_scaleAt p)) (u := univ)
    (((sourceGradient_contDiff 1).continuous.comp continuous_snd).const_smul (cell0_scaleAt p)).continuousOn
    (fun s hs => by
      have h := (scaledRawFlow_extended seed (cell0_scaleAt p) (cell0_scaleAt_abs_le_one p)
        s (htime hs)).mono htime
      change HasDerivWithinAt (scaledRawFlow seed (cell0_scaleAt p))
        (cell0_scaleAt p • globalField 1 (scaledRawFlow seed (cell0_scaleAt p) s)) (uIcc 0 (t : ℝ)) s at h
      rw [globalField_eq_original 1 _ (inside ⟨s, htime hs⟩)] at h
      simpa only [TrueTubeTrace.signedGradient, TrueTubeChecks.directions.2,
        Rat.cast_one, one_smul] using h)
    (fun _ _ => mem_univ _)
  change cell0_scaledActualPath p t = seed + cell0_scaleAt p •
    ∫ s in 0..(t : ℝ), extendPath (pathGradient (cell0_scaledActualPath p)) s
  calc
    cell0_scaledActualPath p t = seed + cell0_scaleAt p •
        ∫ s in 0..(t : ℝ), sourceGradient (scaledRawFlow seed (cell0_scaleAt p) s) := by
      rw [← actual_eq]
      simpa only [ODE.picard_apply, scaledRawFlow, mul_zero, rawFlow_starts,
        intervalIntegral.integral_smul] using hpicard.symm
    _ = _ := by
      congr 2
      apply intervalIntegral.integral_congr
      intro s hs
      change sourceGradient (scaledRawFlow seed (cell0_scaleAt p) s) = _
      rw [actual_eq ⟨s, htime hs⟩]
      exact (extendPath_coe (pathGradient (cell0_scaledActualPath p)) ⟨s, htime hs⟩).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
