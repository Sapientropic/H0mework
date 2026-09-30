import H0mework.Chemistry.LAlanineBandContinuation.ParameterScaledPath
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeContinuation WholeBandSource WholeBandGeometry
open WholeBandContinuation TrueFlowDifferential Set
noncomputable section

theorem scaledActualPath_integral_equation (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) :
    scaledActualPath c p = pathConst (cellSeed c p) +
      scaleAt p • volterra (pathGradient (scaledActualPath c p)) := by
  let seed := cellSeed c p
  have actual_eq (t : Time) :
      scaledRawFlow seed (scaleAt p) t.val = scaledActualPath c p t :=
    (scaledRawPath_eq_scaledRawFlow seed (scaleAt p) (scaleAt_abs_le_one c p inside) t).symm
  have in_cube (t : Time) : scaledRawFlow seed (scaleAt p) t.val ∈ sourceCube := by
    rw [actual_eq, scaledActualPath_apply c p inside]
    exact full_sourceCube c fields p inside _ (scaledTime (scaleAt p) (scaleAt_abs_le_one c p inside) t).property
  apply ContinuousMap.ext
  intro t
  have htime : uIcc (0 : ℝ) (t : ℝ) ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) :=
    uIcc_subset_Icc (by constructor <;> norm_num) t.property
  have hpicard := ODE.picard_eq_of_hasDerivAt
    (f := fun _ z => scaleAt p • sourceGradient z) (t₀ := 0) (t := (t : ℝ))
    (α := scaledRawFlow seed (scaleAt p)) (u := univ)
    (((sourceGradient_contDiff 1).continuous.comp continuous_snd).const_smul (scaleAt p)).continuousOn
    (fun s hs => by
      have h := (scaledRawFlow_extended seed (scaleAt p) (scaleAt_abs_le_one c p inside)
        s (htime hs)).mono htime
      change HasDerivWithinAt (scaledRawFlow seed (scaleAt p))
        (scaleAt p • globalField 1 (scaledRawFlow seed (scaleAt p) s)) (uIcc 0 (t : ℝ)) s at h
      rw [globalField_eq_original 1 _ (in_cube ⟨s, htime hs⟩)] at h
      simpa only [TrueTubeTrace.signedGradient, TrueTubeChecks.directions.2,
        Rat.cast_one, one_smul] using h)
    (fun _ _ => mem_univ _)
  change scaledActualPath c p t = seed + scaleAt p •
    ∫ s in 0..(t : ℝ), extendPath (pathGradient (scaledActualPath c p)) s
  calc
    scaledActualPath c p t = seed + scaleAt p •
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
      exact (extendPath_coe (pathGradient (scaledActualPath c p)) ⟨s, htime hs⟩).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
