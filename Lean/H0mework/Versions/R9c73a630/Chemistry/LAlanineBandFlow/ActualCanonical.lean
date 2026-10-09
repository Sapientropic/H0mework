import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlow.ActualFullFlow
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceRawPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandActual

open SourceGaussianModel SourceSignedEvaluator WholeBandSource WholeBandReplay ContinuousGradient Set
noncomputable section

theorem source_first_length : (stepSize : ℝ) ≤ 1/2 := by
  have source : stepSize = 1/32 := by decide +kernel
  rw [source]
  norm_num

/-- The existing source runtime, evaluated at this new seed, is the actual generated local curve. -/
theorem firstCurve_eq_sourceWindow (d : Direction) (initial : InitialAt d) :
    EqOn (firstCurve d initial) (TrueTubeContinuation.windowCurve d initial.val) (Icc 0 (stepSize : ℝ)) := by
  have original : IsIntegralCurveOn (firstCurve d initial)
      (fun _ => TrueTubeTrace.signedGradient (TrueTubeSource.sign d)) (Icc 0 (stepSize : ℝ)) := by
    intro t ht
    have h := ((firstCurve_spec d initial).2.1 t ht).1
    simpa only [source_step_and_sign.2] using h
  have result := TrueTubeContinuation.local_source_matches_window d
    (TrueTubeContinuation.windowCurve d initial.val) (firstCurve d initial)
    (TrueTubeContinuation.windowCurve_extended d initial.val) 0 stepSize (by norm_num)
    (by simpa using source_first_length) original
    (firstCurve_stays_in_sourceCube d initial) (by
      rw [TrueTubeContinuation.windowCurve_starts]
      exact (firstCurve_spec d initial).1)
  simpa only [add_zero] using result

theorem fullFlow_eq_sourceRaw (p : Cell0Point) :
    EqOn (fullFlow p) (TrueFlowDifferential.rawFlow (WholeBandGeometry.cellSeed 0 p.val)) firstWindow := by
  intro t ht
  by_cases negative : t ≤ 0
  · rw [fullFlow, TrueFlowDifferential.rawFlow, LAlanineTrueTube.Signed.full_left _ _ _ negative,
      LAlanineTrueTube.Signed.full_left _ _ _ negative]
    exact firstCurve_eq_sourceWindow 0 (cell0Initial 0 p) ⟨by linarith, by linarith [ht.1]⟩
  · have positive : 0 ≤ t := by linarith
    have same : TrueTubeContinuation.windowCurve 0 (WholeBandGeometry.cellSeed 0 p.val) 0 =
        TrueTubeContinuation.windowCurve 1 (WholeBandGeometry.cellSeed 0 p.val) 0 := by
      rw [TrueTubeContinuation.windowCurve_starts, TrueTubeContinuation.windowCurve_starts]
    rw [fullFlow, TrueFlowDifferential.rawFlow,
      LAlanineTrueTube.Signed.full_right (directions_same_initial p) _ positive,
      LAlanineTrueTube.Signed.full_right same _ positive]
    exact firstCurve_eq_sourceWindow 1 (cell0Initial 1 p) ⟨positive, ht.2⟩

theorem sourceRaw_original_on_firstWindow (p : Cell0Point) :
    IsIntegralCurveOn (TrueFlowDifferential.rawFlow (WholeBandGeometry.cellSeed 0 p.val))
      (fun _ => sourceGradient) firstWindow := by
  intro t ht
  have h := fullFlow_original p t ht
  rw [fullFlow_eq_sourceRaw p ht] at h
  exact h.congr_of_mem (fun s hs => (fullFlow_eq_sourceRaw p hs).symm) ht

end
end LAlanine40K2025.BasinRefinement.WholeBandActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
