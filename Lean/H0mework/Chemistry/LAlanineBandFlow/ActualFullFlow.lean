import H0mework.Chemistry.LAlanineBandFlow.ActualRealization
import H0mework.Chemistry.LAlanineTrueTubeWhole.SignedGlue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandActual

open SourceGaussianModel SourceSignedEvaluator WholeBandSource WholeBandGeometry WholeBandReplay
open ContinuousGradient Set
noncomputable section

abbrev Cell0Point := {p : Point // p ∈ cellDomain 0}
def negativeFlow (p : Cell0Point) : ℝ → Point := firstCurve 0 (cell0Initial 0 p)
def positiveFlow (p : Cell0Point) : ℝ → Point := firstCurve 1 (cell0Initial 1 p)
def fullFlow (p : Cell0Point) : ℝ → Point := LAlanineTrueTube.Signed.full (negativeFlow p) (positiveFlow p)
def firstWindow : Set ℝ := Icc (-(stepSize : ℝ)) (stepSize : ℝ)

theorem directions_same_initial (p : Cell0Point) : negativeFlow p 0 = positiveFlow p 0 :=
  (firstCurve_spec 0 (cell0Initial 0 p)).1.trans (firstCurve_spec 1 (cell0Initial 1 p)).1.symm

theorem fullFlow_starts (p : Cell0Point) : fullFlow p 0 = cellSeed 0 p.val := by
  rw [fullFlow, LAlanineTrueTube.Signed.full_zero]
  exact (firstCurve_spec 0 (cell0Initial 0 p)).1

theorem negativeFlow_original (p : Cell0Point) :
    IsIntegralCurveOn (negativeFlow p) (fun _ x => -sourceGradient x) (Icc 0 (stepSize : ℝ)) := by
  intro t ht
  have h := ((firstCurve_spec 0 (cell0Initial 0 p)).2.1 t ht).1
  have sourceSign : (sign 0 : ℝ) = -1 := by norm_num [source_step_and_sign.2, TrueTubeChecks.directions.1]
  simpa only [negativeFlow, TrueTubeTrace.signedGradient, sourceSign, neg_one_smul] using h

theorem positiveFlow_original (p : Cell0Point) :
    IsIntegralCurveOn (positiveFlow p) (fun _ => sourceGradient) (Icc 0 (stepSize : ℝ)) := by
  intro t ht
  have h := ((firstCurve_spec 1 (cell0Initial 1 p)).2.1 t ht).1
  have sourceSign : (sign 1 : ℝ) = 1 := by norm_num [source_step_and_sign.2, TrueTubeChecks.directions.2]
  simpa only [positiveFlow, TrueTubeTrace.signedGradient, sourceSign, one_smul] using h

theorem fullFlow_original (p : Cell0Point) :
    IsIntegralCurveOn (fullFlow p) (fun _ => sourceGradient) firstWindow :=
  LAlanineTrueTube.Signed.full_integralCurve
    (Rat.cast_pos.mpr (all_row_arithmetic 0 0 0).positive_step).le
    (directions_same_initial p) (negativeFlow_original p) (positiveFlow_original p)

theorem fullFlow_stays (p : Cell0Point) (t : ℝ) (ht : t ∈ firstWindow) : fullFlow p t ∈ sourceCube := by
  by_cases negative : t ≤ 0
  · rw [fullFlow, LAlanineTrueTube.Signed.full_left _ _ _ negative]
    exact firstCurve_stays_in_sourceCube 0 (cell0Initial 0 p) (-t) ⟨by linarith, by linarith [ht.1]⟩
  · rw [fullFlow, LAlanineTrueTube.Signed.full_right (directions_same_initial p) t (by linarith)]
    exact firstCurve_stays_in_sourceCube 1 (cell0Initial 1 p) t ⟨by linarith, ht.2⟩

theorem fullFlow_zero_derivative (p : Cell0Point) :
    HasDerivAt (fullFlow p) (sourceGradient (cellSeed 0 p.val)) 0 := by
  have h := LAlanineTrueTube.Signed.full_hasDerivAt_zero
    (Rat.cast_pos.mpr (all_row_arithmetic 0 0 0).positive_step)
    (directions_same_initial p) (negativeFlow_original p) (positiveFlow_original p)
  simpa only [fullFlow,
    show negativeFlow p 0 = cellSeed 0 p.val from (firstCurve_spec 0 (cell0Initial 0 p)).1] using h

end
end LAlanine40K2025.BasinRefinement.WholeBandActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
