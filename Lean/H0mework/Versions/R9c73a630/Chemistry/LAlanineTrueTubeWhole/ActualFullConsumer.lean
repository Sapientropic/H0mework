import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualFullModel
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ContinuationSteps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeActual

open SourceGaussianModel SourceSignedEvaluator TrueTubeSource TrueTubeTrace TrueTubeActual
open TrueTubeContinuation ContinuousGradient Set
noncomputable section

theorem original_full_from_local (localLaws : ∀ d i, LocalStepLaw d i) (p : BandPoint) :
    IsIntegralCurveOn (fullFlow p) (fun _ => sourceGradient) (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
  have left : IsIntegralCurveOn (negativeFlow p) (fun _ x => -sourceGradient x) (Icc (0 : ℝ) (1 / 2)) := by
    have paid := window_is_original_flow 0 (bandInitial 0 p).val (bandInitial 0 p).property (localLaws 0)
    have field : signedGradient (sign 0 : ℝ) = fun x => -sourceGradient x := by
      funext x
      change (sign 0 : ℝ) • sourceGradient x = _
      rw [TrueTubeChecks.directions.1, Rat.cast_neg, Rat.cast_one, neg_one_smul]
    rw [field] at paid
    exact paid
  have right : IsIntegralCurveOn (positiveFlow p) (fun _ => sourceGradient) (Icc (0 : ℝ) (1 / 2)) := by
    have paid := window_is_original_flow 1 (bandInitial 1 p).val (bandInitial 1 p).property (localLaws 1)
    have field : signedGradient (sign 1 : ℝ) = sourceGradient := by
      funext x
      change (sign 1 : ℝ) • sourceGradient x = _
      rw [TrueTubeChecks.directions.2, Rat.cast_one, one_smul]
    rw [field] at paid
    exact paid
  exact LAlanineTrueTube.Signed.full_integralCurve (by norm_num) (directions_same_initial p) left right

theorem full_stays_from_local (localLaws : ∀ d i, LocalStepLaw d i)
    (p : BandPoint) (t : ℝ) (time : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) : fullFlow p t ∈ sourceCube := by
  by_cases ht : t ≤ 0
  · rw [fullFlow, LAlanineTrueTube.Signed.full_left _ _ _ ht]
    exact window_stays_source 0 (bandInitial 0 p).val (bandInitial 0 p).property (localLaws 0)
      (-t) ⟨by linarith, by linarith [time.1]⟩
  · rw [fullFlow, LAlanineTrueTube.Signed.full_right (directions_same_initial p) t (by linarith)]
    exact window_stays_source 1 (bandInitial 1 p).val (bandInitial 1 p).property (localLaws 1)
      t ⟨by linarith, time.2⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
