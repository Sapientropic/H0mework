import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceActualPath

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueTubeSource TrueTubeTrace TrueTubeContinuation TrueTubeWholeActual Set
noncomputable section

theorem globalField_negative : globalField 0 = fun x => -globalField 1 x := by
  funext x
  simp only [globalField, LAlanineTrueTube.Dynamics.extension, signedGradient,
    TrueTubeChecks.directions.1, TrueTubeChecks.directions.2,
    Rat.cast_neg, Rat.cast_one, neg_one_smul, one_smul]

def rawFlow (x : Point) : ℝ → Point :=
  LAlanineTrueTube.Signed.full (windowCurve 0 x) (windowCurve 1 x)

theorem rawFlow_starts (x : Point) : rawFlow x 0 = x := by
  rw [rawFlow, LAlanineTrueTube.Signed.full_zero, windowCurve_starts]

theorem rawFlow_extended (x : Point) :
    IsIntegralCurveOn (rawFlow x) (fun _ => globalField 1)
      (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
  apply LAlanineTrueTube.Signed.full_integralCurve (by norm_num)
  · rw [windowCurve_starts, windowCurve_starts]
  · simpa only [globalField_negative] using windowCurve_extended 0 x
  · exact windowCurve_extended 1 x

def rawPath (x : Point) : Path where
  toFun t := rawFlow x t.val
  continuous_toFun := (rawFlow_extended x).continuousOn.domRestrict

theorem rawPath_starts (x : Point) : rawPath x zeroTime = x := rawFlow_starts x

theorem rawPath_eq_actualPath (p : BandPoint) :
    rawPath (ContinuousParameterMap.initialMap 0 4 p.val) = actualPath p := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
