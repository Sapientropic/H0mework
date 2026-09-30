import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusPath
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceMargin
import H0mework.Chemistry.LAlanineTrueTubeWhole.ActualFullFlow
import H0mework.Chemistry.LAlanineTrueTubeWhole.ErrorSupport

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceSignedEvaluator ContinuousGradient TrueTubeWholeActual
open TrueTubeWholeError Set Metric
noncomputable section

def actualPath (p : BandPoint) : Path where
  toFun t := fullFlow p t.val
  continuous_toFun := (fullFlow_original p).continuousOn.domRestrict

theorem actualPath_starts (p : BandPoint) :
    actualPath p zeroTime = ContinuousParameterMap.initialMap 0 4 p.val := fullFlow_starts p

theorem actualPath_in_hull (p : BandPoint) (t : Time) :
    InRectangle TrueTubeHullSource.box (actualPath p t) :=
  (TrueTubeTrace.inRectangle_iff _ _).mpr (full_inside_common_from_local actual_step p t.val t.property)

theorem path_near_actual_in_cube (p : BandPoint) (u : Path)
    (nearby : dist u (actualPath p) < (1 / 100 : ℝ)) (t : Time) : u t ∈ sourceCube :=
  nearby_hull_inside_cube _ _ (actualPath_in_hull p t)
    ((ContinuousMap.dist_apply_le_dist t).trans_lt nearby)

theorem actualPath_hessian_bound (p : BandPoint) (t : Time) :
    ‖sourceHessianLinear (actualPath p t)‖ ≤ (TrueTubeHull.lipschitzConstant : ℝ) :=
  TrueTubeHull.hessian_norm _ (actualPath_in_hull p t)

theorem actual_volterra_budget : (TrueTubeHull.lipschitzConstant : ℝ) / 2 < 1 := by
  linarith [TrueTubeHull.constant_strict.2]

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
