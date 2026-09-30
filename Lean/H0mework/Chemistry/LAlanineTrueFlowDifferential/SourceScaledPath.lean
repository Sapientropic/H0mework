import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceRawPath
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceSignedEvaluator ContinuousGradient TrueTubeWholeActual
open TrueTubeContinuation WholeCellPartition Set Metric
noncomputable section

def scaleAt (p : BandPoint) : ℝ := 2 * p.val 2

theorem scaleAt_abs_le_one (p : BandPoint) : |scaleAt p| ≤ 1 := by
  have lower := p.property.1 (2 : Fin 3)
  have upper := p.property.2 (2 : Fin 3)
  norm_num [fullLower, fullUpper, fullLowerQ, fullUpperQ, halfFlow_exact] at lower upper
  unfold scaleAt
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem scaledTime_mem (a : ℝ) (ha : |a| ≤ 1) (t : Time) :
    a * t.val ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
  apply abs_le.mp
  calc
    |a * t.val| = |a| * |t.val| := abs_mul _ _
    _ ≤ 1 * (1 / 2 : ℝ) :=
      mul_le_mul ha (abs_le.mpr t.property) (abs_nonneg _) (by norm_num)
    _ = 1 / 2 := one_mul _

def scaledTime (a : ℝ) (ha : |a| ≤ 1) (t : Time) : Time :=
  ⟨a * t.val, scaledTime_mem a ha t⟩

def scaledRawFlow (x : Point) (a : ℝ) (t : ℝ) : Point := rawFlow x (a * t)

def scaledRawPath (x : Point) (a : ℝ) : Path where
  toFun t := extendPath (rawPath x) (a * t.val)
  continuous_toFun := (continuous_extendPath (rawPath x)).comp
    (continuous_const.mul continuous_subtype_val)

theorem scaledRawPath_eq_scaledRawFlow (x : Point) (a : ℝ) (ha : |a| ≤ 1) (t : Time) :
    scaledRawPath x a t = scaledRawFlow x a t.val :=
  extendPath_coe (rawPath x) (scaledTime a ha t)

theorem scaledRawFlow_starts (x : Point) (a : ℝ) : scaledRawFlow x a 0 = x := by
  simp only [scaledRawFlow, mul_zero, rawFlow_starts]

theorem scaledRawPath_starts (x : Point) (a : ℝ) : scaledRawPath x a zeroTime = x := by
  change extendPath (rawPath x) (a * 0) = x
  rw [mul_zero]
  exact (extendPath_coe (rawPath x) zeroTime).trans (rawPath_starts x)

theorem scaledRawFlow_extended (x : Point) (a : ℝ) (ha : |a| ≤ 1) :
    IsIntegralCurveOn (scaledRawFlow x a) (fun _ z => a • globalField 1 z)
      (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
  intro t ht
  exact (rawFlow_extended x (a * t) (scaledTime_mem a ha ⟨t, ht⟩)).scomp t
    (hasDerivAt_const_mul a).hasDerivWithinAt
    (fun s hs => scaledTime_mem a ha ⟨s, hs⟩)

def scaledActualPath (p : BandPoint) : Path :=
  scaledRawPath (ContinuousParameterMap.initialMap 0 4 p.val) (scaleAt p)

theorem scaledActualPath_apply (p : BandPoint) (t : Time) :
    scaledActualPath p t = actualPath p (scaledTime (scaleAt p) (scaleAt_abs_le_one p) t) := by
  change extendPath (rawPath (ContinuousParameterMap.initialMap 0 4 p.val)) _ = _
  rw [rawPath_eq_actualPath]
  exact extendPath_coe (actualPath p) (scaledTime (scaleAt p) (scaleAt_abs_le_one p) t)

theorem scaledActualPath_starts (p : BandPoint) :
    scaledActualPath p zeroTime = ContinuousParameterMap.initialMap 0 4 p.val :=
  scaledRawPath_starts _ _

theorem scaledActualPath_in_hull (p : BandPoint) (t : Time) :
    InRectangle TrueTubeHullSource.box (scaledActualPath p t) := by
  rw [scaledActualPath_apply]
  exact actualPath_in_hull p _

theorem scaledActualPath_hessian_bound (p : BandPoint) (t : Time) :
    ‖sourceHessianLinear (scaledActualPath p t)‖ ≤ (TrueTubeHull.lipschitzConstant : ℝ) :=
  TrueTubeHull.hessian_norm _ (scaledActualPath_in_hull p t)

theorem path_near_scaled_actual_in_cube (p : BandPoint) (u : Path)
    (nearby : dist u (scaledActualPath p) < (1 / 100 : ℝ)) (t : Time) : u t ∈ sourceCube :=
  nearby_hull_inside_cube _ _ (scaledActualPath_in_hull p t)
    ((ContinuousMap.dist_apply_le_dist t).trans_lt nearby)

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
