import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual
noncomputable section

theorem sourceResponse_integral_equation (p : BandPoint) (h : Space) :
    sourceResponse p h = pathConst h + volterra (pathHessian p (sourceResponse p h)) := by
  have invertible : (1 - volterraHessian p).IsInvertible := by
    simpa only [residualDerivative, ContinuousLinearMap.coprod_comp_inr] using
      pathResidual_right_invertible p
  have equation := ((invertible.inverse_apply_eq).mp
    (show (1 - volterraHessian p).inverse (pathConst h) = sourceResponse p h from rfl)).symm
  change sourceResponse p h - volterra (pathHessian p (sourceResponse p h)) = pathConst h at equation
  linear_combination equation

theorem sourceResponse_starts (p : BandPoint) (h : Space) :
    sourceResponse p h zeroTime = h := by
  have equation := congrArg (fun η : Path => η zeroTime) (sourceResponse_integral_equation p h)
  change sourceResponse p h zeroTime = h + volterra (pathHessian p (sourceResponse p h)) zeroTime at equation
  simpa only [volterra_apply_zero, add_zero] using equation

def responseCurve (p : BandPoint) (h : Space) (s : ℝ) : Space :=
  h + pathPrimitive (pathHessian p (sourceResponse p h)) s

theorem responseCurve_is_actual (p : BandPoint) (h : Space) (s : Time) :
    responseCurve p h s = sourceResponse p h s := by
  exact (congrArg (fun η : Path => η s) (sourceResponse_integral_equation p h)).symm

theorem sourceResponse_variational (p : BandPoint) (h : Space) (s : Time) :
    HasDerivAt (responseCurve p h)
      (sourceHessianLinear (actualPath p s) (sourceResponse p h s)) (s : ℝ) := by
  have derivative := (hasDerivAt_pathPrimitive (pathHessian p (sourceResponse p h)) s).const_add h
  change HasDerivAt (responseCurve p h) (pathHessian p (sourceResponse p h) s) (s : ℝ) at derivative
  rw [pathHessian_apply] at derivative
  exact derivative

def initialFlowDerivative (p : BandPoint) (s : Time) : Space →L[ℝ] Space :=
  (ContinuousMap.evalCLM ℝ s).comp (sourceResponse p)

theorem initialFlow_hasStrictFDerivAt (p : BandPoint) (s : Time) :
    HasStrictFDerivAt (fun x => rawPath x s) (initialFlowDerivative p s)
      (ContinuousParameterMap.initialMap 0 4 p.val) :=
  (ContinuousMap.evalCLM ℝ s).hasStrictFDerivAt.comp _ (rawPath_hasStrictFDerivAt p)

theorem initialFlowDerivative_zero (p : BandPoint) :
    initialFlowDerivative p zeroTime = ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro h
  exact sourceResponse_starts p h

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
