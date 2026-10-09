import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.Derivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandGeometry WholeBandActual TrueFlowDifferential
noncomputable section

theorem cell0_sourceResponse_integral_equation (p : Cell0Point) (h : Space) :
    cell0_sourceResponse p h = pathConst h + volterra (cell0_pathHessian p (cell0_sourceResponse p h)) := by
  have invertible : (1 - cell0_volterraHessian p).IsInvertible := by
    simpa only [cell0_residualDerivative, ContinuousLinearMap.coprod_comp_inr] using
      cell0_pathResidual_right_invertible p
  have equation := ((invertible.inverse_apply_eq).mp
    (show (1 - cell0_volterraHessian p).inverse (pathConst h) = cell0_sourceResponse p h from rfl)).symm
  change cell0_sourceResponse p h - volterra (cell0_pathHessian p (cell0_sourceResponse p h)) = pathConst h at equation
  linear_combination equation

theorem cell0_sourceResponse_starts (p : Cell0Point) (h : Space) :
    cell0_sourceResponse p h zeroTime = h := by
  have equation := congrArg (fun η : Path => η zeroTime) (cell0_sourceResponse_integral_equation p h)
  change cell0_sourceResponse p h zeroTime = h + volterra (cell0_pathHessian p (cell0_sourceResponse p h)) zeroTime at equation
  simpa only [volterra_apply_zero, add_zero] using equation

def cell0_responseCurve (p : Cell0Point) (h : Space) (s : ℝ) : Space :=
  h + pathPrimitive (cell0_pathHessian p (cell0_sourceResponse p h)) s

theorem cell0_responseCurve_is_actual (p : Cell0Point) (h : Space) (s : Time) :
    cell0_responseCurve p h s = cell0_sourceResponse p h s := by
  exact (congrArg (fun η : Path => η s) (cell0_sourceResponse_integral_equation p h)).symm

theorem cell0_sourceResponse_variational (p : Cell0Point) (h : Space) (s : Time) :
    HasDerivAt (cell0_responseCurve p h)
      (sourceHessianLinear (rawPath (cellSeed 0 p.val) s) (cell0_sourceResponse p h s)) (s : ℝ) := by
  have derivative := (hasDerivAt_pathPrimitive (cell0_pathHessian p (cell0_sourceResponse p h)) s).const_add h
  change HasDerivAt (cell0_responseCurve p h) (cell0_pathHessian p (cell0_sourceResponse p h) s) (s : ℝ) at derivative
  rw [cell0_pathHessian_apply] at derivative
  exact derivative

def cell0_initialFlowDerivative (p : Cell0Point) (s : Time) : Space →L[ℝ] Space :=
  (ContinuousMap.evalCLM ℝ s).comp (cell0_sourceResponse p)

theorem cell0_initialFlow_hasStrictFDerivAt (p : Cell0Point) (s : Time) :
    HasStrictFDerivAt (fun x => rawPath x s) (cell0_initialFlowDerivative p s)
      (cellSeed 0 p.val) :=
  (ContinuousMap.evalCLM ℝ s).hasStrictFDerivAt.comp _ (cell0_rawPath_hasStrictFDerivAt p)

theorem cell0_initialFlowDerivative_zero (p : Cell0Point) :
    cell0_initialFlowDerivative p zeroTime = ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro h
  exact cell0_sourceResponse_starts p h

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
