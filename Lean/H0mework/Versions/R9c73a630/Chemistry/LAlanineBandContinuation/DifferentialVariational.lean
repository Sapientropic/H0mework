import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.DifferentialDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation TrueFlowDifferential
noncomputable section

theorem sourceResponse_integral_equation (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (h : Space) :
    sourceResponse c p h = pathConst h + volterra (pathHessian c p (sourceResponse c p h)) := by
  have invertible : (1 - volterraHessian c p).IsInvertible := by
    simpa only [residualDerivative, ContinuousLinearMap.coprod_comp_inr] using
      residual_right_invertible c fields bounds p inside
  have equation := ((invertible.inverse_apply_eq).mp
    (show (1 - volterraHessian c p).inverse (pathConst h) = sourceResponse c p h from rfl)).symm
  change sourceResponse c p h - volterra (pathHessian c p (sourceResponse c p h)) = pathConst h at equation
  linear_combination equation

theorem sourceResponse_starts (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (h : Space) :
    sourceResponse c p h zeroTime = h := by
  have equation := congrArg (fun η : Path => η zeroTime)
    (sourceResponse_integral_equation c fields bounds p inside h)
  change sourceResponse c p h zeroTime = h + volterra (pathHessian c p (sourceResponse c p h)) zeroTime at equation
  simpa only [volterra_apply_zero, add_zero] using equation

def responseCurve (c : FullBandCell) (p : Point) (h : Space) (s : ℝ) : Space :=
  h + pathPrimitive (pathHessian c p (sourceResponse c p h)) s

theorem responseCurve_is_actual (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (h : Space) (s : Time) :
    responseCurve c p h s = sourceResponse c p h s :=
  (congrArg (fun η : Path => η s) (sourceResponse_integral_equation c fields bounds p inside h)).symm

theorem sourceResponse_variational (c : FullBandCell) (p : Point) (h : Space) (s : Time) :
    HasDerivAt (responseCurve c p h)
      (sourceHessianLinear (rawPath (cellSeed c p) s) (sourceResponse c p h s)) (s : ℝ) := by
  have derivative := (hasDerivAt_pathPrimitive (pathHessian c p (sourceResponse c p h)) s).const_add h
  change HasDerivAt (responseCurve c p h) (pathHessian c p (sourceResponse c p h) s) (s : ℝ) at derivative
  rw [pathHessian_apply] at derivative
  exact derivative

def initialFlowDerivative (c : FullBandCell) (p : Point) (s : Time) : Space →L[ℝ] Space :=
  (ContinuousMap.evalCLM ℝ s).comp (sourceResponse c p)

theorem initialFlow_hasStrictFDerivAt (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (s : Time) :
    HasStrictFDerivAt (fun x => rawPath x s) (initialFlowDerivative c p s) (cellSeed c p) :=
  (ContinuousMap.evalCLM ℝ s).hasStrictFDerivAt.comp _ (rawPath_hasStrictFDerivAt c fields bounds p inside)

theorem initialFlowDerivative_zero (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    initialFlowDerivative c p zeroTime = ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro h
  exact sourceResponse_starts c fields bounds p inside h

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
