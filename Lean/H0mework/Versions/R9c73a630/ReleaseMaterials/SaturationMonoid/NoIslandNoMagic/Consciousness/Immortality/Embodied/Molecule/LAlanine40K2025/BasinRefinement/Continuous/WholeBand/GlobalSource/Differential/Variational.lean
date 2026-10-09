import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Implicit

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel
open _root_.LAlanineTrueFlowDifferential
noncomputable section

theorem response_integral_equation (x : Point) (h : Space) :
    response x h = pathConst h+volterra (derivativeOnPath x (response x h)) := by
  have invertible : (1-volterra.comp (derivativeOnPath x)).IsInvertible := by
    simpa only [residualDerivative,ContinuousLinearMap.coprod_comp_inr] using residual_right_invertible x
  have equation := ((invertible.inverse_apply_eq).mp
    (show (1-volterra.comp (derivativeOnPath x)).inverse (pathConst h) = response x h from rfl)).symm
  change response x h-volterra (derivativeOnPath x (response x h)) = pathConst h at equation
  linear_combination equation

theorem response_starts (x : Point) (h : Space) : response x h zeroTime = h := by
  have equation := congrArg (fun p : Path => p zeroTime) (response_integral_equation x h)
  change response x h zeroTime = h+volterra (derivativeOnPath x (response x h)) zeroTime at equation
  simpa only [volterra_apply_zero,add_zero] using equation

def responseCurve (x : Point) (h : Space) (t : ℝ) : Space :=
  h+pathPrimitive (derivativeOnPath x (response x h)) t

theorem responseCurve_actual (x : Point) (h : Space) (t : Time) : responseCurve x h t = response x h t :=
  (congrArg (fun p : Path => p t) (response_integral_equation x h)).symm

theorem original_variational (x : Point) (h : Space) (t : Time) :
    HasDerivAt (responseCurve x h) (derivative (actualPath x t) (response x h t)) (t : ℝ) := by
  have result := (hasDerivAt_pathPrimitive (derivativeOnPath x (response x h)) t).const_add h
  change HasDerivAt (responseCurve x h) (derivativeOnPath x (response x h) t) (t : ℝ) at result
  rw [derivativeOnPath_apply] at result
  exact result

def flowDerivative (x : Point) (t : Time) : Space →L[ℝ] Space := (ContinuousMap.evalCLM ℝ t).comp (response x)

theorem original_flow_strictDerivative (x : Point) (t : Time) :
    HasStrictFDerivAt (fun y => flow y (spatialStep*(t : ℝ))) (flowDerivative x t) x :=
  (ContinuousMap.evalCLM ℝ t).hasStrictFDerivAt.comp _ (actualPath_strictDerivative x)

theorem flowDerivative_zero (x : Point) : flowDerivative x zeroTime = ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro h
  exact response_starts x h

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
