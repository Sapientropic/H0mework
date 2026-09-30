import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceEquation
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual
open scoped Topology
noncomputable section

def pathResidual (state : Space × Path) : Path :=
  state.2 - pathConst state.1 - volterra (pathGradient state.2)

def volterraHessian (p : BandPoint) : Path →L[ℝ] Path := volterra.comp (pathHessian p)

theorem volterraHessian_norm_lt_one (p : BandPoint) : ‖volterraHessian p‖ < 1 :=
  (norm_volterra_comp_le _ (pathHessian_norm p)).trans_lt actual_volterra_budget

def residualDerivative (p : BandPoint) : Space × Path →L[ℝ] Path :=
  (-pathConst).coprod (1 - volterraHessian p)

theorem pathResidual_hasStrictFDerivAt (p : BandPoint) :
    HasStrictFDerivAt pathResidual (residualDerivative p)
      (ContinuousParameterMap.initialMap 0 4 p.val, actualPath p) := by
  have first := (hasStrictFDerivAt_snd (𝕜 := ℝ)
    (p := (ContinuousParameterMap.initialMap 0 4 p.val, actualPath p))).sub
    (pathConst.hasStrictFDerivAt.comp _ (hasStrictFDerivAt_fst (𝕜 := ℝ)
      (p := (ContinuousParameterMap.initialMap 0 4 p.val, actualPath p))))
  have second := volterra.hasStrictFDerivAt.comp
    (ContinuousParameterMap.initialMap 0 4 p.val, actualPath p)
    ((pathGradient_hasStrictFDerivAt p).comp
      (ContinuousParameterMap.initialMap 0 4 p.val, actualPath p)
      (hasStrictFDerivAt_snd (𝕜 := ℝ)
        (p := (ContinuousParameterMap.initialMap 0 4 p.val, actualPath p))))
  have derivative_eq : residualDerivative p =
      ContinuousLinearMap.snd ℝ Space Path - pathConst.comp (.fst ℝ Space Path) -
        volterra.comp ((pathHessian p).comp (.snd ℝ Space Path)) := by
    apply ContinuousLinearMap.ext
    intro state
    change -pathConst state.1 + (state.2 - volterra (pathHessian p state.2)) =
      state.2 - pathConst state.1 - volterra (pathHessian p state.2)
    abel
  rw [derivative_eq]
  exact first.sub second

theorem pathResidual_right_invertible (p : BandPoint) :
    ((residualDerivative p).comp (.inr ℝ Space Path)).IsInvertible := by
  have inverse : (1 - volterraHessian p).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit (Units.oneSub (volterraHessian p) (volterraHessian_norm_lt_one p)), rfl⟩
  simpa only [residualDerivative, ContinuousLinearMap.coprod_comp_inr] using inverse

def nearbySolution (p : BandPoint) : Space → Path :=
  (pathResidual_hasStrictFDerivAt p).implicitFunctionOfProdDomain (pathResidual_right_invertible p)

theorem nearbySolution_hasStrictFDerivAt (p : BandPoint) :
    HasStrictFDerivAt (nearbySolution p)
      (-((residualDerivative p).comp (.inr ℝ Space Path)).inverse.comp
        ((residualDerivative p).comp (.inl ℝ Space Path)))
      (ContinuousParameterMap.initialMap 0 4 p.val) :=
  (pathResidual_hasStrictFDerivAt p).hasStrictFDerivAt_implicitFunctionOfProdDomain
    (pathResidual_right_invertible p)

theorem actualPath_residual_zero (p : BandPoint) :
    pathResidual (ContinuousParameterMap.initialMap 0 4 p.val, actualPath p) = 0 := by
  change actualPath p - pathConst (ContinuousParameterMap.initialMap 0 4 p.val) -
    volterra (pathGradient (actualPath p)) = 0
  linear_combination actualPath_integral_equation p

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
