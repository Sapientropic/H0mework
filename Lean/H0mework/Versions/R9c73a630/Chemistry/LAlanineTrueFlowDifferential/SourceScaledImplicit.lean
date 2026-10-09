import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledLinearization
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledEquation
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual
noncomputable section

theorem scaledResidual_hasStrictFDerivAt (p : BandPoint) :
    HasStrictFDerivAt scaledResidual (scaledResidualDerivative p)
      (sourceInput p, scaledActualPath p) := by
  let center : InitialScale × Path := (sourceInput p, scaledActualPath p)
  have initial := (ContinuousLinearMap.fst ℝ Space ℝ).hasStrictFDerivAt.comp center
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := center))
  have scale := (ContinuousLinearMap.snd ℝ Space ℝ).hasStrictFDerivAt.comp center
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := center))
  have first := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := center)).sub
    (pathConst.hasStrictFDerivAt.comp center initial)
  have integral := volterra.hasStrictFDerivAt.comp center
    ((scaledGradient_hasStrictFDerivAt p).comp center
      (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := center)))
  have generated := first.sub (scale.smul integral)
  have derivative_eq : scaledResidualDerivative p =
      ContinuousLinearMap.snd ℝ InitialScale Path -
        pathConst.comp ((ContinuousLinearMap.fst ℝ Space ℝ).comp (.fst ℝ InitialScale Path)) -
      (scaleAt p • volterra.comp ((scaledHessian p).comp (.snd ℝ InitialScale Path)) +
        ((ContinuousLinearMap.snd ℝ Space ℝ).comp (.fst ℝ InitialScale Path)).smulRight
          (volterra (pathGradient (scaledActualPath p)))) := by
    apply ContinuousLinearMap.ext
    intro state
    change -pathConst state.1.1 - state.1.2 • volterra (pathGradient (scaledActualPath p)) +
        (state.2 - scaleAt p • volterra (scaledHessian p state.2)) =
      state.2 - pathConst state.1.1 -
        (scaleAt p • volterra (scaledHessian p state.2) +
          state.1.2 • volterra (pathGradient (scaledActualPath p)))
    abel
  rw [derivative_eq]
  exact generated

theorem scaledResidual_right_invertible (p : BandPoint) :
    ((scaledResidualDerivative p).comp (.inr ℝ InitialScale Path)).IsInvertible := by
  have inverse : (1 - scaledVolterra p).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit (Units.oneSub (scaledVolterra p) (scaledVolterra_norm_lt_one p)), rfl⟩
  simpa only [scaledResidualDerivative, ContinuousLinearMap.coprod_comp_inr] using inverse

def scaledSolution (p : BandPoint) : InitialScale → Path :=
  (scaledResidual_hasStrictFDerivAt p).implicitFunctionOfProdDomain (scaledResidual_right_invertible p)

def scaledResponse (p : BandPoint) : InitialScale →L[ℝ] Path :=
  -((1 - scaledVolterra p).inverse.comp (sourceInputDerivative p))

theorem scaledSolution_hasStrictFDerivAt (p : BandPoint) :
    HasStrictFDerivAt (scaledSolution p) (scaledResponse p) (sourceInput p) := by
  simpa only [scaledSolution, scaledResponse, scaledResidualDerivative,
    ContinuousLinearMap.coprod_comp_inr, ContinuousLinearMap.coprod_comp_inl] using
    (scaledResidual_hasStrictFDerivAt p).hasStrictFDerivAt_implicitFunctionOfProdDomain
      (scaledResidual_right_invertible p)

theorem scaledActual_residual_zero (p : BandPoint) :
    scaledResidual (sourceInput p, scaledActualPath p) = 0 := by
  change scaledActualPath p - pathConst (ContinuousParameterMap.initialMap 0 4 p.val) -
    scaleAt p • volterra (pathGradient (scaledActualPath p)) = 0
  linear_combination scaledActualPath_integral_equation p

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
