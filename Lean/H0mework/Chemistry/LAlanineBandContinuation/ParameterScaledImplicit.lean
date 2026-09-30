import H0mework.Chemistry.LAlanineBandContinuation.ParameterScaledLinearization
import H0mework.Chemistry.LAlanineBandContinuation.ParameterScaledEquation
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationDifferential TrueFlowDifferential
noncomputable section

theorem scaledResidual_hasStrictFDerivAt (c : FullBandCell) (p : Point) :
    HasStrictFDerivAt scaledResidual (scaledResidualDerivative c p)
      (sourceInput c p, scaledActualPath c p) := by
  let center : InitialScale × Path := (sourceInput c p, scaledActualPath c p)
  have initial := (ContinuousLinearMap.fst ℝ Space ℝ).hasStrictFDerivAt.comp center
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := center))
  have scale := (ContinuousLinearMap.snd ℝ Space ℝ).hasStrictFDerivAt.comp center
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := center))
  have first := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := center)).sub
    (pathConst.hasStrictFDerivAt.comp center initial)
  have integral := volterra.hasStrictFDerivAt.comp center
    ((scaledGradient_hasStrictFDerivAt c p).comp center
      (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := center)))
  have generated := first.sub (scale.smul integral)
  have derivative_eq : scaledResidualDerivative c p =
      ContinuousLinearMap.snd ℝ InitialScale Path -
        pathConst.comp ((ContinuousLinearMap.fst ℝ Space ℝ).comp (.fst ℝ InitialScale Path)) -
      (scaleAt p • volterra.comp ((scaledHessian c p).comp (.snd ℝ InitialScale Path)) +
        ((ContinuousLinearMap.snd ℝ Space ℝ).comp (.fst ℝ InitialScale Path)).smulRight
          (volterra (pathGradient (scaledActualPath c p)))) := by
    apply ContinuousLinearMap.ext
    intro state
    change -pathConst state.1.1 - state.1.2 • volterra (pathGradient (scaledActualPath c p)) +
        (state.2 - scaleAt p • volterra (scaledHessian c p state.2)) =
      state.2 - pathConst state.1.1 -
        (scaleAt p • volterra (scaledHessian c p state.2) +
          state.1.2 • volterra (pathGradient (scaledActualPath c p)))
    abel
  rw [derivative_eq]
  exact generated

theorem scaledResidual_right_invertible (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    ((scaledResidualDerivative c p).comp (.inr ℝ InitialScale Path)).IsInvertible := by
  have inverse : (1 - scaledVolterra c p).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit
      (Units.oneSub (scaledVolterra c p) (scaledVolterra_norm_lt_one c fields bounds p inside)), rfl⟩
  simpa only [scaledResidualDerivative, ContinuousLinearMap.coprod_comp_inr] using inverse

def scaledSolution (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) : InitialScale → Path :=
  (scaledResidual_hasStrictFDerivAt c p).implicitFunctionOfProdDomain
    (scaledResidual_right_invertible c fields bounds p inside)

def scaledResponse (c : FullBandCell) (p : Point) : InitialScale →L[ℝ] Path :=
  -((1 - scaledVolterra c p).inverse.comp (sourceInputDerivative c p))

theorem scaledSolution_hasStrictFDerivAt (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    HasStrictFDerivAt (scaledSolution c fields bounds p inside) (scaledResponse c p) (sourceInput c p) := by
  simpa only [scaledSolution, scaledResponse, scaledResidualDerivative,
    ContinuousLinearMap.coprod_comp_inr, ContinuousLinearMap.coprod_comp_inl] using
    (scaledResidual_hasStrictFDerivAt c p).hasStrictFDerivAt_implicitFunctionOfProdDomain
      (scaledResidual_right_invertible c fields bounds p inside)

theorem scaledActual_residual_zero (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) :
    scaledResidual (sourceInput c p, scaledActualPath c p) = 0 := by
  change scaledActualPath c p - pathConst (cellSeed c p) -
    scaleAt p • volterra (pathGradient (scaledActualPath c p)) = 0
  linear_combination scaledActualPath_integral_equation c fields p inside

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
