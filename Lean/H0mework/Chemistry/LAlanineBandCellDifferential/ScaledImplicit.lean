import H0mework.Chemistry.LAlanineBandCellDifferential.ScaledLinearization
import H0mework.Chemistry.LAlanineBandCellDifferential.ScaledEquation
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandActual WholeBandGeometry WholeBandCell0Continuation TrueFlowDifferential
noncomputable section

theorem cell0_scaledResidual_hasStrictFDerivAt (p : Cell0Point) :
    HasStrictFDerivAt scaledResidual (cell0_scaledResidualDerivative p)
      (cell0_sourceInput p, cell0_scaledActualPath p) := by
  let center : InitialScale × Path := (cell0_sourceInput p, cell0_scaledActualPath p)
  have initial := (ContinuousLinearMap.fst ℝ Space ℝ).hasStrictFDerivAt.comp center
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := center))
  have scale := (ContinuousLinearMap.snd ℝ Space ℝ).hasStrictFDerivAt.comp center
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := center))
  have first := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := center)).sub
    (pathConst.hasStrictFDerivAt.comp center initial)
  have integral := volterra.hasStrictFDerivAt.comp center
    ((cell0_scaledGradient_hasStrictFDerivAt p).comp center
      (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := center)))
  have generated := first.sub (scale.smul integral)
  have derivative_eq : cell0_scaledResidualDerivative p =
      ContinuousLinearMap.snd ℝ InitialScale Path -
        pathConst.comp ((ContinuousLinearMap.fst ℝ Space ℝ).comp (.fst ℝ InitialScale Path)) -
      (cell0_scaleAt p • volterra.comp ((cell0_scaledHessian p).comp (.snd ℝ InitialScale Path)) +
        ((ContinuousLinearMap.snd ℝ Space ℝ).comp (.fst ℝ InitialScale Path)).smulRight
          (volterra (pathGradient (cell0_scaledActualPath p)))) := by
    apply ContinuousLinearMap.ext
    intro state
    change -pathConst state.1.1 - state.1.2 • volterra (pathGradient (cell0_scaledActualPath p)) +
        (state.2 - cell0_scaleAt p • volterra (cell0_scaledHessian p state.2)) =
      state.2 - pathConst state.1.1 -
        (cell0_scaleAt p • volterra (cell0_scaledHessian p state.2) +
          state.1.2 • volterra (pathGradient (cell0_scaledActualPath p)))
    abel
  rw [derivative_eq]
  exact generated

theorem cell0_scaledResidual_right_invertible (p : Cell0Point) :
    ((cell0_scaledResidualDerivative p).comp (.inr ℝ InitialScale Path)).IsInvertible := by
  have inverse : (1 - cell0_scaledVolterra p).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit (Units.oneSub (cell0_scaledVolterra p) (cell0_scaledVolterra_norm_lt_one p)), rfl⟩
  simpa only [cell0_scaledResidualDerivative, ContinuousLinearMap.coprod_comp_inr] using inverse

def cell0_scaledSolution (p : Cell0Point) : InitialScale → Path :=
  (cell0_scaledResidual_hasStrictFDerivAt p).implicitFunctionOfProdDomain (cell0_scaledResidual_right_invertible p)

def cell0_scaledResponse (p : Cell0Point) : InitialScale →L[ℝ] Path :=
  -((1 - cell0_scaledVolterra p).inverse.comp (cell0_sourceInputDerivative p))

theorem cell0_scaledSolution_hasStrictFDerivAt (p : Cell0Point) :
    HasStrictFDerivAt (cell0_scaledSolution p) (cell0_scaledResponse p) (cell0_sourceInput p) := by
  simpa only [cell0_scaledSolution, cell0_scaledResponse, cell0_scaledResidualDerivative,
    ContinuousLinearMap.coprod_comp_inr, ContinuousLinearMap.coprod_comp_inl] using
    (cell0_scaledResidual_hasStrictFDerivAt p).hasStrictFDerivAt_implicitFunctionOfProdDomain
      (cell0_scaledResidual_right_invertible p)

theorem cell0_scaledActual_residual_zero (p : Cell0Point) :
    scaledResidual (cell0_sourceInput p, cell0_scaledActualPath p) = 0 := by
  change cell0_scaledActualPath p - pathConst (cellSeed 0 p.val) -
    cell0_scaleAt p • volterra (pathGradient (cell0_scaledActualPath p)) = 0
  linear_combination cell0_scaledActualPath_integral_equation p

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
