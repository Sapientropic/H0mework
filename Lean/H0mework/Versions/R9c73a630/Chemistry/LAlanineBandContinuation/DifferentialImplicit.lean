import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.DifferentialEquation
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.Implicit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation TrueFlowDifferential
noncomputable section

def residualDerivative (c : FullBandCell) (p : Point) : Space × Path →L[ℝ] Path :=
  (-pathConst).coprod (1 - volterraHessian c p)

theorem residual_strictDerivative (c : FullBandCell) (p : Point) :
    HasStrictFDerivAt pathResidual (residualDerivative c p) (cellSeed c p, rawPath (cellSeed c p)) :=
  WholeBandCell0Differential.pathResidual_hasStrictFDerivAt_on_path _ _

theorem residual_right_invertible (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    ((residualDerivative c p).comp (.inr ℝ Space Path)).IsInvertible := by
  have inverse : (1 - volterraHessian c p).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit
      (Units.oneSub (volterraHessian c p) (volterraHessian_norm_lt_one c fields bounds p inside)), rfl⟩
  simpa only [residualDerivative, ContinuousLinearMap.coprod_comp_inr] using inverse

def nearbySolution (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) : Space → Path :=
  (residual_strictDerivative c p).implicitFunctionOfProdDomain (residual_right_invertible c fields bounds p inside)

theorem nearbySolution_hasStrictFDerivAt (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    HasStrictFDerivAt (nearbySolution c fields bounds p inside)
      (-((residualDerivative c p).comp (.inr ℝ Space Path)).inverse.comp
        ((residualDerivative c p).comp (.inl ℝ Space Path))) (cellSeed c p) :=
  (residual_strictDerivative c p).hasStrictFDerivAt_implicitFunctionOfProdDomain
    (residual_right_invertible c fields bounds p inside)

theorem rawPath_residual_zero (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) : pathResidual (cellSeed c p, rawPath (cellSeed c p)) = 0 := by
  change rawPath (cellSeed c p) - pathConst (cellSeed c p) - volterra (pathGradient (rawPath (cellSeed c p))) = 0
  linear_combination rawPath_integral_equation c fields p inside

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
