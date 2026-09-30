import H0mework.Chemistry.LAlanineWholeBandCell1.ActualGeometry
import H0mework.Chemistry.LAlanineWholeBandCell1.ActualResponse
import H0mework.Chemistry.LAlanineBandContinuation.ParameterNondegenerate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell1Actual

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel WholeBandGeometry WholeBandContinuation WholeBandContinuationDifferential
open WholeBandCell1Differential WholeBandContinuationParameter Set
noncomputable section

theorem cell1_actual_parameter_derivative (p : Cell1Point) :
    HasFDerivWithinAt (sourceParameterMap 1) (trueJacobian 1 p.val) (cellDomain 1) p.val :=
  actualMap_hasFDerivWithinAt 1 cell1_source_fields cell1_analytic_bounds p.val p.property

theorem cell1_actual_jacobian_factorization (p : Cell1Point) :
    trueJacobian 1 p.val = (initialFlowDerivative 1 p.val (actualParameterTime 1 p.val p.property)).comp
      (seedFlowDerivative 1 p.val) :=
  trueJacobian_flow_factorization 1 cell1_source_fields cell1_analytic_bounds p.val p.property

theorem cell1_actual_jacobian_injective (p : Cell1Point) : Function.Injective (trueJacobian 1 p.val) :=
  trueJacobian_injective 1 cell1_source_fields cell1_analytic_bounds cell1_positive_reports p.val p.property

theorem cell1_actual_jacobian_det_ne_zero (p : Cell1Point) :
    LinearMap.det (trueJacobian 1 p.val).toLinearMap ≠ 0 :=
  trueJacobian_det_ne_zero 1 cell1_source_fields cell1_analytic_bounds cell1_positive_reports p.val p.property

theorem cell1_actual_jacobian_eq_fderivWithin (p : Cell1Point) :
    trueJacobian 1 p.val = fderivWithin ℝ (sourceParameterMap 1) (cellDomain 1) p.val :=
  trueJacobian_eq_fderivWithin 1 cell1_source_fields cell1_analytic_bounds p.val p.property

end
end LAlanine40K2025.BasinRefinement.WholeBandCell1Actual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
