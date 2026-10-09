import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell1.ActualFull
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.DifferentialInjective
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.DifferentialGradientTransport
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell1.DifferentialBounds

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell1Actual

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel WholeBandGeometry WholeBandContinuationDifferential WholeBandCell1Differential
open TrueFlowDifferential ContinuousGradient
noncomputable section

theorem cell1_actual_initial_response (p : Cell1Point) :
    HasStrictFDerivAt rawPath (sourceResponse 1 p.val) (cellSeed 1 p.val) :=
  rawPath_hasStrictFDerivAt 1 cell1_source_fields cell1_analytic_bounds p.val p.property

theorem cell1_actual_initial_derivative (p : Cell1Point) (s : Time) :
    HasStrictFDerivAt (fun x => rawPath x s) (initialFlowDerivative 1 p.val s) (cellSeed 1 p.val) :=
  initialFlow_hasStrictFDerivAt 1 cell1_source_fields cell1_analytic_bounds p.val p.property s

theorem cell1_response_initial_identity (p : Cell1Point) :
    initialFlowDerivative 1 p.val zeroTime = ContinuousLinearMap.id ℝ Space :=
  initialFlowDerivative_zero 1 cell1_source_fields cell1_analytic_bounds p.val p.property

theorem cell1_response_injective (p : Cell1Point) (s : Time) :
    Function.Injective (initialFlowDerivative 1 p.val s) :=
  initialFlowDerivative_injective 1 cell1_source_fields cell1_analytic_bounds p.val p.property s

theorem cell1_gradient_transport (p : Cell1Point) (s : Time) :
    initialFlowDerivative 1 p.val s (sourceGradient (cellSeed 1 p.val)) =
      sourceGradient (rawPath (cellSeed 1 p.val) s) :=
  gradient_transport 1 cell1_source_fields cell1_analytic_bounds p.val p.property s

end
end LAlanine40K2025.BasinRefinement.WholeBandCell1Actual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
