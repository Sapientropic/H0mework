import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ParameterColumns
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.DifferentialInjective
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.DifferentialGradientTransport
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandSource WholeBandGeometry
open TrueFlowDifferential WholeBandContinuation WholeBandContinuationDifferential Set
noncomputable section

theorem trueJacobian_flow_factorization (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    trueJacobian c p = (initialFlowDerivative c p (actualParameterTime c p inside)).comp
      (seedFlowDerivative c p) := by
  apply ContinuousLinearMap.ext
  intro h
  rw [trueJacobian_decomposition c fields bounds p inside]
  change initialFlowDerivative c p (actualParameterTime c p inside)
      (bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) p h) +
        h 2 • sourceGradient (sourceParameterMap c p) =
    initialFlowDerivative c p (actualParameterTime c p inside)
      (bandSeedDerivative (cellSegment c) (Geometry.Source.epsilon 0) p h +
        h 2 • sourceGradient (cellSeed c p))
  rw [map_add, map_smul, gradient_transport c fields bounds p inside]
  rfl

theorem trueJacobian_injective (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) :
    Function.Injective (trueJacobian c p) := by
  rw [trueJacobian_flow_factorization c fields bounds p inside]
  exact (initialFlowDerivative_injective c fields bounds p inside (actualParameterTime c p inside)).comp
    (seedFlowDerivative_injective c fields positive p inside)

theorem trueJacobian_det_ne_zero (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) :
    LinearMap.det (trueJacobian c p).toLinearMap ≠ 0 := by
  intro zero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp zero)
    (LinearMap.ker_eq_bot.mpr (trueJacobian_injective c fields bounds positive p inside))

def trueJacobianEquiv (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) :
    Point ≃L[ℝ] Point :=
  (LinearEquiv.ofInjectiveEndo (trueJacobian c p).toLinearMap
    (trueJacobian_injective c fields bounds positive p inside)).toContinuousLinearEquiv

@[simp] theorem trueJacobianEquiv_coe (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (positive : PositiveNormalReports c) (p : Point) (inside : p ∈ cellDomain c) :
    (trueJacobianEquiv c fields bounds positive p inside : Point →L[ℝ] Point) = trueJacobian c p := rfl

theorem trueJacobian_eq_fderivWithin (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) :
    trueJacobian c p = fderivWithin ℝ (sourceParameterMap c) (cellDomain c) p :=
  ((actualMap_hasFDerivWithinAt c fields bounds p inside).fderivWithin (uniqueDiffWithinAt c p inside)).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
