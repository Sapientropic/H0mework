import H0mework.Chemistry.LAlanineTrueFlowGeometry.ResponseGradientTransport
import H0mework.Chemistry.LAlanineTrueFlowGeometry.ResponseInjective
import H0mework.Chemistry.LAlanineTrueFlowGeometry.SeedInjective
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel TrueFlowDifferential TrueTubeWholeActual
noncomputable section

theorem trueJacobian_injective (p : BandPoint) : Function.Injective (trueJacobian p) := by
  rw [trueJacobian_flow_factorization]
  exact (initialFlowDerivative_injective p (actualParameterTime p)).comp
    (seedFlowDerivative_injective p)

def initialFlowDerivativeEquiv (p : BandPoint) (s : Time) : Point ≃L[ℝ] Point :=
  (LinearEquiv.ofInjectiveEndo (initialFlowDerivative p s).toLinearMap
    (initialFlowDerivative_injective p s)).toContinuousLinearEquiv

@[simp] theorem initialFlowDerivativeEquiv_coe (p : BandPoint) (s : Time) :
    (initialFlowDerivativeEquiv p s : Point →L[ℝ] Point) = initialFlowDerivative p s := rfl

def trueJacobianEquiv (p : BandPoint) : Point ≃L[ℝ] Point :=
  (LinearEquiv.ofInjectiveEndo (trueJacobian p).toLinearMap
    (trueJacobian_injective p)).toContinuousLinearEquiv

@[simp] theorem trueJacobianEquiv_coe (p : BandPoint) :
    (trueJacobianEquiv p : Point →L[ℝ] Point) = trueJacobian p := rfl

theorem trueJacobian_det_ne_zero (p : BandPoint) :
    LinearMap.det (trueJacobian p).toLinearMap ≠ 0 := by
  intro zero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp zero)
    (LinearMap.ker_eq_bot.mpr (trueJacobian_injective p))

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
