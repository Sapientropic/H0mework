import H0mework.Chemistry.LAlanineBandCellDifferential.SeedColumns
import H0mework.Chemistry.LAlanineBandCellDifferential.Injective
import H0mework.Chemistry.LAlanineBandCellDifferential.GradientTransport
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient ContinuousSeed WholeBandGeometry WholeBandActual
open WholeBandCell0Geometry TrueFlowDifferential
noncomputable section

theorem cell0_trueJacobian_flow_factorization (p : Cell0Point) :
    cell0_trueJacobian p = (cell0_initialFlowDerivative p (cell0_actualParameterTime p)).comp
      (cell0_seedFlowDerivative p) := by
  apply ContinuousLinearMap.ext
  intro h
  rw [cell0_trueJacobian_decomposition]
  change cell0_initialFlowDerivative p (cell0_actualParameterTime p)
      (bandSeedDerivative 0 (Geometry.Source.epsilon 0) p.val h) +
        h 2 • sourceGradient (cell0ParameterMap p.val) =
    cell0_initialFlowDerivative p (cell0_actualParameterTime p)
      (bandSeedDerivative 0 (Geometry.Source.epsilon 0) p.val h +
        h 2 • sourceGradient (cellSeed 0 p.val))
  rw [map_add, map_smul, cell0_gradient_transport]
  rfl

theorem cell0_trueJacobian_injective (p : Cell0Point) : Function.Injective (cell0_trueJacobian p) := by
  rw [cell0_trueJacobian_flow_factorization]
  exact (cell0_initialFlowDerivative_injective p (cell0_actualParameterTime p)).comp
    (cell0_seedFlowDerivative_injective p)

def cell0_initialFlowDerivativeEquiv (p : Cell0Point) (s : Time) : Point ≃L[ℝ] Point :=
  (LinearEquiv.ofInjectiveEndo (cell0_initialFlowDerivative p s).toLinearMap
    (cell0_initialFlowDerivative_injective p s)).toContinuousLinearEquiv

@[simp] theorem cell0_initialFlowDerivativeEquiv_coe (p : Cell0Point) (s : Time) :
    (cell0_initialFlowDerivativeEquiv p s : Point →L[ℝ] Point) = cell0_initialFlowDerivative p s := rfl

def cell0_trueJacobianEquiv (p : Cell0Point) : Point ≃L[ℝ] Point :=
  (LinearEquiv.ofInjectiveEndo (cell0_trueJacobian p).toLinearMap
    (cell0_trueJacobian_injective p)).toContinuousLinearEquiv

@[simp] theorem cell0_trueJacobianEquiv_coe (p : Cell0Point) :
    (cell0_trueJacobianEquiv p : Point →L[ℝ] Point) = cell0_trueJacobian p := rfl

theorem cell0_trueJacobian_det_ne_zero (p : Cell0Point) :
    LinearMap.det (cell0_trueJacobian p).toLinearMap ≠ 0 := by
  intro zero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp zero)
    (LinearMap.ker_eq_bot.mpr (cell0_trueJacobian_injective p))

theorem cell0_trueJacobian_eq_fderivWithin (p : Cell0Point) :
    cell0_trueJacobian p = fderivWithin ℝ cell0ParameterMap (cellDomain 0) p.val :=
  ((cell0_actualMap_hasFDerivWithinAt p).fderivWithin (cell0_uniqueDiffWithinAt p)).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
