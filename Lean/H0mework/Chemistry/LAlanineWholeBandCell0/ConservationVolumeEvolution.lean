import H0mework.Chemistry.LAlanineBandCellDifferential.Nondegenerate
import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceVolumeEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient ContinuousSeed TrueFlowDifferential TrueFlowGeometry
open TrueFlowConservation WholeBandActual WholeBandGeometry WholeBandCell0Geometry WholeBandCell0Differential
open WholeBandCell0Continuation WholeCellBoundary
open Matrix Set MeasureTheory
open scoped Matrix
noncomputable section

/-- All three original seed-time columns evolve through the already generated response. -/
def cell0_evolvingJacobian (p : Cell0Point) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => extendPath (cell0_sourceResponse p (cell0_seedFlowDerivative p (Pi.single j 1))) t i

theorem cell0_evolvingJacobian_variational (p : Cell0Point) (s : Time) (i j : Fin 3) :
    HasDerivWithinAt (fun t => cell0_evolvingJacobian p t i j)
      ((hessianMatrix (rawPath (cellSeed 0 p.val) s) * cell0_evolvingJacobian p s) i j)
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) := by
  have derivative := hasDerivWithinAt_pi.mp
    (cell0_sourceResponse_actual_variational p (cell0_seedFlowDerivative p (Pi.single j 1)) s) i
  simpa only [sourceHessianLinear_apply, Matrix.mul_apply, hessianMatrix, cell0_evolvingJacobian,
    extendPath_coe] using derivative

/-- The true source Laplacian controls actual oriented volume along every closed trajectory. -/
theorem cell0_evolvingJacobian_determinant_evolution (p : Cell0Point) (s : Time) :
    HasDerivWithinAt (fun t => (cell0_evolvingJacobian p t).det)
      (laplacian sourceTerms densityMatrix (rawPath (cellSeed 0 p.val) s) * (cell0_evolvingJacobian p s).det)
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) := by
  rw [← sourceHessian_trace]
  exact _root_.LAlanineTrueFlowConservation.determinant_evolution
    (cell0_evolvingJacobian p) (hessianMatrix (rawPath (cellSeed 0 p.val) s)) _ s
    (cell0_evolvingJacobian_variational p s)

theorem cell0_evolvingJacobian_is_actual (p : Cell0Point) :
    cell0_evolvingJacobian p (cell0_actualParameterTime p) = LinearMap.toMatrix' (cell0_trueJacobian p).toLinearMap := by
  ext i j
  rw [cell0_trueJacobian_flow_factorization]
  change extendPath (cell0_sourceResponse p (cell0_seedFlowDerivative p (Pi.single j 1)))
    (cell0_actualParameterTime p : ℝ) i = cell0_sourceResponse p (cell0_seedFlowDerivative p (Pi.single j 1))
    (cell0_actualParameterTime p) i
  rw [extendPath_coe]

theorem cell0_evolvingJacobian_det_is_actual (p : Cell0Point) :
    (cell0_evolvingJacobian p (cell0_actualParameterTime p)).det =
      LinearMap.det (cell0_trueJacobian p).toLinearMap := by
  rw [cell0_evolvingJacobian_is_actual, LinearMap.det_toMatrix']

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
