import H0mework.Chemistry.LAlanineTrueFlowConservation.CalculusDeterminantEvolution
import H0mework.Chemistry.LAlanineTrueFlowGeometry.ResponseNondegenerate
import H0mework.Chemistry.LAlanineSignedEvaluator.Field

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient TrueFlowDifferential
open TrueFlowGeometry TrueTubeWholeActual Matrix Set
open scoped Matrix
noncomputable section

/-- All three original seed-time columns evolve through the already generated response. -/
def evolvingJacobian (p : BandPoint) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => extendPath (sourceResponse p (seedFlowDerivative p (Pi.single j 1))) t i

def hessianMatrix (x : Point) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => sourceHessian x i j

theorem evolvingJacobian_variational (p : BandPoint) (s : Time) (i j : Fin 3) :
    HasDerivWithinAt (fun t => evolvingJacobian p t i j)
      ((hessianMatrix (actualPath p s) * evolvingJacobian p s) i j)
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) := by
  have derivative := hasDerivWithinAt_pi.mp
    (sourceResponse_actual_variational p (seedFlowDerivative p (Pi.single j 1)) s) i
  simpa only [sourceHessianLinear_apply, Matrix.mul_apply, hessianMatrix, evolvingJacobian,
    extendPath_coe] using derivative

theorem sourceHessian_trace (x : Point) :
    (hessianMatrix x).trace = laplacian sourceTerms densityMatrix x := by
  simp only [Matrix.trace, Matrix.diag, hessianMatrix, SourceSignedField.sourceHessian_diagonal]
  rfl

/-- The true source Laplacian controls actual oriented volume along every closed trajectory. -/
theorem evolvingJacobian_determinant_evolution (p : BandPoint) (s : Time) :
    HasDerivWithinAt (fun t => (evolvingJacobian p t).det)
      (laplacian sourceTerms densityMatrix (actualPath p s) * (evolvingJacobian p s).det)
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) := by
  rw [← sourceHessian_trace]
  exact _root_.LAlanineTrueFlowConservation.determinant_evolution
    (evolvingJacobian p) (hessianMatrix (actualPath p s)) _ s
    (evolvingJacobian_variational p s)

theorem evolvingJacobian_is_actual (p : BandPoint) :
    evolvingJacobian p (actualParameterTime p) = LinearMap.toMatrix' (trueJacobian p).toLinearMap := by
  ext i j
  rw [trueJacobian_flow_factorization]
  change extendPath (sourceResponse p (seedFlowDerivative p (Pi.single j 1)))
    (actualParameterTime p : ℝ) i = sourceResponse p (seedFlowDerivative p (Pi.single j 1))
    (actualParameterTime p) i
  rw [extendPath_coe]

theorem evolvingJacobian_det_is_actual (p : BandPoint) :
    (evolvingJacobian p (actualParameterTime p)).det =
      LinearMap.det (trueJacobian p).toLinearMap := by
  rw [evolvingJacobian_is_actual, LinearMap.det_toMatrix']

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
