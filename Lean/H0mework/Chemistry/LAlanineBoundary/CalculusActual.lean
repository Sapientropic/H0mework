import H0mework.Chemistry.LAlanineBoundary.CalculusPullback
import H0mework.Chemistry.LAlanineBoundary.SourceModel
import H0mework.Chemistry.LAlanineSignedEvaluator.Field

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary

open SourceGaussianModel SourceFiniteData ContinuousGradient ContinuousParameterMap
noncomputable section
attribute [local irreducible] parameterMap parameterJacobian

theorem chartJacobian_eq_calculus (p : Point) : chartJacobian p = Calculus.jacobian chart p := by
  ext i j
  exact chartJacobian_eq_derivative p i j

theorem calculated_pullback_eq : Calculus.pullback chart sourceGradient = pulledFlux := by
  funext p
  simp only [Calculus.pullback, pulledFlux, ← chartJacobian_eq_calculus]

theorem pulledFlux_contDiff : ContDiff ℝ 1 pulledFlux := by
  rw [← calculated_pullback_eq]
  exact Calculus.pullback_contDiff chart sourceGradient (chart_contDiff 2) (sourceGradient_contDiff 1)

theorem gradient_jacobian_diagonal (x : Point) (i : Fin 3) :
    Calculus.jacobian sourceGradient x i i = sourceHessian x i i := by
  unfold Calculus.jacobian
  rw [(sourceGradient_hasFDerivAt x).fderiv, sourceHessianLinear_apply]
  simp [Calculus.unit, Pi.single_apply]

theorem gradient_jacobian_trace (x : Point) :
    (∑ i : Fin 3, Calculus.jacobian sourceGradient x i i) = laplacian sourceTerms densityMatrix x := by
  simp only [gradient_jacobian_diagonal, SourceSignedField.sourceHessian_diagonal]
  rfl

theorem div_pulledFlux (p : Point) :
    (∑ i : Fin 3, fderiv ℝ pulledFlux p (Pi.single i 1) i) = signedLaplacian 0 4 p := by
  have result := Calculus.div_pullback chart sourceGradient (chart_contDiff 2) (sourceGradient_contDiff 1) p
  rw [calculated_pullback_eq, ← chartJacobian_eq_calculus, gradient_jacobian_trace] at result
  simpa only [Calculus.unit, chart, chartJacobian, signedLaplacian, mul_comm] using result

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
