import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.PartitionIntegral
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! The original source chart and gradient generate the oriented pullback flux. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary

open SourceGaussianModel ContinuousParameterMap ContinuousGradient
noncomputable section
attribute [local irreducible] parameterMap parameterJacobian

def chart : Point → Point := parameterMap 0 4
def chartJacobian (p : Point) : Matrix (Fin 3) (Fin 3) ℝ := jacobianMatrix 0 4 p
def pulledFlux (p : Point) : Point := (chartJacobian p).adjugate.mulVec (sourceGradient (chart p))

theorem chart_hasFDerivAt (p : Point) : HasFDerivAt chart (parameterJacobian 0 4 p) p :=
  parameterMap_hasFDerivAt 0 4 p

theorem chart_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n chart := parameterMap_contDiff 0 4 n

theorem chartJacobian_eq_derivative (p : Point) (i j : Fin 3) :
    chartJacobian p i j = fderiv ℝ chart p (Pi.single j 1) i := by
  simpa only [chartJacobian, jacobianMatrix, chart] using
    congrArg (fun derivative : Point →L[ℝ] Point => derivative (Pi.single j 1) i)
      (parameterJacobian_eq_fderiv 0 4 p)

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
