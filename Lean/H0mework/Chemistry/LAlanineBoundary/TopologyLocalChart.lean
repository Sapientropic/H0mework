import H0mework.Chemistry.LAlanineWholeCell.SpatialProducer
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary.Topology

open SourceGaussianModel ContinuousParameterMap WholeCellPartition WholeCellSpatial
open Set
noncomputable section

theorem derivative_kernel (p : Point) (inside : p ∈ fullDomain) :
    (parameterJacobian 0 4 p).ker = ⊥ := by
  by_contra nonzero
  have zero : (parameterJacobian 0 4 p).det = 0 :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mpr nonzero
  rw [SourceChart.linearDet_eq_matrixDet] at zero
  exact (ne_of_gt (sourceGeneratedWholeCellClosure.jacobianPositive p inside)) zero

theorem derivative_range (p : Point) (inside : p ∈ fullDomain) :
    (parameterJacobian 0 4 p).range = ⊤ :=
  LinearMap.range_eq_top.mpr
    ((parameterJacobian 0 4 p).toLinearMap.surjective_of_injective
      (LinearMap.ker_eq_bot.mp (derivative_kernel p inside)))

def derivativeEquiv (p : Point) (inside : p ∈ fullDomain) : Point ≃L[ℝ] Point :=
  ContinuousLinearEquiv.ofBijective (parameterJacobian 0 4 p)
    (derivative_kernel p inside) (derivative_range p inside)

theorem derivativeEquiv_computes (p : Point) (inside : p ∈ fullDomain) :
    (derivativeEquiv p inside : Point →L[ℝ] Point) = parameterJacobian 0 4 p :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

theorem actual_local_homeomorph (p : Point) (inside : p ∈ fullDomain) :
    ∃ e : OpenPartialHomeomorph Point Point,
      (e : Point → Point) = parameterMap 0 4 ∧ p ∈ e.source := by
  have derivative : HasFDerivAt (parameterMap 0 4) (derivativeEquiv p inside : Point →L[ℝ] Point) p := by
    rw [derivativeEquiv_computes]
    exact parameterMap_hasFDerivAt 0 4 p
  let smooth := (parameterMap_contDiff 0 4 1).contDiffAt (x := p)
  exact ⟨smooth.toOpenPartialHomeomorph (parameterMap 0 4) derivative (by norm_num),
    rfl, smooth.mem_toOpenPartialHomeomorph_source derivative (by norm_num)⟩

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary.Topology
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
