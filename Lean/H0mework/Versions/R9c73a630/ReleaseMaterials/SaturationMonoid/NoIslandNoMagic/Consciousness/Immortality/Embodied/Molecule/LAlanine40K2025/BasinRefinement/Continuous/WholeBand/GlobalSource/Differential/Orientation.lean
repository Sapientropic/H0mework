import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Matrix
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.Inverse
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource.Differential
open SourceGaussianModel Set
open _root_.LAlanineTrueFlowDifferential
noncomputable section

theorem response_determinant_nonzero (x : Point) (t : Time) : (responseMatrix x t).det ≠ 0 := by
  rw [responseMatrix_actual,LinearMap.det_toMatrix']
  intro zero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp zero)
    (LinearMap.ker_eq_bot.mpr (flowDerivative_injective x t))

theorem responseMatrix_continuous (x : Point) : Continuous (responseMatrix x) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have curve : Continuous (responseCurve x (Pi.single j 1)) :=
    continuous_const.add (continuous_pathPrimitive (derivativeOnPath x (response x (Pi.single j 1))))
  exact (continuous_apply i).comp curve

theorem response_determinant_positive (x : Point) (t : Time) : 0 < (responseMatrix x t).det := by
  have initial : 0 < (responseMatrix x 0).det := by rw [responseMatrix_starts,Matrix.det_one]; norm_num
  by_contra failed
  have zero_mem : (0 : ℝ) ∈ Icc (-(1/2) : ℝ) (1/2) := by constructor <;> norm_num
  obtain ⟨u,hu,vanished⟩ :=
    isPreconnected_Icc.intermediate_value t.property zero_mem (responseMatrix_continuous x).matrix_det.continuousOn
      ⟨le_of_not_gt failed,initial.le⟩
  exact response_determinant_nonzero x ⟨u,hu⟩ vanished

theorem actual_determinant_positive (x : Point) (t : Time) : 0 < (flowDerivative x t).det := by
  change 0 < LinearMap.det (flowDerivative x t).toLinearMap
  rw [← LinearMap.det_toMatrix',(responseMatrix_actual x t).symm]
  exact response_determinant_positive x t

end
end LAlanine40K2025.BasinRefinement.GlobalSource.Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
