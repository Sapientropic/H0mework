import H0mework.Chemistry.LAlanineBandCellDifferential.Actual
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandGeometry WholeBandActual TrueFlowDifferential
noncomputable section

def cell0_pathHessian (p : Cell0Point) : Path →L[ℝ] Path :=
  pathCompDeriv sourceGradient (sourceGradient_contDiff 1) (rawPath (cellSeed 0 p.val))

theorem cell0_pathHessian_apply (p : Cell0Point) (η : Path) (t : Time) :
    cell0_pathHessian p η t = sourceHessianLinear (rawPath (cellSeed 0 p.val) t) (η t) := by
  rw [cell0_pathHessian, pathCompDeriv_apply, (sourceGradient_hasFDerivAt _).fderiv]

theorem cell0_pathGradient_hasStrictFDerivAt (p : Cell0Point) :
    HasStrictFDerivAt pathGradient (cell0_pathHessian p) (rawPath (cellSeed 0 p.val)) :=
  hasStrictFDerivAt_pathComp sourceGradient (sourceGradient_contDiff 1) _

theorem cell0_pathHessian_norm (p : Cell0Point) : ‖cell0_pathHessian p‖ ≤ (17/20 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro η
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg η))).mpr
  intro t
  rw [cell0_pathHessian_apply]
  exact ((sourceHessianLinear (rawPath (cellSeed 0 p.val) t)).le_opNorm_of_le
    (η.norm_coe_le_norm t)).trans
    (mul_le_mul_of_nonneg_right (cell0_hessian_norm p t) (norm_nonneg η))

def cell0_volterraHessian (p : Cell0Point) : Path →L[ℝ] Path :=
  volterra.comp (cell0_pathHessian p)

theorem cell0_volterraHessian_norm_lt_one (p : Cell0Point) : ‖cell0_volterraHessian p‖ < 1 :=
  (norm_volterra_comp_le _ (cell0_pathHessian_norm p)).trans_lt (by norm_num)

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
