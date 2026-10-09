import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.ScaledPath
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledLinearization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandGeometry WholeBandActual TrueFlowDifferential
noncomputable section

def cell0_sourceInput (p : Cell0Point) : InitialScale := (cellSeed 0 p.val, cell0_scaleAt p)

def cell0_scaledHessian (p : Cell0Point) : Path →L[ℝ] Path :=
  pathCompDeriv sourceGradient (sourceGradient_contDiff 1) (cell0_scaledActualPath p)

theorem cell0_scaledHessian_apply (p : Cell0Point) (η : Path) (t : Time) :
    cell0_scaledHessian p η t = sourceHessianLinear (cell0_scaledActualPath p t) (η t) := by
  rw [cell0_scaledHessian, pathCompDeriv_apply,
    (sourceGradient_hasFDerivAt (cell0_scaledActualPath p t)).fderiv]

theorem cell0_scaledGradient_hasStrictFDerivAt (p : Cell0Point) :
    HasStrictFDerivAt pathGradient (cell0_scaledHessian p) (cell0_scaledActualPath p) :=
  hasStrictFDerivAt_pathComp sourceGradient (sourceGradient_contDiff 1) (cell0_scaledActualPath p)

theorem cell0_scaledHessian_norm (p : Cell0Point) : ‖cell0_scaledHessian p‖ ≤ (17/20 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro η
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg η))).mpr
  intro t
  rw [cell0_scaledHessian_apply]
  exact ((sourceHessianLinear (cell0_scaledActualPath p t)).le_opNorm_of_le (η.norm_coe_le_norm t)).trans
    (mul_le_mul_of_nonneg_right (cell0_scaledActualPath_hessian_bound p t) (norm_nonneg η))

def cell0_scaledVolterra (p : Cell0Point) : Path →L[ℝ] Path :=
  cell0_scaleAt p • volterra.comp (cell0_scaledHessian p)

theorem cell0_scaledVolterra_norm_bound (p : Cell0Point) : ‖cell0_scaledVolterra p‖ ≤ (17/40 : ℝ) := by
  calc
    ‖cell0_scaledVolterra p‖ ≤ |cell0_scaleAt p| * ‖volterra.comp (cell0_scaledHessian p)‖ := by
      simpa only [cell0_scaledVolterra, Real.norm_eq_abs] using
        ContinuousLinearMap.opNorm_smul_le (cell0_scaleAt p) (volterra.comp (cell0_scaledHessian p))
    _ ≤ |cell0_scaleAt p| * ((17/20 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left (norm_volterra_comp_le _ (cell0_scaledHessian_norm p)) (abs_nonneg _)
    _ ≤ 1 * ((17/20 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right (cell0_scaleAt_abs_le_one p) (by norm_num)
    _ = _ := by norm_num

theorem cell0_scaledVolterra_norm_lt_one (p : Cell0Point) : ‖cell0_scaledVolterra p‖ < 1 :=
  (cell0_scaledVolterra_norm_bound p).trans_lt (by norm_num)

def cell0_sourceInputDerivative (p : Cell0Point) : InitialScale →L[ℝ] Path :=
  (-pathConst).comp (.fst ℝ Space ℝ) -
    (ContinuousLinearMap.snd ℝ Space ℝ).smulRight (volterra (pathGradient (cell0_scaledActualPath p)))

def cell0_scaledResidualDerivative (p : Cell0Point) : InitialScale × Path →L[ℝ] Path :=
  (cell0_sourceInputDerivative p).coprod (1 - cell0_scaledVolterra p)

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
