import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledPath
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual
noncomputable section

abbrev InitialScale := Space × ℝ

def sourceInput (p : BandPoint) : InitialScale :=
  (ContinuousParameterMap.initialMap 0 4 p.val, scaleAt p)

def scaledHessian (p : BandPoint) : Path →L[ℝ] Path :=
  pathCompDeriv sourceGradient (sourceGradient_contDiff 1) (scaledActualPath p)

theorem scaledHessian_apply (p : BandPoint) (η : Path) (t : Time) :
    scaledHessian p η t = sourceHessianLinear (scaledActualPath p t) (η t) := by
  rw [scaledHessian, pathCompDeriv_apply, (sourceGradient_hasFDerivAt (scaledActualPath p t)).fderiv]

theorem scaledGradient_hasStrictFDerivAt (p : BandPoint) :
    HasStrictFDerivAt pathGradient (scaledHessian p) (scaledActualPath p) :=
  hasStrictFDerivAt_pathComp sourceGradient (sourceGradient_contDiff 1) (scaledActualPath p)

theorem scaledHessian_norm (p : BandPoint) :
    ‖scaledHessian p‖ ≤ (TrueTubeHull.lipschitzConstant : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (NNReal.coe_nonneg _)
  intro η
  apply (ContinuousMap.norm_le _ (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg η))).mpr
  intro t
  rw [scaledHessian_apply]
  exact ((sourceHessianLinear (scaledActualPath p t)).le_opNorm_of_le (η.norm_coe_le_norm t)).trans
    (mul_le_mul_of_nonneg_right (scaledActualPath_hessian_bound p t) (norm_nonneg η))

def scaledVolterra (p : BandPoint) : Path →L[ℝ] Path :=
  scaleAt p • volterra.comp (scaledHessian p)

theorem scaledVolterra_norm_lt_one (p : BandPoint) : ‖scaledVolterra p‖ < 1 := by
  have half_nonnegative : (0 : ℝ) ≤ (TrueTubeHull.lipschitzConstant : ℝ) / 2 := by positivity
  calc
    ‖scaledVolterra p‖ ≤ |scaleAt p| * ‖volterra.comp (scaledHessian p)‖ := by
      simpa only [scaledVolterra, Real.norm_eq_abs] using
        ContinuousLinearMap.opNorm_smul_le (scaleAt p) (volterra.comp (scaledHessian p))
    _ ≤ |scaleAt p| * ((TrueTubeHull.lipschitzConstant : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left (norm_volterra_comp_le _ (scaledHessian_norm p)) (abs_nonneg _)
    _ ≤ 1 * ((TrueTubeHull.lipschitzConstant : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right (scaleAt_abs_le_one p) half_nonnegative
    _ < 1 := by simpa only [one_mul] using actual_volterra_budget

def scaledResidual (state : InitialScale × Path) : Path :=
  state.2 - pathConst state.1.1 - state.1.2 • volterra (pathGradient state.2)

def sourceInputDerivative (p : BandPoint) : InitialScale →L[ℝ] Path :=
  (-pathConst).comp (.fst ℝ Space ℝ) -
    (ContinuousLinearMap.snd ℝ Space ℝ).smulRight (volterra (pathGradient (scaledActualPath p)))

def scaledResidualDerivative (p : BandPoint) : InitialScale × Path →L[ℝ] Path :=
  (sourceInputDerivative p).coprod (1 - scaledVolterra p)

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
