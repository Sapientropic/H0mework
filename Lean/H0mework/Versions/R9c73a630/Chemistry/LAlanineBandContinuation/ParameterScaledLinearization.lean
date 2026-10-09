import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ParameterScaledPath
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledLinearization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationDifferential TrueFlowDifferential
noncomputable section

def sourceInput (c : FullBandCell) (p : Point) : InitialScale := (cellSeed c p, scaleAt p)

def scaledHessian (c : FullBandCell) (p : Point) : Path →L[ℝ] Path :=
  pathCompDeriv sourceGradient (sourceGradient_contDiff 1) (scaledActualPath c p)

theorem scaledHessian_apply (c : FullBandCell) (p : Point) (η : Path) (t : Time) :
    scaledHessian c p η t = sourceHessianLinear (scaledActualPath c p t) (η t) := by
  rw [scaledHessian, pathCompDeriv_apply, (sourceGradient_hasFDerivAt (scaledActualPath c p t)).fderiv]

theorem scaledGradient_hasStrictFDerivAt (c : FullBandCell) (p : Point) :
    HasStrictFDerivAt pathGradient (scaledHessian c p) (scaledActualPath c p) :=
  hasStrictFDerivAt_pathComp sourceGradient (sourceGradient_contDiff 1) (scaledActualPath c p)

theorem scaledHessian_norm (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) : ‖scaledHessian c p‖ ≤ (17/20 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro η
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg η))).mpr
  intro t
  rw [scaledHessian_apply]
  exact ((sourceHessianLinear (scaledActualPath c p t)).le_opNorm_of_le (η.norm_coe_le_norm t)).trans
    (mul_le_mul_of_nonneg_right (scaledActualPath_hessian_bound c fields bounds p inside t) (norm_nonneg η))

def scaledVolterra (c : FullBandCell) (p : Point) : Path →L[ℝ] Path :=
  scaleAt p • volterra.comp (scaledHessian c p)

theorem scaledVolterra_norm_bound (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) : ‖scaledVolterra c p‖ ≤ (17/40 : ℝ) := by
  calc
    ‖scaledVolterra c p‖ ≤ |scaleAt p| * ‖volterra.comp (scaledHessian c p)‖ := by
      simpa only [scaledVolterra, Real.norm_eq_abs] using
        ContinuousLinearMap.opNorm_smul_le (scaleAt p) (volterra.comp (scaledHessian c p))
    _ ≤ |scaleAt p| * ((17/20 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left (norm_volterra_comp_le _ (scaledHessian_norm c fields bounds p inside)) (abs_nonneg _)
    _ ≤ 1 * ((17/20 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right (scaleAt_abs_le_one c p inside) (by norm_num)
    _ = _ := by norm_num

theorem scaledVolterra_norm_lt_one (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) : ‖scaledVolterra c p‖ < 1 :=
  (scaledVolterra_norm_bound c fields bounds p inside).trans_lt (by norm_num)

def sourceInputDerivative (c : FullBandCell) (p : Point) : InitialScale →L[ℝ] Path :=
  (-pathConst).comp (.fst ℝ Space ℝ) -
    (ContinuousLinearMap.snd ℝ Space ℝ).smulRight (volterra (pathGradient (scaledActualPath c p)))

def scaledResidualDerivative (c : FullBandCell) (p : Point) : InitialScale × Path →L[ℝ] Path :=
  (sourceInputDerivative c p).coprod (1 - scaledVolterra c p)

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
