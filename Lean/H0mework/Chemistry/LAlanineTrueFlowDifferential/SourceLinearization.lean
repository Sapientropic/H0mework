import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceActualPath
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusCompositionStrict

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeWholeActual
noncomputable section

def pathGradient : Path → Path := pathComp sourceGradient (sourceGradient_contDiff 1)

def pathHessian (p : BandPoint) : Path →L[ℝ] Path :=
  pathCompDeriv sourceGradient (sourceGradient_contDiff 1) (actualPath p)

theorem pathHessian_apply (p : BandPoint) (η : Path) (t : Time) :
    pathHessian p η t = sourceHessianLinear (actualPath p t) (η t) := by
  rw [pathHessian, pathCompDeriv_apply, (sourceGradient_hasFDerivAt (actualPath p t)).fderiv]

theorem pathGradient_hasStrictFDerivAt (p : BandPoint) :
    HasStrictFDerivAt pathGradient (pathHessian p) (actualPath p) :=
  hasStrictFDerivAt_pathComp sourceGradient (sourceGradient_contDiff 1) (actualPath p)

theorem pathHessian_norm (p : BandPoint) :
    ‖pathHessian p‖ ≤ (TrueTubeHull.lipschitzConstant : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (NNReal.coe_nonneg _)
  intro η
  apply (ContinuousMap.norm_le _ (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg η))).mpr
  intro t
  rw [pathHessian_apply]
  exact ((sourceHessianLinear (actualPath p t)).le_opNorm_of_le (η.norm_coe_le_norm t)).trans
    (mul_le_mul_of_nonneg_right (actualPath_hessian_bound p t) (norm_nonneg η))

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
