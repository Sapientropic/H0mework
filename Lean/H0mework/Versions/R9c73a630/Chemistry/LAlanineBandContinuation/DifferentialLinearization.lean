import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.DifferentialActual
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceLinearization
import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusVolterraOperator

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation TrueFlowDifferential
noncomputable section

def pathHessian (c : FullBandCell) (p : Point) : Path →L[ℝ] Path :=
  pathCompDeriv sourceGradient (sourceGradient_contDiff 1) (rawPath (cellSeed c p))

theorem pathHessian_apply (c : FullBandCell) (p : Point) (η : Path) (t : Time) :
    pathHessian c p η t = sourceHessianLinear (rawPath (cellSeed c p) t) (η t) := by
  rw [pathHessian, pathCompDeriv_apply, (sourceGradient_hasFDerivAt _).fderiv]

theorem pathGradient_hasStrictFDerivAt (c : FullBandCell) (p : Point) :
    HasStrictFDerivAt pathGradient (pathHessian c p) (rawPath (cellSeed c p)) :=
  hasStrictFDerivAt_pathComp sourceGradient (sourceGradient_contDiff 1) _

theorem pathHessian_norm (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ WholeBandGeometry.cellDomain c) :
    ‖pathHessian c p‖ ≤ (17/20 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro η
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg η))).mpr
  intro t
  rw [pathHessian_apply]
  exact ((sourceHessianLinear (rawPath (cellSeed c p) t)).le_opNorm_of_le (η.norm_coe_le_norm t)).trans
    (mul_le_mul_of_nonneg_right (actual_hessian_norm c fields bounds p inside t) (norm_nonneg η))

def volterraHessian (c : FullBandCell) (p : Point) : Path →L[ℝ] Path := volterra.comp (pathHessian c p)

theorem volterraHessian_norm_lt_one (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) : ‖volterraHessian c p‖ < 1 :=
  (norm_volterra_comp_le _ (pathHessian_norm c fields bounds p inside)).trans_lt (by norm_num)

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
