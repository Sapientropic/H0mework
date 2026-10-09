import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.Actual
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceScaledPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceSignedEvaluator ContinuousGradient WholeBandActual WholeBandGeometry
open WholeBandCell0Continuation TrueFlowDifferential Set Metric
noncomputable section

def cell0_scaleAt (p : Cell0Point) : ℝ := 2 * p.val 2

theorem cell0_scaleAt_abs_le_one (p : Cell0Point) : |cell0_scaleAt p| ≤ 1 := by
  have bounds := p.property.2.2
  unfold cell0_scaleAt
  exact abs_le.mpr ⟨by linarith [bounds.1], by linarith [bounds.2]⟩

def cell0_scaledActualPath (p : Cell0Point) : Path :=
  scaledRawPath (cellSeed 0 p.val) (cell0_scaleAt p)

theorem cell0_scaledActualPath_apply (p : Cell0Point) (t : Time) :
    cell0_scaledActualPath p t = rawPath (cellSeed 0 p.val)
      (scaledTime (cell0_scaleAt p) (cell0_scaleAt_abs_le_one p) t) :=
  extendPath_coe (rawPath (cellSeed 0 p.val)) (scaledTime (cell0_scaleAt p) (cell0_scaleAt_abs_le_one p) t)

theorem cell0_scaledActualPath_starts (p : Cell0Point) :
    cell0_scaledActualPath p zeroTime = cellSeed 0 p.val := scaledRawPath_starts _ _

theorem cell0_scaledActualPath_hessian_bound (p : Cell0Point) (t : Time) :
    ‖sourceHessianLinear (cell0_scaledActualPath p t)‖ ≤ (17/20 : ℝ) := by
  rw [cell0_scaledActualPath_apply]
  exact cell0_hessian_norm p _

theorem path_near_cell0_scaled_in_cube (p : Cell0Point) (u : Path)
    (nearby : dist u (cell0_scaledActualPath p) < (1/200 : ℝ)) (t : Time) : u t ∈ sourceCube := by
  let time := scaledTime (cell0_scaleAt p) (cell0_scaleAt_abs_le_one p) t
  obtain ⟨d, i, inside, _⟩ := cell0_full_field_cover p time.val time.property
  apply nearby_tube_inside_cube d i _ _ inside
  have delta := (ContinuousMap.dist_apply_le_dist t).trans_lt nearby
  rwa [cell0_scaledActualPath_apply] at delta

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
