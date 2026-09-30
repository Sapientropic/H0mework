import H0mework.Chemistry.LAlanineBandContinuation.DifferentialActual
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceScaledPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationDifferential TrueFlowDifferential Set Metric
noncomputable section

def scaleAt (p : Point) : ℝ := 2 * p 2

theorem scaleAt_abs_le_one (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) :
    |scaleAt p| ≤ 1 := by
  unfold scaleAt
  exact abs_le.mpr ⟨by linarith [inside.2.2.1], by linarith [inside.2.2.2]⟩

def scaledActualPath (c : FullBandCell) (p : Point) : Path :=
  scaledRawPath (cellSeed c p) (scaleAt p)

theorem scaledActualPath_apply (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) (t : Time) :
    scaledActualPath c p t = rawPath (cellSeed c p)
      (scaledTime (scaleAt p) (scaleAt_abs_le_one c p inside) t) :=
  extendPath_coe (rawPath (cellSeed c p)) (scaledTime (scaleAt p) (scaleAt_abs_le_one c p inside) t)

theorem scaledActualPath_starts (c : FullBandCell) (p : Point) :
    scaledActualPath c p zeroTime = cellSeed c p := scaledRawPath_starts _ _

theorem scaledActualPath_hessian_bound (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (t : Time) :
    ‖sourceHessianLinear (scaledActualPath c p t)‖ ≤ (17/20 : ℝ) := by
  rw [scaledActualPath_apply c p inside]
  exact actual_hessian_norm c fields bounds p inside _

theorem path_near_scaled_in_cube (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (u : Path)
    (nearby : dist u (scaledActualPath c p) < (1/200 : ℝ)) (t : Time) : u t ∈ sourceCube := by
  let time := scaledTime (scaleAt p) (scaleAt_abs_le_one c p inside) t
  obtain ⟨d, i, tube, _⟩ := full_field_cover c fields p inside time.val time.property
  change SourceSignedEvaluator.InRectangle (tubeBox c d i) (rawPath (cellSeed c p) time) at tube
  have delta : dist (u t) (rawPath (cellSeed c p) time) < (1/200 : ℝ) := by
    have pointwise := (ContinuousMap.dist_apply_le_dist t).trans_lt nearby
    rwa [scaledActualPath_apply c p inside] at pointwise
  change ∀ axis, |u t axis - sourceCentre axis| ≤ sourceRadius
  intro axis
  have displacement : |u t axis - rawPath (cellSeed c p) time axis| < (1/200 : ℝ) := by
    have pointwise := norm_le_pi_norm (u t - rawPath (cellSeed c p) time) axis
    rw [dist_eq_norm] at delta
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using pointwise.trans_lt delta
  have lo := (tube_margin_real c bounds d i axis).1
  have hi := (tube_margin_real c bounds d i axis).2
  have row := tube axis
  have distance := abs_lt.mp displacement
  apply abs_le.mpr
  constructor <;> linarith [row.1, row.2, distance.1, distance.2]

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationParameter
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
