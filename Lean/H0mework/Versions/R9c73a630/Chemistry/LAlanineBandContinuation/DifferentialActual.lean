import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.Full
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceSignedEvaluator ContinuousGradient ContinuousChart TrueTubeTrace
open WholeBandSource WholeBandReplay WholeBandGeometry WholeBandContinuation TrueFlowDifferential Set Metric
noncomputable section

abbrev CellBounds (c : FullBandCell) : Prop :=
  ∀ d i, WholeBandCell0Differential.AnalyticBounds (rowInput c d i)

theorem actual_hessian_norm (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (t : Time) :
    ‖sourceHessianLinear (rawPath (cellSeed c p) t)‖ ≤ (17/20 : ℝ) := by
  obtain ⟨d, i, _, actual⟩ := full_field_cover c fields p inside t.val t.property
  have bound : ‖sourceHessianLinear (rawPath (cellSeed c p) t)‖ ≤ ((17/20 : ℚ) : ℝ) := by
    apply matrix_norm_le (recordedCallField (tubeCallAt c d i)).hessian _ (17/20) (by norm_num)
    · intro axis direction
      rw [hessian_single]
      exact actual.2 axis direction
    · exact (bounds d i).1
  simpa only [Rat.cast_div, Rat.cast_ofNat] using bound

theorem tube_margin_real (c : FullBandCell) (bounds : CellBounds c) (d : Direction) (i : Step) (axis : Fin 3) :
    sourceCentre axis - sourceRadius + 1/200 < ((tubeBox c d i axis).1 : ℝ) ∧
    ((tubeBox c d i axis).2 : ℝ) < sourceCentre axis + sourceRadius - 1/200 := by
  have source := (bounds d i).2 axis
  dsimp only [sourceCentre, sourceRadius]
  constructor
  · simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt.mpr source.1 :
        ((SourceFiniteData.boxCentre axis - SourceFiniteData.boxRadius + 1/200 : ℚ) : ℝ) <
          ((tubeBox c d i axis).1 : ℝ))
  · simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt.mpr source.2 : ((tubeBox c d i axis).2 : ℝ) <
        ((SourceFiniteData.boxCentre axis + SourceFiniteData.boxRadius - 1/200 : ℚ) : ℝ))

private theorem nearby_tube_inside_cube (c : FullBandCell) (bounds : CellBounds c)
    (d : Direction) (i : Step) (x y : Point)
    (inside : InRectangle (tubeBox c d i) x) (nearby : dist y x < (1/200 : ℝ)) : y ∈ sourceCube := by
  change ∀ axis, |y axis - sourceCentre axis| ≤ sourceRadius
  intro axis
  have delta : |y axis - x axis| < (1/200 : ℝ) := by
    have pointwise := norm_le_pi_norm (y-x) axis
    rw [dist_eq_norm] at nearby
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using pointwise.trans_lt nearby
  have lo := (tube_margin_real c bounds d i axis).1
  have hi := (tube_margin_real c bounds d i axis).2
  have row := inside axis
  have displacement := abs_lt.mp delta
  apply abs_le.mpr
  constructor <;> linarith [row.1, row.2, displacement.1, displacement.2]

theorem path_near_in_cube (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (bounds : CellBounds c) (p : Point) (inside : p ∈ cellDomain c) (u : Path)
    (nearby : dist u (rawPath (cellSeed c p)) < (1/200 : ℝ)) (t : Time) : u t ∈ sourceCube := by
  obtain ⟨d, i, tube, _⟩ := full_field_cover c fields p inside t.val t.property
  exact nearby_tube_inside_cube c bounds d i _ _ tube ((ContinuousMap.dist_apply_le_dist t).trans_lt nearby)

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuationDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
