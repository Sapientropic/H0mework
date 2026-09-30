import H0mework.Chemistry.LAlanineBandCellDifferential.Bounds
import H0mework.Chemistry.LAlanineWholeBandCell0.ContinuationFull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Differential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceSignedEvaluator ContinuousGradient ContinuousChart TrueTubeTrace
open WholeBandSource WholeBandReplay WholeBandGeometry WholeBandCell0Continuation TrueFlowDifferential
open Set Metric
noncomputable section

theorem cell0_hessian_norm (p : WholeBandActual.Cell0Point) (t : Time) :
    ‖sourceHessianLinear (rawPath (cellSeed 0 p.val) t)‖ ≤ (17/20 : ℝ) := by
  obtain ⟨d, i, _, actual⟩ := cell0_full_field_cover p t.val t.property
  have bound : ‖sourceHessianLinear (rawPath (cellSeed 0 p.val) t)‖ ≤ ((17/20 : ℚ) : ℝ) := by
    apply matrix_norm_le (recordedCallField (tubeCallAt 0 d i)).hessian _ (17/20) (by norm_num)
    · intro axis direction
      rw [hessian_single]
      exact actual.2 axis direction
    · exact (cell0_analytic_bounds d i).1
  simpa only [Rat.cast_div, Rat.cast_ofNat] using bound

theorem tube_margin_real (d : Direction) (i : Step) (axis : Fin 3) :
    sourceCentre axis - sourceRadius + 1/200 < ((tubeBox 0 d i axis).1 : ℝ) ∧
    ((tubeBox 0 d i axis).2 : ℝ) < sourceCentre axis + sourceRadius - 1/200 := by
  have source := (cell0_analytic_bounds d i).2 axis
  dsimp only [sourceCentre, sourceRadius]
  constructor
  · simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt.mpr source.1 :
        ((SourceFiniteData.boxCentre axis - SourceFiniteData.boxRadius + 1/200 : ℚ) : ℝ) <
          ((tubeBox 0 d i axis).1 : ℝ))
  · simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt.mpr source.2 : ((tubeBox 0 d i axis).2 : ℝ) <
        ((SourceFiniteData.boxCentre axis + SourceFiniteData.boxRadius - 1/200 : ℚ) : ℝ))

theorem nearby_tube_inside_cube (d : Direction) (i : Step) (x y : Point)
    (inside : InRectangle (tubeBox 0 d i) x) (nearby : dist y x < (1/200 : ℝ)) : y ∈ sourceCube := by
  change ∀ axis, |y axis - sourceCentre axis| ≤ sourceRadius
  intro axis
  have delta : |y axis - x axis| < (1/200 : ℝ) := by
    have pointwise := norm_le_pi_norm (y-x) axis
    rw [dist_eq_norm] at nearby
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using pointwise.trans_lt nearby
  have lo := (tube_margin_real d i axis).1
  have hi := (tube_margin_real d i axis).2
  have row := inside axis
  have displacement := abs_lt.mp delta
  apply abs_le.mpr
  constructor <;> linarith [row.1, row.2, displacement.1, displacement.2]

theorem path_near_cell0_in_cube (p : WholeBandActual.Cell0Point) (u : Path)
    (nearby : dist u (rawPath (cellSeed 0 p.val)) < (1/200 : ℝ)) (t : Time) : u t ∈ sourceCube := by
  obtain ⟨d, i, inside, _⟩ := cell0_full_field_cover p t.val t.property
  exact nearby_tube_inside_cube d i _ _ inside
    ((ContinuousMap.dist_apply_le_dist t).trans_lt nearby)

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Differential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
