import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.CellData
import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceCellGeometry

open SourceGaussianModel SourceSignedEvaluator SourceRectangle ContinuousSeed IntervalParameterMap Set MeasureTheory
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Geometry

noncomputable section

def vFirst : ℚ := knotCoordinate 4
def vLast : ℚ := vFirst + (knotCoordinate 5 - vFirst) / 4
def cellLowerQ : Fin 3 → ℚ := ![0, vFirst, 15 / 32]
def cellUpperQ : Fin 3 → ℚ := ![1, vLast, 1 / 2]
def cellLower : Point := fun axis => (cellLowerQ axis : ℝ)
def cellUpper : Point := fun axis => (cellUpperQ axis : ℝ)
def cellDomain : Set Point := Icc cellLower cellUpper
def cellVolume : ℚ := rationalBoxVolume cellLowerQ cellUpperQ

theorem source_parameter_incidence : ∀ axis : Fin 3,
    reportedParameter axis = (cellLowerQ axis, cellUpperQ axis) := by decide +kernel

theorem cell_ordered : ∀ axis : Fin 3, cellLowerQ axis < cellUpperQ axis := by decide +kernel
theorem cell_volume_reported : cellVolume = reportedVolume := by decide +kernel
theorem cellVolume_positive : 0 < cellVolume := by decide +kernel
theorem cell_volume_exact : cellVolume = 1441151880758559 / 18446744073709551616 := by decide +kernel

theorem cellDomain_nonempty : cellDomain.Nonempty :=
  ⟨cellLower, le_rfl, fun axis => Rat.cast_le.mpr (cell_ordered axis).le⟩

theorem cellDomain_volume_toReal : (volume cellDomain).toReal = (cellVolume : ℝ) := by
  change (volume (Icc (fun axis => (cellLowerQ axis : ℝ)) (fun axis => (cellUpperQ axis : ℝ)))).toReal = _
  rw [Real.volume_Icc_pi_toReal (fun axis => Rat.cast_le.mpr (cell_ordered axis).le)]
  simp only [cellVolume, rationalBoxVolume, Rat.cast_prod, Rat.cast_sub]

theorem cell_coordinates (p : Point) (inside : p ∈ cellDomain) :
    p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (vFirst : ℝ) vLast ∧
      p 2 ∈ Icc ((15 : ℝ) / 32) (1 / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [cellLower, cellUpper, cellLowerQ, cellUpperQ] using And.intro (inside.1 0) (inside.2 0)
  · simpa [cellLower, cellUpper, cellLowerQ, cellUpperQ] using And.intro (inside.1 1) (inside.2 1)
  · simpa [cellLower, cellUpper, cellLowerQ, cellUpperQ] using And.intro (inside.1 2) (inside.2 2)

def quarterValue (values : Data.Knot → ℚ) : ℚ := values 4 + (values 5 - values 4) / 4
def curveCorner (values : Data.Knot → ℚ) (side : Fin 2) : ℚ :=
  if side = 0 then values 4 else quarterValue values
def lowerCornerU (side : Fin 2) : ℚ := curveCorner Source.lower side - Source.epsilon 0
def upperCornerU (side : Fin 2) : ℚ := curveCorner Source.upper side + Source.epsilon 0
def widthCorner (side : Fin 2) : ℚ :=
  curveCorner Source.upper side - curveCorner Source.lower side + 2 * Source.epsilon 0
def slopeQ (values : Data.Knot → ℚ) : ℚ :=
  (values 5 - values 4) / (knotCoordinate 5 - knotCoordinate 4)

theorem source_u_corners : ∀ side : Fin 2,
    reportedParameterU.1 ≤ lowerCornerU side ∧ lowerCornerU side ≤ reportedParameterU.2 ∧
    reportedParameterU.1 ≤ upperCornerU side ∧ upperCornerU side ≤ reportedParameterU.2 := by decide +kernel

theorem source_width_corners : ∀ side : Fin 2,
    reportedBandWidth.1 ≤ widthCorner side ∧ widthCorner side ≤ reportedBandWidth.2 := by decide +kernel

theorem source_slope_corners :
    reportedBandSlope.1 ≤ slopeQ Source.lower ∧ slopeQ Source.lower ≤ reportedBandSlope.2 ∧
    reportedBandSlope.1 ≤ slopeQ Source.upper ∧ slopeQ Source.upper ≤ reportedBandSlope.2 := by decide +kernel

theorem source_v_interval : reportedParameterV = (vFirst, vLast) := by decide +kernel

def generatedPositionBox (axis : Fin 3) : Pair :=
  add (add (point (SourceFiniteData.boxCentre axis))
    (mul (point (Source.basis axis 0)) reportedParameterU))
    (mul (point (Source.basis axis 1)) reportedParameterV)

def generatedDerivativeBox (axis direction : Fin 3) : Pair :=
  if direction = 0 then mul (point (Source.basis axis 0)) reportedBandWidth
  else if direction = 1 then add (point (Source.basis axis 1))
    (mul (point (Source.basis axis 0)) reportedBandSlope)
  else point 0

theorem source_position_box : ∀ axis : Fin 3,
    generatedPositionBox axis = actualBox 0 axis := by decide +kernel

theorem source_derivative_box : ∀ axis direction : Fin 3,
    generatedDerivativeBox axis direction = reportedInitialDerivative axis direction := by decide +kernel

theorem holds_lerp (range : Pair) (x y t : ℝ) (hx : Holds range x) (hy : Holds range y)
    (ht : t ∈ Icc (0 : ℝ) 1) : Holds range ((1 - t) * x + t * y) := by
  exact (convex_Icc (𝕜 := ℝ) (range.1 : ℝ) (range.2 : ℝ)) hx hy
    (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem quarter_interpolate (values : Data.Knot → ℚ) (v : ℝ) :
    interpolate values 4 v = (1 - 4 * knotFraction 4 v) * (values 4 : ℝ) +
      (4 * knotFraction 4 v) * (quarterValue values : ℝ) := by
  change (1 - knotFraction 4 v) * (values 4 : ℝ) + knotFraction 4 v * (values 5 : ℝ) = _
  simp only [quarterValue, Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
  ring

theorem quarter_fraction (v : ℝ) (inside : v ∈ Icc (vFirst : ℝ) vLast) :
    4 * knotFraction 4 v ∈ Icc (0 : ℝ) 1 := by
  have width : (0 : ℝ) < (knotCoordinate 5 : ℝ) - knotCoordinate 4 := by
    exact sub_pos.mpr (Rat.cast_lt.mpr (source_knot_geometry.1 4))
  have low : 0 ≤ (v - (knotCoordinate 4 : ℝ)) / ((knotCoordinate 5 : ℝ) - knotCoordinate 4) :=
    div_nonneg (sub_nonneg.mpr inside.1) width.le
  have high : (v - (knotCoordinate 4 : ℝ)) / ((knotCoordinate 5 : ℝ) - knotCoordinate 4) ≤ 1 / 4 := by
    apply (div_le_iff₀ width).mpr
    have endpoint := inside.2
    simp only [vLast, vFirst, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at endpoint
    linarith
  change 0 ≤ 4 * ((v - (knotCoordinate 4 : ℝ)) / ((knotCoordinate 5 : ℝ) - knotCoordinate 4)) ∧
    4 * ((v - (knotCoordinate 4 : ℝ)) / ((knotCoordinate 5 : ℝ) - knotCoordinate 4)) ≤ 1
  constructor <;> linarith

theorem slope_cast (values : Data.Knot → ℚ) : slope values 4 = (slopeQ values : ℝ) := by
  simp only [ContinuousSeed.slope, slopeQ, Rat.cast_div, Rat.cast_sub]
  rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceCellGeometry
