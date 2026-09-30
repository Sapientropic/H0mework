import H0mework.Chemistry.LAlanineContinuousSource.CellBounds
import H0mework.Chemistry.LAlanineParametric.ActualMap
import H0mework.Chemistry.LAlanineParametric.IntervalStage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceCellGeometry

open SourceGaussianModel SourceSignedEvaluator SourceRectangle ContinuousSeed ContinuousParameterMap IntervalParameterMap Set
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Geometry

noncomputable section

theorem lower_curve_in_source_u (v : ℝ) (inside : v ∈ Icc (vFirst : ℝ) vLast) :
    Holds reportedParameterU (interpolate Source.lower 4 v - (Source.epsilon 0 : ℝ)) := by
  have first : Holds reportedParameterU (lowerCornerU 0 : ℝ) := by
    unfold Holds
    exact_mod_cast And.intro (source_u_corners 0).1 (source_u_corners 0).2.1
  have last : Holds reportedParameterU (lowerCornerU 1 : ℝ) := by
    unfold Holds
    exact_mod_cast And.intro (source_u_corners 1).1 (source_u_corners 1).2.1
  have bound := holds_lerp _ _ _ _ first last (quarter_fraction v inside)
  convert bound using 1
  rw [quarter_interpolate]
  simp only [lowerCornerU, curveCorner, ↓reduceIte, one_ne_zero, Rat.cast_sub]
  ring

theorem upper_curve_in_source_u (v : ℝ) (inside : v ∈ Icc (vFirst : ℝ) vLast) :
    Holds reportedParameterU (interpolate Source.upper 4 v + (Source.epsilon 0 : ℝ)) := by
  have first : Holds reportedParameterU (upperCornerU 0 : ℝ) := by
    unfold Holds
    exact_mod_cast And.intro (source_u_corners 0).2.2.1 (source_u_corners 0).2.2.2
  have last : Holds reportedParameterU (upperCornerU 1 : ℝ) := by
    unfold Holds
    exact_mod_cast And.intro (source_u_corners 1).2.2.1 (source_u_corners 1).2.2.2
  have bound := holds_lerp _ _ _ _ first last (quarter_fraction v inside)
  convert bound using 1
  rw [quarter_interpolate]
  simp only [upperCornerU, curveCorner, ↓reduceIte, one_ne_zero, Rat.cast_add]
  ring

theorem bandU_in_source (p : Point) (inside : p ∈ cellDomain) :
    Holds reportedParameterU (bandU 4 (Source.epsilon 0) p) := by
  have coordinates := cell_coordinates p inside
  have bound := holds_lerp _ _ _ _
    (lower_curve_in_source_u (p 1) coordinates.2.1)
    (upper_curve_in_source_u (p 1) coordinates.2.1) coordinates.1
  convert bound using 1
  simp only [bandU, bandWidth]
  ring

theorem bandWidth_in_source (p : Point) (inside : p ∈ cellDomain) :
    Holds reportedBandWidth (bandWidth 4 (Source.epsilon 0) (p 1)) := by
  have first : Holds reportedBandWidth (widthCorner 0 : ℝ) := by
    unfold Holds
    exact_mod_cast source_width_corners 0
  have last : Holds reportedBandWidth (widthCorner 1 : ℝ) := by
    unfold Holds
    exact_mod_cast source_width_corners 1
  have bound := holds_lerp _ _ _ _ first last (quarter_fraction (p 1) (cell_coordinates p inside).2.1)
  convert bound using 1
  rw [bandWidth, quarter_interpolate, quarter_interpolate]
  simp only [widthCorner, curveCorner, ↓reduceIte, one_ne_zero,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  ring

theorem bandSlope_in_source (p : Point) (inside : p ∈ cellDomain) :
    Holds reportedBandSlope (slope Source.lower 4 + p 0 * (slope Source.upper 4 - slope Source.lower 4)) := by
  have first : Holds reportedBandSlope (slopeQ Source.lower : ℝ) := by
    unfold Holds
    exact_mod_cast And.intro source_slope_corners.1 source_slope_corners.2.1
  have last : Holds reportedBandSlope (slopeQ Source.upper : ℝ) := by
    unfold Holds
    exact_mod_cast And.intro source_slope_corners.2.2.1 source_slope_corners.2.2.2
  have bound := holds_lerp _ _ _ _ first last (cell_coordinates p inside).1
  convert bound using 1
  rw [slope_cast, slope_cast]
  ring

theorem cell_initial_position (p : Point) (inside : p ∈ cellDomain) :
    InRectangle (actualBox 0) (bandSeed 4 (Source.epsilon 0) p) := by
  have hu := bandU_in_source p inside
  have hv : Holds reportedParameterV (p 1) := by
    rw [source_v_interval]
    exact (cell_coordinates p inside).2.1
  intro axis
  rw [← source_position_box axis]
  have bound := add_holds _ _ _ _
    (add_holds _ _ _ _ (point_holds (SourceFiniteData.boxCentre axis))
      (mul_holds _ _ _ _ (point_holds (Source.basis axis 0)) hu))
    (mul_holds _ _ _ _ (point_holds (Source.basis axis 1)) hv)
  simpa only [generatedPositionBox, bandSeed, centre, basisVector,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using bound

theorem cell_initial_derivative (p : Point) (inside : p ∈ cellDomain) :
    MatrixHolds reportedInitialDerivative (bandSeedDerivative 4 (Source.epsilon 0) p) := by
  have width := bandWidth_in_source p inside
  have slopeBound := bandSlope_in_source p inside
  intro axis direction
  rw [← source_derivative_box axis direction]
  fin_cases direction
  · have bound := mul_holds _ _ _ _ (point_holds (Source.basis axis 0)) width
    simpa [generatedDerivativeBox, bandSeedDerivative, bandUDerivative, basisVector,
      Pi.single_apply, mul_comm] using bound
  · have bound := add_holds _ _ _ _ (point_holds (Source.basis axis 1))
      (mul_holds _ _ _ _ (point_holds (Source.basis axis 0)) slopeBound)
    simpa [generatedDerivativeBox, bandSeedDerivative, bandUDerivative, basisVector,
      Pi.single_apply, mul_comm, add_comm] using bound
  · simpa [generatedDerivativeBox, bandSeedDerivative, bandUDerivative, basisVector,
      Pi.single_apply] using point_holds 0

theorem source_step_count : stepCount 0 = 4 := by decide +kernel

def stepSizeInterval : Pair := mul (point (1 / (stepCount 0 : ℚ))) (reportedParameter 2)
def stepDerivativeInterval (direction : Fin 3) : Pair :=
  point (if direction = 2 then 1 / (stepCount 0 : ℚ) else 0)

theorem source_step_interval : stepSizeInterval = (15 / 128, 1 / 8) := by decide +kernel
theorem source_step_derivative_interval : ∀ direction : Fin 3,
    stepDerivativeInterval direction = point (if direction = 2 then 1 / 4 else 0) := by decide +kernel

theorem cell_step_size (p : Point) (inside : p ∈ cellDomain) :
    Holds stepSizeInterval (parameterTimeLinear 0 p) := by
  have input : Holds (reportedParameter 2) (p 2) := by
    rw [source_parameter_incidence]
    exact ⟨inside.1 2, inside.2 2⟩
  have bound := mul_holds _ _ _ _ (point_holds (1 / (stepCount 0 : ℚ))) input
  rw [parameterTime_readout]
  simpa only [stepSizeInterval, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    one_div_mul_eq_div] using bound

theorem cell_step_derivative : ∀ direction : Fin 3,
    Holds (stepDerivativeInterval direction) (parameterTimeLinear 0 (Pi.single direction 1)) := by
  intro direction
  rw [source_step_derivative_interval]
  have value : parameterTimeLinear 0 (Pi.single direction 1) =
      ((if direction = 2 then (1 : ℚ) / 4 else 0) : ℝ) := by
    fin_cases direction <;> simp [parameterTimeLinear, source_step_count]
  rw [value]
  simpa only [apply_ite, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero] using
    point_holds (if direction = 2 then (1 : ℚ) / 4 else 0)

def initialJetBox : JetBox := ⟨actualBox 0, reportedInitialDerivative⟩

theorem cell_initial_jet (p : Point) (inside : p ∈ cellDomain) :
    JetHolds initialJetBox (initialMap 0 4 p) (bandSeedDerivative 4 (Source.epsilon 0) p) :=
  ⟨cell_initial_position p inside, cell_initial_derivative p inside⟩

def cellGeometryClosure : Prop :=
  cellDomain.Nonempty ∧ 0 < cellVolume ∧ cellVolume = reportedVolume ∧
    (MeasureTheory.volume cellDomain).toReal = (cellVolume : ℝ) ∧
    type_of% cell_initial_jet ∧ type_of% cell_step_size ∧ type_of% cell_step_derivative

theorem sourceGeneratedCellGeometry : cellGeometryClosure :=
  ⟨cellDomain_nonempty, cellVolume_positive, cell_volume_reported, cellDomain_volume_toReal,
    cell_initial_jet, cell_step_size, cell_step_derivative⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceCellGeometry
