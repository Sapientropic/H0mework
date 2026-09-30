import H0mework.Versions.X.NavierStokes.SourcePairing.MotherTransportGreenNormalization

set_option autoImplicit false
open scoped Topology ENNReal BigOperators
namespace SaturationMonoid.NavierStokes.NativeWindowGreenTemporalCoefficient
open MeasureTheory Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCanonicalFluidCoframe NativePhysicalFourier
open NativeCanonicalGreenNormalization
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {nu : Viscosity}

theorem density_dominates (velocity : PhysicalSpace) : ‖velocity‖ ≤ density velocity := by
  dsimp [density]
  nlinarith [sq_nonneg (‖velocity‖-4)]

def pointValue (velocity tangent : PhysicalSpace) : ℂ :=
  ((inner ℝ velocity tangent / (4*density velocity) : ℝ) : ℂ)

theorem point_original (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    pointValue velocity (jet 0) = ((densityJet velocity jet 0 / density velocity : ℝ) : ℂ) := by
  unfold pointValue densityJet
  congr 1
  ring

theorem point_bound (velocity tangent : PhysicalSpace) : ‖pointValue velocity tangent‖ ≤ ‖tangent‖/4 := by
  have positive : 0 < density velocity := by dsimp [density]; positivity
  rw [pointValue, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos (by norm_num) positive)]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) positive)).mpr
  calc
    _ ≤ ‖velocity‖*‖tangent‖ := abs_real_inner_le_norm _ _
    _ ≤ density velocity*‖tangent‖ := mul_le_mul_of_nonneg_right (density_dominates velocity) (norm_nonneg _)
    _ = _ := by ring

def sourceValue (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (point : Torus) : ℂ :=
  pointValue (sourceField seed 0 time point) (sourceField seed 1 time point)

theorem source_measurable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    AEStronglyMeasurable (sourceValue seed time) (volume : Measure Torus) := by
  have first : AEStronglyMeasurable (fun point : Torus => sourceField seed 0 time point) volume :=
    Lp.aestronglyMeasurable (sourceField seed 0 time)
  have last : AEStronglyMeasurable (fun point : Torus => sourceField seed 1 time point) volume :=
    Lp.aestronglyMeasurable (sourceField seed 1 time)
  have scalar : AEStronglyMeasurable (fun point : Torus => inner ℝ (sourceField seed 0 time point)
      (sourceField seed 1 time point) / (4 * (2 + ‖sourceField seed 0 time point‖^2/8))) volume :=
    (first.inner (𝕜 := ℝ) last).div₀
      (aestronglyMeasurable_const.mul (aestronglyMeasurable_const.add
        ((first.norm.pow 2).div₀ aestronglyMeasurable_const)))
  exact Complex.continuous_ofReal.comp_aestronglyMeasurable scalar

theorem source_memLp (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    MemLp (sourceValue seed time) 2 (volume : Measure Torus) := by
  have paid := (Lp.memLp (sourceField seed 1 time)).norm.const_smul (1/4 : ℝ)
  apply paid.mono' (source_measurable seed time)
  filter_upwards with point
  simpa only [sourceValue, Pi.smul_apply, smul_eq_mul, one_div, div_eq_mul_inv, one_mul, mul_comm] using
    point_bound (sourceField seed 0 time point) (sourceField seed 1 time point)

def field (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ScalarField :=
  (source_memLp seed time).toLp (sourceValue seed time)

theorem field_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    field seed time =ᵐ[volume] sourceValue seed time := (source_memLp seed time).coeFn_toLp

theorem field_norm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖field seed time‖ ≤ ‖sourceField seed 1 time‖/4 := by
  have quarter : ‖(1/4 : ℝ)‖ = 1/4 := by norm_num
  have paid : ‖field seed time‖ ≤ ‖(1/4 : ℝ) • sourceField seed 1 time‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [field_ae seed time, Lp.coeFn_smul (1/4 : ℝ) (sourceField seed 1 time)] with point actual scaled
    rw [actual, scaled, Pi.smul_apply, norm_smul, quarter]
    simpa only [sourceValue, one_div, div_eq_mul_inv, one_mul, mul_comm] using
      point_bound (sourceField seed 0 time point) (sourceField seed 1 time point)
  rw [norm_smul, quarter] at paid
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using paid

def coefficients (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ScalarSequence :=
  (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (field seed time)

theorem coefficients_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    coefficients seed time wave = UnitAddTorus.mFourierCoeff (field seed time) wave :=
  UnitAddTorus.mFourierBasis_repr (field seed time) wave

theorem coefficients_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖coefficients seed time‖ ≤ Real.sqrt 3*NativeForwardWindowJets.budget seed 1/4 := by
  rw [coefficients, LinearIsometryEquiv.norm_map]
  exact (field_norm seed time).trans (div_le_div_of_nonneg_right (sourceField_bound seed 1 time) (by norm_num))

theorem source_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (point : Torus)
    (jet : Fin 4 → PhysicalSpace) (actual : jet 0 = sourceField seed 1 time point) :
    sourceValue seed time point =
      ((densityJet (sourceField seed 0 time point) jet 0 / density (sourceField seed 0 time point) : ℝ) : ℂ) := by
  rw [sourceValue, ← actual, point_original]

theorem field_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    field seed (response.2.clockAdvance+time) = field response.1 time := by
  have same (order : ℕ) : sourceField seed order (response.2.clockAdvance+time) = sourceField response.1 order time := by
    simp only [sourceField, NativeForwardWindowEvolution.velocityJet]
    rw [NativeForwardWindowJets.jet_next seed order response generated time nonnegative]
  apply Lp.ext
  filter_upwards [field_ae seed (response.2.clockAdvance+time), field_ae response.1 time] with point first last
  rw [first, last, sourceValue, sourceValue, same 0, same 1]

theorem coefficients_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    coefficients seed (response.2.clockAdvance+time) = coefficients response.1 time := by
  rw [coefficients, coefficients, field_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowGreenTemporalCoefficient
