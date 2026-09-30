import H0mework.NavierStokes.UnheatedWriterHalf.Carrier
import H0mework.NavierStokes.UnheatedWriterTriad.Rows

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedHalfNonlinear
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeResolventCompactness NativeWholeResolvent NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeWholeH1Pairing
open NativeUnheatedPairNegativeKernel NativeUnheatedSourceWeightedTail NativeUnheatedSourceGradient
noncomputable section
variable {nu : Viscosity}

theorem source_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Summable (fun wave : Wave => ‖quarter wave.1 • nonlinear seed time wave‖^2) := by
  by_cases nonnegative : 0 ≤ time
  · by_cases regular : H1 (physical seed time nonnegative)
    · simpa only [nonlinear, dif_pos nonnegative, dif_pos regular] using
        row_square_summable (physical seed time nonnegative) regular
    · simp [nonlinear, nonnegative, regular]
  · simp [nonlinear, nonnegative]

def source (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : State :=
  ⟨fun wave => quarter wave.1 • nonlinear seed time wave, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using source_summable seed time)⟩

theorem source_row (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : Wave) :
    source seed time wave = quarter wave.1 • nonlinear seed time wave := rfl

theorem source_whole_row (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    wholeVelocity (source seed time) wave = quarter wave • wholeVelocity (nonlinear seed time) wave := by
  by_cases zero : wave = 0
  · simp only [zero, wholeVelocity_zero, smul_zero]
  · funext coordinate
    simp only [wholeVelocity_nonzero _ ⟨wave,zero⟩, source_row, Pi.smul_apply, PiLp.smul_apply]

theorem source_action (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (coordinate : Coordinate) :
    NativeUnheatedTriadRows.action seed time wave coordinate = quarter wave • wholeVelocity (source seed time) wave coordinate := by
  simp only [NativeUnheatedTriadRows.action, NativeUnheatedTriadRows.decode_apply, source_whole_row,
    Pi.smul_apply, smul_smul, ← pow_two, quarter_sq]

def decode (wave : IntegerWavevector) (coordinate : Coordinate) : State →L[ℝ] ℂ :=
  quarter wave • ((ContinuousLinearMap.proj coordinate : ComplexCoordinateVector →L[ℝ] ℂ).comp
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp wholeVelocityCLM))

theorem decode_source (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (coordinate : Coordinate) :
    decode wave coordinate (source seed time) = NativeUnheatedTriadRows.action seed time wave coordinate :=
  (source_action seed time wave coordinate).symm

theorem source_ofPhysical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) : source seed time = ofPhysical (physical seed time nonnegative) regular := by
  apply lp.ext
  funext wave
  simp only [source, ofPhysical, nonlinear, dif_pos nonnegative, dif_pos regular]

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ‖source seed time‖ ≤ coefficient*mass seed time := by
  by_cases nonnegative : 0 ≤ time
  · by_cases regular : H1 (physical seed time nonnegative)
    · rw [source_ofPhysical seed time nonnegative regular]
      simpa only [physical_mass] using ofPhysical_bound (physical seed time nonnegative) regular
    · have zero : source seed time = 0 := by
        apply lp.ext
        funext wave
        simp [source, nonlinear, nonnegative, regular]
      rw [zero, norm_zero]
      exact mul_nonneg coefficient_nonnegative (mass_nonnegative seed time)
  · have zero : source seed time = 0 := by
      apply lp.ext
      funext wave
      simp [source, nonlinear, nonnegative]
    rw [zero, norm_zero]
    exact mul_nonneg coefficient_nonnegative (mass_nonnegative seed time)

theorem source_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (source seed) (volume : Measure ℝ) := by
  have rows (wave : Wave) : AEStronglyMeasurable (fun time => source seed time wave) (volume : Measure ℝ) :=
    ((lp.evalCLM ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.comp_aestronglyMeasurable
      (nonlinear_measurable seed)).const_smul (quarter wave.1)
  let part (observed : Finset Wave) (time : ℝ) : State := ∑ wave ∈ observed, lp.single 2 wave (source seed time wave)
  have partialMeas (observed : Finset Wave) : AEStronglyMeasurable (part observed) (volume : Measure ℝ) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.comp_aestronglyMeasurable (rows wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Wave)) partialMeas
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (source seed time)

theorem source_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (source seed) (volume.restrict (Icc 0 horizon)) :=
  ((mass_integrable seed horizon nonnegative).const_mul coefficient).mono' (source_measurable seed).restrict
    (Eventually.of_forall (source_bound seed))

theorem source_integral_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∫ time in Icc 0 horizon, ‖source seed time‖) ≤
      coefficient*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon := by
  have paid := integral_mono (source_integrable seed horizon nonnegative).norm
    ((mass_integrable seed horizon nonnegative).const_mul coefficient) (source_bound seed)
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (mass_integral_bound seed horizon nonnegative) coefficient_nonnegative)

theorem source_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    source seed (response.2.clockAdvance+time) = source response.1 time := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  have actual := congrFun (congrFun (NativeUnheatedTriadRows.action_next seed response generated time nonnegative) wave.1) coordinate
  rw [source_action, source_action] at actual
  have positive : 0 < quarter wave.1 := Real.sqrt_pos.mpr (root_positive wave.1 wave.2)
  have cancelled := congrArg (fun value : ℂ => (quarter wave.1)⁻¹ • value) actual
  simpa only [inv_smul_smul₀ positive.ne', wholeVelocity_nonzero] using cancelled

end
end SaturationMonoid.NavierStokes.NativeUnheatedHalfNonlinear
