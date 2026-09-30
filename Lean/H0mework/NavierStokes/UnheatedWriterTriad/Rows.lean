import H0mework.NavierStokes.UnheatedWriterTail.Cubic

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeWholeH1Pairing NativeWholeH1Mixed
open NativeUnheatedPairNegativeKernel NativeUnheatedGlobalNegativeOne NativeUnheatedSourceWeightedTail
open NativeUnheatedIntegralBilinear NativeUnheatedPairGlobalEvolution NativeUnheatedSourceGradient
noncomputable section
variable {nu : Viscosity}

def decode (wave : IntegerWavevector) (coordinate : Coordinate) : State →L[ℝ] ℂ :=
  root wave • ((ContinuousLinearMap.proj coordinate : ComplexCoordinateVector →L[ℝ] ℂ).comp
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp wholeVelocityCLM))

theorem decode_apply (wave : IntegerWavevector) (coordinate : Coordinate) (value : State) :
    decode wave coordinate value = root wave • wholeVelocity value wave coordinate := rfl

theorem decode_inverse (wave : IntegerWavevector) (coordinate : Coordinate) (value : State) :
    decode wave coordinate (inverseGradient value) = wholeVelocity value wave coordinate := by
  rw [decode_apply, inverse_row]
  by_cases zero : wave = 0
  · subst wave; simp [wholeVelocity_zero]
  · exact smul_inv_smul₀ (root_positive wave zero).ne' _

def velocity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (coordinate : Coordinate) : ℂ :=
  decode wave coordinate (state seed time)

def action (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (coordinate : Coordinate) : ℂ :=
  decode wave coordinate (nonlinear seed time)

def derivative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (coordinate : Coordinate) : ℂ :=
  decode wave coordinate (rate seed time)

theorem velocity_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    velocity seed time wave coordinate = wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave coordinate :=
  decode_inverse wave coordinate _

theorem derivative_split_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ wave coordinate,
      derivative seed time wave coordinate = action seed time wave coordinate -
        (nu.coeff * integerWaveViscousMultiplier wave) • velocity seed time wave coordinate := by
  filter_upwards [nonlinear_original_ae seed] with time actual nonnegative wave coordinate
  by_cases zero : wave = 0
  · subst wave; simp [derivative, action, velocity, decode_apply, wholeVelocity_zero]
  · have same := congrArg (fun value : ComplexCoordinateEuclidean => root wave • value coordinate) (actual ⟨wave,zero⟩)
    simp only [if_pos nonnegative, PiLp.add_apply, PiLp.smul_apply, smul_add, smul_smul] at same
    change root wave • nonlinear seed time ⟨wave,zero⟩ coordinate =
      root wave • rate seed time ⟨wave,zero⟩ coordinate +
      (root wave * (nu.coeff * root wave)) • (NativeUnheatedSourceWeightedTail.velocity seed time ⟨wave,zero⟩ coordinate) at same
    have frequency : root wave * (nu.coeff * root wave) = nu.coeff * integerWaveViscousMultiplier wave := by
      rw [mul_left_comm, ← pow_two, root_sq]
    rw [frequency] at same
    simp only [derivative, action, decode_apply, velocity_original,
      wholeVelocity_nonzero _ ⟨wave,zero⟩]
    exact (sub_eq_of_eq_add same).symm

theorem velocity_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (coordinate : Coordinate) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (fun t => velocity seed t wave coordinate) (derivative seed time wave coordinate) time := by
  filter_upwards [source_hasDerivAt_ae seed] with time actual positive
  exact (decode wave coordinate).hasFDerivAt.comp_hasDerivAt time (actual positive)

theorem velocity_ac (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    AbsolutelyContinuousOnInterval (fun t => velocity seed t wave coordinate) a b := by
  apply dominated (state_ac seed a b a0 b0) ‖decode wave coordinate‖
  intro x _ y _
  rw [dist_eq_norm, dist_eq_norm]
  simpa only [map_sub, velocity] using (decode wave coordinate).le_opNorm (state seed x-state seed y)

theorem derivative_integrable (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    IntervalIntegrable (fun time => derivative seed time wave coordinate) volume a b :=
  ⟨(decode wave coordinate).integrable_comp (rate_intervalIntegrable seed a b a0 b0).1,
    (decode wave coordinate).integrable_comp (rate_intervalIntegrable seed a b a0 b0).2⟩

theorem velocity_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    velocity seed (response.2.clockAdvance + time) = velocity response.1 time := by
  funext wave coordinate
  simp only [velocity, state_next seed response generated time nonnegative]

theorem action_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    action seed (response.2.clockAdvance + time) = action response.1 time := by
  have later : 0 ≤ response.2.clockAdvance + time := add_nonneg response.2.clockAdvance_pos.le nonnegative
  have same : physical seed (response.2.clockAdvance + time) later = physical response.1 time nonnegative := by
    apply Subtype.ext
    simp only [physical, NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]
  funext wave coordinate
  by_cases regular : H1 (physical response.1 time nonnegative)
  · have original : H1 (physical seed (response.2.clockAdvance + time) later) := same.symm ▸ regular
    simp only [action, nonlinear, dif_pos later, dif_pos nonnegative, dif_pos original, dif_pos regular, same]
  · have original : ¬ H1 (physical seed (response.2.clockAdvance + time) later) := fun h => regular (same ▸ h)
    simp only [action, nonlinear, dif_pos later, dif_pos nonnegative, dif_neg original, dif_neg regular]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadRows
