import H0mework.Versions.X.NavierStokes.UnifiedAction.UnifiedCompleteSource
import H0mework.Versions.X.NavierStokes.GlobalAction.GlobalPhysicalAction
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedGlobalDuhamel

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open NativeEndpointVelocityCarrier NativeTimeJetCarrier

noncomputable section

variable {nu : Viscosity}

def velocity (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (time : ℝ) : ComplexCoordinateVector :=
  wholeVelocity (NativeAbsoluteEventualControl.velocity seed time) wave

def forcing (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (time : ℝ) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (NativeUnifiedGlobalStressSource.stress seed time wave)

def damping (nu : Viscosity) (wave : IntegerWavevector) : ℝ := nu.coeff * integerWaveViscousMultiplier wave

def rate (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (time : ℝ) : ComplexCoordinateVector :=
  forcing seed wave time - damping nu wave • velocity seed wave time

def rowRead (wave : NonzeroIntegerWavevector) : WholeRestartVelocityEndpointState →L[ℝ] ComplexCoordinateVector :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℂ)).toContinuousLinearMap.comp
    (integerWaveNormSq wave.1 ^ 2 • lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave)

theorem rowRead_source (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) (time : ℝ) :
    rowRead wave (NativeGlobalHilbertAction.sourceState seed time) = velocity seed wave.1 time := by
  change (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℂ))
    (integerWaveNormSq wave.1 ^ 2 • NativeNegativeFourMomentum.embed (NativeAbsoluteEventualControl.velocity seed time) wave) = _
  rw [NativeNegativeFourMomentum.embed_reconstruct]
  funext coordinate
  exact (wholeVelocity_nonzero _ wave coordinate).symm

theorem rowRead_action (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) (time : ℝ) :
    rowRead wave (NativeUnifiedGlobalActionFeed.action seed time) = rate seed wave.1 time := by
  change (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℂ))
    (integerWaveNormSq wave.1 ^ 2 • NativeUnifiedGlobalActionFeed.action seed time wave) = _
  rw [NativeUnifiedGlobalStressSource.source_momentum]
  change integerWaveNormSq wave.1 ^ 2 • (NativeNegativeFourMomentum.weight wave.1 •
    (projectedDivergenceCLM wave.1 ((NativeUnifiedGlobalStressSource.source seed time).2 wave.1) -
      (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity (NativeUnifiedGlobalStressSource.source seed time).1 wave.1)) = _
  rw [smul_smul, NativeNegativeFourMomentum.weight, ← mul_pow,
    mul_inv_cancel₀ (integerWaveNormSq_pos wave.2).ne', one_pow, one_smul,
    NativeUnifiedGlobalStressSource.source_velocity]
  rfl

theorem rate_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) :
    IntervalIntegrable (rate seed wave.1) volume a b := by
  have original := (NativeUnifiedGlobalActionFeed.action_intervalIntegrable seed a a_nonnegative).symm.trans
    (NativeUnifiedGlobalActionFeed.action_intervalIntegrable seed b b_nonnegative)
  have projected : IntervalIntegrable (fun time => rowRead wave (NativeUnifiedGlobalActionFeed.action seed time)) volume a b :=
    ⟨(rowRead wave).integrable_comp original.1, (rowRead wave).integrable_comp original.2⟩
  simpa only [rowRead_action] using projected

theorem velocity_derivative_ae (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (velocity seed wave.1) (rate seed wave.1 time) time := by
  filter_upwards [NativeUnifiedGlobalActionFeed.source_hasDerivAt_ae seed] with time evolves
  intro positive
  have projected := (rowRead wave).hasFDerivAt.comp_hasDerivAt time (evolves positive)
  simpa only [Function.comp_def, rowRead_source, rowRead_action] using projected

theorem velocity_absolutelyContinuous (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    AbsolutelyContinuousOnInterval (velocity seed wave.1) a b := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  apply LipschitzOnWith.of_dist_le'
  intro first firstInside last lastInside
  rw [uIcc_of_le ordered] at firstInside lastInside
  rw [← rowRead_source seed wave first, ← rowRead_source seed wave last]
  calc
    _ ≤ ‖rowRead wave‖ * dist (NativeGlobalHilbertAction.sourceState seed first)
        (NativeGlobalHilbertAction.sourceState seed last) := (rowRead wave).lipschitz.dist_le_mul _ _
    _ ≤ ‖rowRead wave‖ * (NativeGlobalHilbertAction.sourceBudget seed * |first - last|) :=
      mul_le_mul_of_nonneg_left
        (NativeGlobalHilbertAction.sourceState_dist_le seed last first (a_nonnegative.trans lastInside.1)
          (a_nonnegative.trans firstInside.1)) (norm_nonneg _)
    _ = (‖rowRead wave‖ * NativeGlobalHilbertAction.sourceBudget seed) * dist first last := by
      rw [Real.dist_eq]
      ring

theorem forcing_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    IntervalIntegrable (forcing seed wave.1) volume a b := by
  have path : IntervalIntegrable (velocity seed wave.1) volume a b :=
    (velocity_absolutelyContinuous seed wave a b a_nonnegative ordered).continuousOn.intervalIntegrable
  have sum := (rate_integrable seed wave a b a_nonnegative (a_nonnegative.trans ordered)).add
    (path.smul (damping nu wave.1))
  simpa only [rate, Pi.smul_apply, sub_add_cancel] using sum

open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport

theorem source_eq_heatDuhamel (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    velocity seed wave.1 b = heatDuhamelComplexCoordinatePath (velocity seed wave.1 a)
      (forcing seed wave.1) (damping nu wave.1) a b := by
  let factor (time : ℝ) := Real.exp (damping nu wave.1 * (time - a))
  have factorDerivative (time : ℝ) : HasDerivAt factor (factor time * damping nu wave.1) time := by
    simpa only [factor, id_eq, mul_one] using (((hasDerivAt_id time).sub_const a).const_mul (damping nu wave.1)).exp
  have factorAC : AbsolutelyContinuousOnInterval factor a b :=
    (show ContDiff ℝ 1 factor by fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have weightedAC : AbsolutelyContinuousOnInterval (fun time => factor time • velocity seed wave.1 time) a b :=
    factorAC.fun_smul (velocity_absolutelyContinuous seed wave a b a_nonnegative ordered)
  have weightedPaid : IntervalIntegrable (fun time => factor time • forcing seed wave.1 time) volume a b :=
    (forcing_integrable seed wave a b a_nonnegative ordered).continuousOn_smul (by fun_prop)
  have weightedDerivative : ∀ᵐ time : ℝ, time ∈ uIcc a b →
      HasDerivAt (fun actual => factor actual • velocity seed wave.1 actual)
        (factor time • forcing seed wave.1 time) time := by
    filter_upwards [velocity_derivative_ae seed wave, (volume : Measure ℝ).ae_ne 0] with time evolves nonzero
    intro inside
    rw [uIcc_of_le ordered] at inside
    have positive : 0 < time := lt_of_le_of_ne (a_nonnegative.trans inside.1) (Ne.symm nonzero)
    have product := (factorDerivative time).fun_smul (evolves positive)
    simpa only [rate, smul_sub, smul_smul, sub_add_cancel] using product
  have written := path_sub_eq_intervalIntegral weightedAC weightedPaid weightedDerivative b (by simp)
  have start : factor a = 1 := by simp [factor]
  rw [start, one_smul] at written
  have primitive : velocity seed wave.1 a + (∫ time in a..b, factor time • forcing seed wave.1 time) =
      factor b • velocity seed wave.1 b := by
    simpa only [add_comm] using (eq_add_of_sub_eq written).symm
  symm
  unfold heatDuhamelComplexCoordinatePath intervalIntegralComplexCoordinatePath
  change Real.exp (-damping nu wave.1 * (b - a)) •
    (velocity seed wave.1 a + (∫ time in a..b, factor time • forcing seed wave.1 time)) = _
  rw [primitive, smul_smul]
  dsimp only [factor]
  rw [← Real.exp_add]
  have cancel : -damping nu wave.1 * (b - a) + damping nu wave.1 * (b - a) = 0 := by ring
  rw [cancel, Real.exp_zero, one_smul]

theorem source_duhamel_nonzero (seed : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    velocity seed wave.1 b = Real.exp (-damping nu wave.1 * (b - a)) • velocity seed wave.1 a +
      ∫ time in a..b, Real.exp (-damping nu wave.1 * (b - time)) • forcing seed wave.1 time := by
  rw [source_eq_heatDuhamel seed wave a b a_nonnegative ordered,
    heatDuhamelComplexCoordinatePath_eq_heat_add_integral]

@[simp] theorem velocity_zero (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    velocity seed 0 time = 0 := wholeVelocity_zero _

@[simp] theorem forcing_zero (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    forcing seed 0 time = 0 := by
  simp [forcing, projectedDivergenceCLM_apply, transverseProjection]

theorem forcing_intervalIntegrable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    IntervalIntegrable (forcing seed wave) volume a b := by
  by_cases nonzero : wave ≠ 0
  · exact forcing_integrable seed ⟨wave, nonzero⟩ a b a_nonnegative ordered
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    have same : forcing seed 0 = fun _ => (0 : ComplexCoordinateVector) := funext (forcing_zero seed)
    rw [same]
    exact intervalIntegrable_const

theorem source_duhamel (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (ordered : a ≤ b) :
    velocity seed wave b = Real.exp (-damping nu wave * (b - a)) • velocity seed wave a +
      ∫ time in a..b, Real.exp (-damping nu wave * (b - time)) • forcing seed wave time := by
  by_cases nonzero : wave ≠ 0
  · exact source_duhamel_nonzero seed ⟨wave, nonzero⟩ a b a_nonnegative ordered
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp only [velocity_zero, forcing_zero, smul_zero, intervalIntegral.integral_zero, add_zero]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem forcing_generated_next {seed : GeneratedWholeRestartCurrent nu}
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (wave : IntegerWavevector) (time : ℝ) (nonnegative : 0 ≤ time) :
    forcing seed wave (response.2.clockAdvance + time) = forcing response.1 wave time := by
  have same := NativeUnifiedGlobalStressSource.source_generated_next response generated time nonnegative
  unfold forcing NativeUnifiedGlobalStressSource.stress
  rw [same]

end
end SaturationMonoid.NavierStokes.NativeUnifiedGlobalDuhamel
