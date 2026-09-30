import H0mework.NavierStokes.UnheatedWriterPair.Flux
import H0mework.NavierStokes.WindowPhysics.WindowEvolution

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairWindowTail

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientNativeFluidMedium SourceGeneratedNativeResponseDisposition
open NativeCompleteStressCarrier NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeUnheatedPairInverseKernel NativeUnheatedPairInverseFlux NativeForwardWindowJets

noncomputable section
variable {nu : Viscosity}

def velocity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ComplexVorticityHilbertState :=
  wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst

theorem velocity_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (velocity seed) (volume : Measure ℝ) := by
  let read : FullSpace →L[ℝ] ComplexVorticityHilbertState :=
    wholeVelocityCLM.comp NativeForwardWindowEvolution.velocityRead
  change AEStronglyMeasurable (read ∘ NativeUnifiedCompleteSource.source seed) volume
  exact read.continuous.comp_aestronglyMeasurable (NativeUnifiedCompleteSource.source_measurable seed)

theorem velocity_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖velocity seed time‖ ≤ NativeUnifiedCompleteSource.budget seed :=
  (wholeVelocity_norm_le _).trans ((WithLp.norm_fst_le _ _).trans
    (NativeUnifiedCompleteSource.source_bound seed time))

def raw (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (wave : IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : ℂ :=
  coefficient nu order (velocity seed time) (velocity seed time) wave output input

theorem raw_measurable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    AEStronglyMeasurable (raw seed order wave output input) (volume : Measure ℝ) := by
  have continuous : Continuous (fun value : ComplexVorticityHilbertState =>
      coefficientCLM nu order wave output input value value) :=
    (coefficientCLM nu order wave output input).continuous.clm_apply continuous_id
  exact continuous.comp_aestronglyMeasurable (velocity_measurable seed)

def quadraticBudget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  3 * NativeUnifiedCompleteSource.budget seed ^ 2

theorem raw_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (wave : IntegerWavevector) (output input : Coordinate) (time : ℝ) :
    ‖raw seed order wave output input time‖ ≤ rowBudget nu order wave * quadraticBudget seed := by
  apply (coefficient_bound order (velocity seed time) (velocity seed time) wave output input).trans
  apply mul_le_mul_of_nonneg_left _ (rowBudget_nonnegative order wave)
  have paid := pow_le_pow_left₀ (norm_nonneg _) (velocity_bound seed time) 2
  dsimp [quadraticBudget]
  nlinarith

theorem raw_locallyIntegrable (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    LocallyIntegrable (raw seed order wave output input) :=
  (memLp_top_of_bound (raw_measurable seed order wave output input)
    (rowBudget nu order wave * quadraticBudget seed)
    (Eventually.of_forall (raw_bound seed order wave output input))).locallyIntegrable le_top

def tail (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ) (time : ℝ) :
    NativeFluidStressFourierState := fun wave output input =>
  ∫ shift : ℝ, kernelJet timeOrder shift • raw seed inverseOrder wave output input (time - shift)

theorem integrand_integrable (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ)
    (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    Integrable (fun shift : ℝ => kernelJet timeOrder shift • raw seed inverseOrder wave output input (time - shift)) :=
  (kernelJet_compact timeOrder).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernelJet_smooth timeOrder).continuous (raw_locallyIntegrable seed inverseOrder wave output input) time

theorem tail_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ)
    (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    HasDerivAt (fun sample => tail seed timeOrder inverseOrder sample wave output input)
      (tail seed (timeOrder + 1) inverseOrder time wave output input) time := by
  have actual := (kernelJet_compact timeOrder).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kernelJet_smooth timeOrder).of_le (by simp)) (raw_locallyIntegrable seed inverseOrder wave output input) time
  simpa only [tail, kernelJet, iteratedDeriv_succ] using! actual

def budget (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ) : ℝ :=
  (∫ shift : ℝ, ‖kernelJet timeOrder shift‖) * ((scale nu)⁻¹ ^ inverseOrder * quadraticBudget seed)

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ) :
    0 ≤ budget seed timeOrder inverseOrder := by
  have integral : 0 ≤ ∫ shift : ℝ, ‖kernelJet timeOrder shift‖ :=
    integral_nonneg (fun shift => norm_nonneg (kernelJet timeOrder shift))
  unfold budget quadraticBudget
  positivity [scale_positive (nu := nu)]

theorem tail_bound (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ)
    (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    ‖tail seed timeOrder inverseOrder time wave output input‖ ≤
      budget seed timeOrder inverseOrder * weight wave ^ inverseOrder := by
  have paid := norm_integral_le_of_norm_le
    (f := fun shift : ℝ => kernelJet timeOrder shift • raw seed inverseOrder wave output input (time - shift))
    ((kernelJet_integrable timeOrder).norm.mul_const (rowBudget nu inverseOrder wave * quadraticBudget seed))
    (Eventually.of_forall (fun shift : ℝ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (raw_bound seed inverseOrder wave output input (time - shift))
        (norm_nonneg _)))
  rw [integral_mul_const] at paid
  exact paid.trans_eq (by dsimp [budget, rowBudget]; ring)

theorem tail_next (seed : GeneratedWholeRestartCurrent nu) (timeOrder inverseOrder : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    tail seed timeOrder inverseOrder (response.2.clockAdvance + time) =
      tail response.1 timeOrder inverseOrder time := by
  funext wave output input
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : kernelJet timeOrder shift = 0
  · simp only [zero, zero_smul]
  · simp only [raw, velocity, add_sub_assoc,
      NativeUnifiedCompleteSource.source_generated_next seed response generated (time - shift)
        (by linarith [kernelJet_nonpositive timeOrder shift zero])]

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairWindowTail
