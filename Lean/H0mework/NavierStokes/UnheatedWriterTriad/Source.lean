import H0mework.NavierStokes.UnheatedWriterTriad.Channels
import H0mework.NavierStokes.UnheatedWriterTail.Nonlinear

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadSource

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeResolventCompactness NativeEndpointVelocityCarrier
open NativeUnheatedSourceWeightedTail NativeUnheatedSourceGradient
open NativeUnheatedTriadChannels

noncomputable section
variable {nu : Viscosity}

def input (seed : GeneratedWholeRestartCurrent nu) (slot index : Fin 3) (time : ℝ) :
    NativeUnheatedTriadSum.E :=
  wholeVelocityCLM (if index = slot then nonlinear seed time else velocity seed time)

theorem input_measurable (seed : GeneratedWholeRestartCurrent nu) (slot index : Fin 3) :
    AEStronglyMeasurable (input seed slot index) (volume : Measure ℝ) := by
  change AEStronglyMeasurable (fun time => wholeVelocityCLM (if index = slot then nonlinear seed time else velocity seed time)) volume
  by_cases same : index = slot
  · simpa only [input, if_pos same] using
      wholeVelocityCLM.continuous.comp_aestronglyMeasurable (nonlinear_measurable seed)
  · simpa only [input, if_neg same] using
      wholeVelocityCLM.continuous.comp_aestronglyMeasurable (velocity_measurable seed)

def coefficient (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j output spectator : Coordinate) (time : ℝ) : ℂ :=
  NativeUnheatedTriadSum.value (kernel nu slot i j output) wave i j spectator
    (input seed slot 0 time) (input seed slot 1 time) (input seed slot 2 time)

def bound (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  (3 * cap nu * ‖NativeUnheatedTriadSum.weights‖) *
    Real.sqrt NativeMovingCriticalProductWeights.constant * (NativeUnifiedCompleteSource.budget seed)^2

theorem bound_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ bound seed := by
  unfold bound cap
  positivity [nu.coeff_pos]

theorem input_product (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (time : ℝ) :
    ‖input seed slot 0 time‖ * ‖input seed slot 1 time‖ * ‖input seed slot 2 time‖ ≤
      (Real.sqrt NativeMovingCriticalProductWeights.constant * mass seed time) *
        (NativeUnifiedCompleteSource.budget seed)^2 := by
  have nonlin := (wholeVelocity_norm_le (nonlinear seed time)).trans (nonlinear_bound seed time)
  have vel := (wholeVelocity_norm_le (velocity seed time)).trans (velocity_bound seed time)
  have nonnegative := mul_nonneg (Real.sqrt_nonneg NativeMovingCriticalProductWeights.constant) (mass_nonnegative seed time)
  have budgetNonnegative : 0 ≤ NativeUnifiedCompleteSource.budget seed := (norm_nonneg _).trans vel
  fin_cases slot <;> simp only [input, Fin.ext_iff] <;> norm_num
  · nlinarith [mul_le_mul nonlin vel (norm_nonneg _) nonnegative,
      mul_le_mul (mul_le_mul nonlin vel (norm_nonneg _) nonnegative) vel (norm_nonneg _) (mul_nonneg nonnegative budgetNonnegative)]
  · nlinarith [mul_le_mul vel nonlin (norm_nonneg _) budgetNonnegative,
      mul_le_mul (mul_le_mul vel nonlin (norm_nonneg _) budgetNonnegative) vel (norm_nonneg _) (mul_nonneg budgetNonnegative nonnegative)]
  · nlinarith [mul_le_mul vel vel (norm_nonneg _) budgetNonnegative,
      mul_le_mul (mul_le_mul vel vel (norm_nonneg _) budgetNonnegative) nonlin (norm_nonneg _) (mul_nonneg budgetNonnegative budgetNonnegative)]

theorem coefficient_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3)
    (wave : IntegerWavevector) (i j output spectator : Coordinate) (time : ℝ) :
    ‖coefficient seed slot wave i j output spectator time‖ ≤ bound seed * mass seed time := by
  have generated := NativeUnheatedTriadSum.norm_bound (kernel nu slot i j output) (cap nu)
    (kernel_bound nu slot i j output) wave i j spectator
    (input seed slot 0 time) (input seed slot 1 time) (input seed slot 2 time)
  have scalar0 : 0 ≤ 3 * cap nu * ‖NativeUnheatedTriadSum.weights‖ := by unfold cap; positivity [nu.coeff_pos]
  have paid := mul_le_mul_of_nonneg_left (input_product seed slot time) scalar0
  exact generated.trans (by simpa only [bound, mul_assoc, mul_left_comm, mul_comm] using paid)

theorem coefficient_measurable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3)
    (wave : IntegerWavevector) (i j output spectator : Coordinate) :
    AEStronglyMeasurable (coefficient seed slot wave i j output spectator) (volume : Measure ℝ) :=
  NativeUnheatedTriadSum.aestronglyMeasurable (kernel nu slot i j output) (cap nu)
    (kernel_bound nu slot i j output) wave i j spectator
    (input_measurable seed slot 0) (input_measurable seed slot 1) (input_measurable seed slot 2)

theorem coefficient_integrable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3)
    (wave : IntegerWavevector) (i j output spectator : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (coefficient seed slot wave i j output spectator) (volume.restrict (Icc 0 horizon)) :=
  ((mass_integrable seed horizon nonnegative).const_mul (bound seed)).mono'
    (coefficient_measurable seed slot wave i j output spectator).restrict
    (Eventually.of_forall (coefficient_bound seed slot wave i j output spectator))

theorem coefficient_integral_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3)
    (wave : IntegerWavevector) (i j output spectator : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    (∫ time in Icc 0 horizon, ‖coefficient seed slot wave i j output spectator time‖) ≤
      bound seed * NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) horizon := by
  calc
    _ ≤ ∫ time in Icc 0 horizon, bound seed * mass seed time :=
      integral_mono (coefficient_integrable seed slot wave i j output spectator horizon nonnegative).norm
        ((mass_integrable seed horizon nonnegative).const_mul (bound seed))
        (coefficient_bound seed slot wave i j output spectator)
    _ = bound seed * ∫ time in Icc 0 horizon, mass seed time := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (mass_integral_bound seed horizon nonnegative) (bound_nonnegative seed)

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadSource
