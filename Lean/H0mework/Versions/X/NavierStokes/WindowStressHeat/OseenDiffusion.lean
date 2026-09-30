import H0mework.Versions.X.NavierStokes.WindowHistory.Gradient
import H0mework.Versions.X.NavierStokes.WindowStressHeat.Balance
import H0mework.Versions.X.NavierStokes.WindowEnergyApproximation.Window

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowStressOseenDiffusion
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeCompleteStressAction
open NativeWindowHistoryGradient NativePhysicalGradient NativeWindowFiniteGramFourier
noncomputable section
variable {nu : Viscosity}

def derivativeState (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (direction : Coordinate) : FullSpace :=
  WithLp.toLp 2 (directionCLM direction (gradientState seed time),0)

theorem derivative_original_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ direction wave coordinate,
      wholeVelocity (derivativeState seed time direction).fst wave coordinate =
        multiplier wave direction*wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave coordinate := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with time regular nonnegative direction wave coordinate
  change wholeVelocity (directionCLM direction (gradientState seed time)) wave coordinate = _
  rw [gradientState_original seed time nonnegative (regular nonnegative)]
  have original := derivativeRead_original (0,coordinate) direction
    (NativeUnheatedSourceGradient.physical seed time nonnegative) (regular nonnegative) wave
  change wholeVelocity (directionCLM direction _) (wave-0) coordinate = _ at original
  simpa only [sub_zero,NativeUnheatedSourceGradient.physical,NativeUnifiedCompleteSource.velocity_read] using! original

theorem derivative_read_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ F direction coordinate,
      read F coordinate (derivativeState seed time direction) =
        NativeWindowStressHeatSource.jetRead F direction 1 coordinate (NativeUnifiedCompleteSource.source seed time) := by
  filter_upwards [derivative_original_ae seed] with time original nonnegative F direction coordinate
  ext point
  change ((complexRead F coordinate (derivativeState seed time direction)) point).re = _
  rw [NativeWindowStressHeatSource.jetRead_apply]
  congr 1
  simp only [complexRead,sum_apply,ContinuousMap.sum_apply,NativeWindowStressHeatSource.polynomial,
    ContinuousMap.smul_apply,pow_one,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro wave _
  change wholeVelocity (derivativeState seed time direction).fst wave coordinate*UnitAddTorus.mFourier wave point = _
  rw [original nonnegative]
  rfl

theorem derivative_reality_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ direction,
      FiniteStateFourierReality (wholeVelocity (derivativeState seed time direction).fst) := by
  filter_upwards [derivative_original_ae seed] with time original nonnegative direction
  intro wave
  funext coordinate
  have reality := congrFun (wholeVelocity_reality _ (NativeCompletePairedAction.source seed time).reality wave) coordinate
  change wholeVelocity (derivativeState seed time direction).fst (waveNeg wave) coordinate =
    star (wholeVelocity (derivativeState seed time direction).fst wave coordinate)
  rw [original nonnegative,original nonnegative]
  have source : wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (waveNeg wave) coordinate =
      star (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave coordinate) := reality
  rw [source]
  simp [multiplier,complexWavevector,waveNeg]

theorem projection_bound (F : Finset IntegerWavevector) (value : ComplexVorticityHilbertState) :
    ‖complexSharpSupportProjection F value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  simp only [complexSharpSupportProjection_apply]
  split_ifs <;> simp

theorem derivative_projection_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F : Finset IntegerWavevector) (direction : Coordinate) :
    ‖complexSharpSupportProjection F (wholeVelocity (derivativeState seed time direction).fst)‖ ≤ ‖gradientState seed time‖ :=
  (projection_bound F _).trans ((wholeVelocity_norm_le _).trans (direction_bound direction _))

theorem pair_coefficient_bound_ae (seed : GeneratedWholeRestartCurrent nu)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ direction output input wave,
      ‖fourierRead wave (NativeWindowStressHeatSource.jetRead F direction 1 output (NativeUnifiedCompleteSource.source seed time)*
        NativeWindowStressHeatSource.jetRead F direction 1 input (NativeUnifiedCompleteSource.source seed time))‖ ≤
          3*(2*Real.pi)^2*NativeUnheatedSourceGradient.mass seed time := by
  filter_upwards [derivative_read_ae seed,derivative_reality_ae seed] with time original reality nonnegative direction output input wave
  rw [← original nonnegative F direction output,← original nonnegative F direction input]
  change ‖fourierRead wave (pairRead F output input (derivativeState seed time direction))‖ ≤ _
  rw [pair_fourier F _ (complexSharpSupportProjection_reality _ _ closed (reality nonnegative direction)),norm_neg,
    NativeCompleteStressBilinear.mixed_read]
  have row := NativeHigherTimeJets.mixedFlux_norm_le
    (complexSharpSupportProjection F (wholeVelocity (derivativeState seed time direction).fst))
    (complexSharpSupportProjection F (wholeVelocity (derivativeState seed time direction).fst)) wave
  apply (row output input).trans
  have bound := derivative_projection_bound seed time F direction
  have squared := pow_le_pow_left₀ (norm_nonneg _) bound 2
  have square := gradientState_square seed time
  nlinarith only [squared,square]

theorem weighted_mass_horizon (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ)
    (inside : time ∈ Icc 0 horizon) :
    (∫ shift, NativeUnheatedSourceGradient.mass seed (time-shift) ∂NativeForwardWindowPairingReadout.averageMeasure) ≤
      NativeWindowFiniteStressUniform.kernelBound 0*
        NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2) := by
  have mass := NativeUnheatedSourceGradient.mass_integrable seed (horizon+2) (by linarith [inside.1,inside.2])
  rw [NativeForwardWindowPairingReadout.density_integral]
  change (∫ shift, NativeForwardWindowJets.kernelJet 0 shift • NativeUnheatedSourceGradient.mass seed (time-shift)) ≤ _
  rw [← NativeWindowFiniteStressUniform.average_original 0 time horizon inside]
  unfold NativeWindowFiniteStressUniform.average
  have paid := integral_mono_ae (NativeWindowFiniteStressUniform.average_integrable 0 time horizon mass)
    (mass.const_mul (NativeWindowFiniteStressUniform.kernelBound 0)) (Eventually.of_forall (fun sample => by
      change NativeForwardWindowJets.kernelJet 0 (time-sample)*_ ≤ _
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans
        (NativeWindowFiniteStressUniform.kernel_bounded 0 (time-sample)))
        (NativeUnheatedSourceGradient.mass_nonnegative seed sample)))
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left
    (NativeUnheatedSourceGradient.mass_integral_bound seed (horizon+2) (by linarith [inside.1,inside.2]))
    (NativeWindowFiniteStressUniform.kernelBound_positive 0).le)

theorem product_average_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F)
    (direction output input : Coordinate) (wave : IntegerWavevector) :
    ‖fourierRead wave (NativeWindowStressHeatSource.productAverage seed time
      (NativeWindowStressHeatSource.jetRead F direction 1 output) (NativeWindowStressHeatSource.jetRead F direction 1 input))‖ ≤
        3*(2*Real.pi)^2*(∫ shift, NativeUnheatedSourceGradient.mass seed (time-shift)
          ∂NativeForwardWindowPairingReadout.averageMeasure) := by
  have bound := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
    (pair_coefficient_bound_ae seed F closed)
  have moved := (withDensity_absolutelyContinuous volume (fun shift =>
    (NativeForwardWindowPairingReadout.density shift : ℝ≥0∞))).ae_le bound
  have paid := NativeWindowStressHeatSource.product_integrable seed time
    (NativeWindowStressHeatSource.jetRead F direction 1 output) (NativeWindowStressHeatSource.jetRead F direction 1 input)
  rw [NativeWindowStressHeatSource.productAverage,← (fourierRead wave).integral_comp_comm paid]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae ((fourierRead wave).integrable_comp paid).norm
    ((weighted_mass_integrable seed time (by linarith)).const_mul (3*(2*Real.pi)^2))
  filter_upwards [moved,NativeWindowHistoryGNS.average_support] with shift original support
  exact original (by linarith) direction output input wave

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  9*(2*Real.pi)^2*NativeWindowFiniteStressUniform.kernelBound 0*
    NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2)

theorem diffusion_bound (seed : GeneratedWholeRestartCurrent nu) (time horizon : ℝ) (inside : time ∈ Icc 0 horizon)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F)
    (output input : Coordinate) (wave : IntegerWavevector) :
    ‖fourierRead wave (NativeWindowStressHeatSource.diffusion seed time F output input)‖ ≤ budget seed horizon := by
  simp only [NativeWindowStressHeatSource.diffusion,map_sum]
  apply (norm_sum_le _ _).trans
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun direction _ => product_average_bound seed time inside.1 F closed direction output input wave)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at paid
  apply paid.trans
  have mass := weighted_mass_horizon seed time horizon inside
  have scaled := mul_le_mul_of_nonneg_left mass (by positivity : 0 ≤ 9*(2*Real.pi)^2)
  convert! scaled using 1
  · ring
  · unfold budget
    ring

end
end SaturationMonoid.NavierStokes.NativeWindowStressOseenDiffusion
