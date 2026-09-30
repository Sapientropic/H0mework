import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedSchurMass
import H0mework.Versions.X.NavierStokes.WindowEnergyPressure.PreparationSource

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedGraph
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier (wholeVelocity)
open NativePhysicalPairing (includeCLM)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeUnheatedStressProduct (gradientMass density density_nonnegative projection_mass)
open NativeWindowPreparedPressureSource (gradientEnvelope)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
noncomputable section
variable {nu : Viscosity}

theorem graph_sample_before (seed : GeneratedWholeRestartCurrent nu)
    (F : Finset IntegerWavevector) (sample : ℝ) (before : sample ≤ 0) :
    NativeWindowAugmentedPayment.graphSample seed F sample =
      NativeWindowAugmentedPayment.graphSample seed F 0 := by
  rw [NativeWindowAugmentedPayment.graphSample_original,
    NativeWindowAugmentedPayment.graphSample_original]
  have same : NativeUnheatedWindowStress.projection seed F sample =
      NativeUnheatedWindowStress.projection seed F 0 := by
    unfold NativeUnheatedWindowStress.projection
    rw [← NativeUnifiedCompleteSource.velocity_read seed sample,
      NativeWindowPreparationSource.complete_nonpositive seed sample before,
      NativeUnifiedCompleteSource.velocity_read]
  rw [same]

theorem graph_original_total (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (sample : ℝ) :
    NativeFiniteActionResolvent.pairing (modes M)
        (NativeWindowTraceAdjoint.value seed M sample)
        (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
          (NativeWindowTraceAdjoint.value seed M sample)) =
      NativeWindowAugmentedPayment.graphSample seed (modes M) sample := by
  by_cases nonnegative : 0 ≤ sample
  · exact NativeWindowTraceCutActionPhysical.graph_original seed M sample nonnegative
  · have before : sample ≤ 0 := le_of_not_ge nonnegative
    have value : NativeWindowTraceAdjoint.value seed M sample =
        NativeWindowTraceAdjoint.value seed M 0 := by
      simp only [NativeWindowTraceAdjoint.value,
        NativeWindowHierarchyPairWindow.state_before seed sample before]
    rw [value,graph_sample_before seed (modes M) sample before]
    exact NativeWindowTraceCutActionPhysical.graph_original seed M 0 le_rfl

theorem history_gradient_original_total (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) :
    gradient M (finiteHistory seed time M) =
      NativeWindowAugmentedPayment.graphJet seed (modes M) 0 time := by
  have average : (∫ shift,NativeWindowAugmentedPayment.graphSample seed (modes M)
      (time-shift) ∂averageMeasure) =
      NativeWindowAugmentedPayment.graphJet seed (modes M) 0 time := by
    rw [NativeForwardWindowPairingReadout.density_integral]
    rfl
  apply Eq.trans _ average
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryOseen.history_original seed M time] with shift original
  rw [original,NativeWindowHistoryOseen.velocityPath,NativePhysicalPairing.restrict_include]
  exact (NativeWindowOperatorGreen.laplacian_pairing (modes M) (modes_zero M)
    (modes_closed M) nu _ _).symm.trans (graph_original_total seed M (time-shift))

theorem graph_sample_bound_regular (sample : ℝ)
    (regular : NativeUnheatedStressProduct.H1
      (wholeVelocity (NativeWindowPreparedPressureSource.physical sample).1)) (M : ℕ) :
    NativeWindowAugmentedPayment.graphSample stackedShortCurrent (NativeWholeH1Mixed.modes M) sample ≤
      (2*Real.pi)^2*gradientEnvelope sample := by
  have read : NativeUnheatedWindowStress.projection stackedShortCurrent (NativeWholeH1Mixed.modes M) sample =
      complexSharpSupportProjection (NativeWholeH1Mixed.modes M)
        (wholeVelocity (NativeWindowPreparedPressureSource.physical sample).1) := by
    unfold NativeUnheatedWindowStress.projection
    rw [NativeWindowPreparedPressureSource.physical_original,
      NativeUnifiedCompleteSource.velocity_read]
  rw [NativeWindowAugmentedPayment.graphSample_original,read,projection_mass,
    ← NativeWindowPreparedPressureSource.physical_mass]
  exact mul_le_mul_of_nonneg_left
    (regular.sum_le_tsum _ (fun wave _ => density_nonnegative _ wave)) (sq_nonneg _)

theorem graph_sample_bound_ae : ∀ᵐ sample : ℝ,∀ M : ℕ,
    NativeWindowAugmentedPayment.graphSample stackedShortCurrent (NativeWholeH1Mixed.modes M) sample ≤
      (2*Real.pi)^2*gradientEnvelope sample := by
  filter_upwards [NativeWindowPreparedPressureSource.physical_regular_ae] with sample regular M
  exact graph_sample_bound_regular sample regular M

theorem graph_sample_zero_bound (M : ℕ) :
    NativeWindowAugmentedPayment.graphSample stackedShortCurrent (NativeWholeH1Mixed.modes M) 0 ≤
      (2*Real.pi)^2*gradientEnvelope 0 := by
  apply graph_sample_bound_regular 0
  simp only [NativeWindowPreparedPressureSource.physical,dif_pos le_rfl]
  change NativeWholeH1Mixed.H1
    (NativeUnheatedSourceGradient.physical stackedShortCurrent 0 le_rfl)
  exact NativeWindowPreparedPressureSource.initial_regular

theorem value_zero_gradient_bound (M : ℕ) :
    NativeCommonAdvectorAction.curlPair (modes M)
      (NativeWindowTraceAdjoint.value stackedShortCurrent M 0).1
      (NativeWindowTraceAdjoint.value stackedShortCurrent M 0).1 ≤
      (2*Real.pi)^2*gradientEnvelope 0 := by
  rw [← NativeWindowOperatorGreen.laplacian_pairing (modes M) (modes_zero M)
    (modes_closed M) RationalVorticityEvaluator.butterflyGainViscosity]
  rw [graph_original_total]
  exact graph_sample_zero_bound M

def graphBudget (order : ℕ) (horizon : ℝ) : ℝ :=
  NativeWindowFiniteStressUniform.kernelBound order*(2*Real.pi)^2*
    ∫ sample in Icc (-1 : ℝ) (horizon+2),gradientEnvelope sample

theorem graphBudget_nonnegative (order : ℕ) (horizon : ℝ) : 0 ≤ graphBudget order horizon := by
  unfold graphBudget
  exact mul_nonneg
    (mul_nonneg (NativeWindowFiniteStressUniform.kernelBound_positive order).le (sq_nonneg _))
    (integral_nonneg NativeWindowPreparedPressureSource.gradientEnvelope_nonnegative)

theorem graph_jet_bound (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (M order : ℕ) (time : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) :
    ‖NativeWindowAugmentedPayment.graphJet stackedShortCurrent
      (NativeWholeH1Mixed.modes M) order time‖ ≤ graphBudget order horizon := by
  change ‖∫ shift,NativeForwardWindowJets.kernelJet order shift •
    NativeWindowAugmentedPayment.graphSample stackedShortCurrent
      (NativeWholeH1Mixed.modes M) (time-shift)‖ ≤ _
  rw [← NativeWindowPreparedSobolevWindow.average_original order time horizon inside]
  change ‖∫ sample in Icc (-1 : ℝ) (horizon+2),
    NativeForwardWindowJets.kernelJet order (time-sample) •
      NativeWindowAugmentedPayment.graphSample stackedShortCurrent
        (NativeWholeH1Mixed.modes M) sample‖ ≤ _
  have paid := norm_integral_le_of_norm_le
    (f := fun sample : ℝ => NativeForwardWindowJets.kernelJet order (time-sample) •
      NativeWindowAugmentedPayment.graphSample stackedShortCurrent
        (NativeWholeH1Mixed.modes M) sample)
    ((NativeWindowPreparedPressureSource.gradientEnvelope_integrable horizon nonnegative).const_mul
      (NativeWindowFiniteStressUniform.kernelBound order*(2*Real.pi)^2)) (by
      filter_upwards [ae_restrict_of_ae graph_sample_bound_ae] with sample bound
      rw [norm_smul,Real.norm_of_nonneg
        (NativeWindowAugmentedPayment.graphSample_nonnegative stackedShortCurrent
          (NativeWholeH1Mixed.modes M) sample)]
      exact (mul_le_mul (NativeWindowFiniteStressUniform.kernel_bounded order (time-sample))
        (bound M)
        (NativeWindowAugmentedPayment.graphSample_nonnegative stackedShortCurrent _ sample)
        (NativeWindowFiniteStressUniform.kernelBound_positive order).le).trans_eq (by ring))
  simpa only [integral_const_mul,graphBudget,mul_assoc] using paid

theorem history_gradient_bound (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (M : ℕ) (time : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) :
    gradient M (finiteHistory stackedShortCurrent time M) ≤ graphBudget 0 horizon := by
  rw [history_gradient_original_total]
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le
    (graph_jet_bound horizon nonnegative M 0 time inside))

end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedGraph
