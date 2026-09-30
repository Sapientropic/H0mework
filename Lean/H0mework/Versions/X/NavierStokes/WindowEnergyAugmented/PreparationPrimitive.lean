import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.PreparationCurrent
import H0mework.Versions.X.NavierStokes.WindowEnergyJoint.NormalForm

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowPreparedPrimitiveControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open NativeWindowPreparedCurrentBudget
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

theorem average_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (time horizon : ℝ) (inside : time∈Icc (-2 : ℝ) horizon) (field : ℝ→E)
    (paid : IntegrableOn field (Icc (-1 : ℝ) (horizon+2))) (budget : ℝ)
    (bounded : (∫ sample in Icc (-1 : ℝ) (horizon+2),‖field sample‖)≤budget) :
    ‖∫ shift,NativeForwardWindowJets.kernelJet order shift • field (time-shift)‖≤
      NativeWindowFiniteStressUniform.kernelBound order*budget := by
  rw [← NativeWindowPreparedSobolevWindow.average_original order time horizon inside field,NativeWindowPreparedSobolevWindow.average]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_ae (NativeWindowPreparedSobolevWindow.average_integrable order time horizon paid).norm
    (paid.norm.const_mul (NativeWindowFiniteStressUniform.kernelBound order)) (Eventually.of_forall fun sample => by
      dsimp only
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (NativeWindowFiniteStressUniform.kernel_bounded order (time-sample)) (norm_nonneg _))).trans
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left bounded (NativeWindowFiniteStressUniform.kernelBound_positive order).le

def pressurePayment (radius : ℕ) (horizon : ℝ) : ℝ := NativeWindowHighPressureCurrent.cap stackedShortCurrent*
  ∫ sample in Icc (-1 : ℝ) (horizon+2),gradientTail radius sample

def convectionPayment (radius : ℕ) (horizon : ℝ) : ℝ := NativeWindowHighTransportProduct.cap*
  ∫ sample in Icc (-1 : ℝ) (horizon+2),convectionWeight radius sample

theorem pressure_integral_bound (F : Finset IntegerWavevector) (radius : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon) :
    (∫ sample in Icc (-1 : ℝ) (horizon+2),‖NativeWindowHighPressureCurrent.current stackedShortCurrent F radius sample‖)≤
      pressurePayment radius horizon := by
  rw [pressurePayment,← integral_const_mul]
  apply integral_mono_ae (NativeWindowHighPressureCurrent.current_integrable stackedShortCurrent F radius (-1) (horizon+2)).norm
    ((gradientTail_integrable radius horizon nonnegative).const_mul (NativeWindowHighPressureCurrent.cap stackedShortCurrent))
  filter_upwards [ae_restrict_of_ae pressure_current_bound_ae] with sample bound
  exact bound F radius

theorem convection_integral_bound (F : Finset IntegerWavevector) (radius : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon) :
    (∫ sample in Icc (-1 : ℝ) (horizon+2),‖NativeWindowHighTransportSource.current stackedShortCurrent F radius sample‖)≤
      convectionPayment radius horizon := by
  rw [convectionPayment,← integral_const_mul]
  apply integral_mono_ae (NativeWindowHighTransportSource.current_continuous stackedShortCurrent F radius).integrableOn_Icc.norm
    ((convectionWeight_integrable radius horizon nonnegative).const_mul NativeWindowHighTransportProduct.cap)
  filter_upwards [ae_restrict_of_ae convection_current_bound_ae] with sample bound
  exact (bound F radius).trans_eq (by unfold convectionWeight; ring)

theorem pressure_window_bound (F : Finset IntegerWavevector) (radius order : ℕ) (time horizon : ℝ)
    (nonnegative : 0≤horizon) (inside : time∈Icc (-2 : ℝ) horizon) :
    ‖NativeWindowHighPressureResolvent.window stackedShortCurrent F radius order time‖≤
      NativeWindowFiniteStressUniform.kernelBound order*pressurePayment radius horizon :=
  average_bound order time horizon inside _
    (NativeWindowHighPressureCurrent.current_integrable stackedShortCurrent F radius (-1) (horizon+2))
    _ (pressure_integral_bound F radius horizon nonnegative)

theorem convection_window_bound (F : Finset IntegerWavevector) (radius order : ℕ) (time horizon : ℝ)
    (nonnegative : 0≤horizon) (inside : time∈Icc (-2 : ℝ) horizon) :
    ‖NativeWindowHighTransportSource.window stackedShortCurrent F radius order time‖≤
      NativeWindowFiniteStressUniform.kernelBound order*convectionPayment radius horizon :=
  average_bound order time horizon inside _
    (NativeWindowHighTransportSource.current_continuous stackedShortCurrent F radius).integrableOn_Icc
    _ (convection_integral_bound F radius horizon nonnegative)

def jointPayment (radius order : ℕ) (horizon : ℝ) : ℝ :=
  (3*NativeWindowHighTransportResolvent.cap butterflyGainViscosity)*NativeWindowFiniteStressUniform.kernelBound order*
    (convectionPayment radius horizon+pressurePayment radius horizon)

theorem jointPayment_tendsto (order : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon) :
    Tendsto (fun radius => jointPayment radius order horizon) atTop (𝓝 0) := by
  have first := (convectionWeight_integral_tendsto horizon nonnegative).const_mul NativeWindowHighTransportProduct.cap
  have last := (gradientTail_integral_tendsto horizon nonnegative).const_mul (NativeWindowHighPressureCurrent.cap stackedShortCurrent)
  simpa only [jointPayment,convectionPayment,pressurePayment,mul_zero,add_zero] using
    (first.add last).const_mul ((3*NativeWindowHighTransportResolvent.cap butterflyGainViscosity)*NativeWindowFiniteStressUniform.kernelBound order)

theorem correctionJet_bound (F : Finset IntegerWavevector) (radius order : ℕ) (time horizon : ℝ)
    (nonnegative : 0≤horizon) (inside : time∈Icc (-2 : ℝ) horizon) (output input : Coordinate) :
    ‖NativeWindowJointNormalForm.correctionJet stackedShortCurrent F radius order time output input‖≤
      jointPayment radius order horizon := by
  apply (NativeWindowJointNormalForm.correctionJet_bound stackedShortCurrent F radius order time output input).trans
  have first := (NativeWindowHighTransportResolvent.resolve_bound butterflyGainViscosity output input
    (NativeWindowHighTransportSource.window stackedShortCurrent F radius order time)).trans
      (mul_le_mul_of_nonneg_left (convection_window_bound F radius order time horizon nonnegative inside)
        (by positivity [NativeWindowHighTransportResolvent.cap_positive butterflyGainViscosity]))
  have last := (NativeWindowHighTransportResolvent.resolve_bound butterflyGainViscosity output input
    (NativeWindowHighPressureResolvent.window stackedShortCurrent F radius order time)).trans
      (mul_le_mul_of_nonneg_left (pressure_window_bound F radius order time horizon nonnegative inside)
        (by positivity [NativeWindowHighTransportResolvent.cap_positive butterflyGainViscosity]))
  exact (add_le_add first last).trans_eq (by unfold jointPayment; ring)

theorem correctionJet_small (order : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∀ radius≥low,∀ F : Finset IntegerWavevector,∀ time∈Icc (-2 : ℝ) horizon,∀ output input,
      ‖NativeWindowJointNormalForm.correctionJet stackedShortCurrent F radius order time output input‖<epsilon := by
  obtain ⟨low,paid⟩ := eventually_atTop.mp ((jointPayment_tendsto order horizon nonnegative).eventually (Iio_mem_nhds positive))
  exact ⟨low,fun radius above F time inside output input =>
    (correctionJet_bound F radius order time horizon nonnegative inside output input).trans_lt (paid radius above)⟩

end
end SaturationMonoid.NavierStokes.NativeWindowPreparedPrimitiveControl
