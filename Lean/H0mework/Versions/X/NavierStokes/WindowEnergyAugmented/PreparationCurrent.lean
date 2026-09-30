import H0mework.Versions.X.NavierStokes.WindowEnergyHighPressure.Resolvent
import H0mework.Versions.X.NavierStokes.WindowEnergyPressure.PreparationSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowPreparedCurrentBudget
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeEndpointVelocityCarrier NativeUnheatedStressProduct
open NativeWindowPressureLowInputs (high high_H1 high_mass high_density)
open NativeWindowPreparedPressureSource (physical physical_original physical_measurable physical_regular_ae
  gradientEnvelope gradientEnvelope_nonnegative gradientEnvelope_integrable physical_mass)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section

theorem pressure_value_original (radius : ℕ) (time : ℝ) :
    NativeWindowHighPressureCurrent.value stackedShortCurrent radius time=
      high (wholeVelocity (physical time).1) (integerWaveFrequencyCube radius) := by
  rw [physical_original]
  rfl

def gradientTail (radius : ℕ) (time : ℝ) : ℝ :=
  gradientMass (NativeWindowHighPressureCurrent.value stackedShortCurrent radius time)

theorem gradientTail_nonnegative (radius : ℕ) (time : ℝ) : 0≤gradientTail radius time :=
  tsum_nonneg (density_nonnegative _)

theorem gradientTail_measurable (radius : ℕ) : AEStronglyMeasurable (gradientTail radius) (volume : Measure ℝ) := by
  apply AEMeasurable.aestronglyMeasurable
  apply AEMeasurable.tsum
  intro wave
  have row := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp_aestronglyMeasurable
    (NativeWindowHighPressureCurrent.value_measurable stackedShortCurrent radius)
  have normed := NativeCompleteStressAction.euclideanCLM.continuous.comp_aestronglyMeasurable row
  exact (normed.norm.aemeasurable.pow_const 2).const_mul (integerWaveNormSq wave)

theorem gradientTail_bound_ae : ∀ᵐ time : ℝ,∀ radius,gradientTail radius time≤gradientEnvelope time := by
  filter_upwards [physical_regular_ae] with time regular radius
  rw [gradientTail,pressure_value_original]
  exact (high_mass _ regular _).trans_eq (physical_mass time)

theorem gradientTail_tendsto_ae : ∀ᵐ time : ℝ,Tendsto (fun radius => gradientTail radius time) atTop (𝓝 0) := by
  filter_upwards [physical_regular_ae] with time regular
  let u:=wholeVelocity (physical time).1
  have original : H1 u := regular
  have point (wave : IntegerWavevector) :
      Tendsto (fun radius => density (high u (integerWaveFrequencyCube radius)) wave) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [integerWave_eventually_mem_frequencyCube wave] with radius inside
    rw [high_density,if_pos inside]
  have bounded : ∀ᶠ radius in atTop,∀ wave : IntegerWavevector,
      ‖density (high u (integerWaveFrequencyCube radius)) wave‖≤density u wave := Eventually.of_forall fun radius wave => by
    rw [Real.norm_of_nonneg (density_nonnegative _ _),high_density]
    split_ifs
    · exact density_nonnegative u wave
    · rfl
  have paid := tendsto_tsum_of_dominated_convergence original point bounded
  simpa only [gradientTail,pressure_value_original,gradientMass,tsum_zero] using paid

theorem gradientTail_integrable (radius : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon) :
    IntegrableOn (gradientTail radius) (Icc (-1 : ℝ) (horizon+2)) := by
  apply (gradientEnvelope_integrable horizon nonnegative).mono' (gradientTail_measurable radius).restrict
  filter_upwards [ae_restrict_of_ae gradientTail_bound_ae] with time bound
  rw [Real.norm_of_nonneg (gradientTail_nonnegative radius time)]
  exact bound radius

theorem gradientTail_integral_tendsto (horizon : ℝ) (nonnegative : 0≤horizon) :
    Tendsto (fun radius => ∫ time in Icc (-1 : ℝ) (horizon+2),gradientTail radius time) atTop (𝓝 0) := by
  have paid := tendsto_integral_of_dominated_convergence gradientEnvelope
    (fun radius => (gradientTail_measurable radius).restrict) (gradientEnvelope_integrable horizon nonnegative)
    (fun radius => by
      filter_upwards [ae_restrict_of_ae gradientTail_bound_ae] with time bound
      rw [Real.norm_of_nonneg (gradientTail_nonnegative radius time)]
      exact bound radius) (ae_restrict_of_ae gradientTail_tendsto_ae)
  simpa only [integral_zero] using paid

theorem pressure_current_bound_ae : ∀ᵐ time : ℝ,∀ F radius,
    ‖NativeWindowHighPressureCurrent.current stackedShortCurrent F radius time‖≤
      NativeWindowHighPressureCurrent.cap stackedShortCurrent*gradientTail radius time := by
  filter_upwards [physical_regular_ae] with time regular F radius
  have h : H1 (NativeWindowHighPressureCurrent.value stackedShortCurrent radius time) := by
    rw [pressure_value_original]
    exact high_H1 _ regular _
  have zero : NativeWindowHighPressureCurrent.value stackedShortCurrent radius time 0=0 := by
    rw [pressure_value_original]
    exact NativeWindowPressureLowInputs.high_zero _ (wholeVelocity_zero _) _
  have pressureBound := NativeWindowHighPressureCurrent.pressure_bound _ zero h F
  have actual := NativeWindowHighPressureCurrent.rawCurrent_bound
    (NativeWindowHighPressureCurrent.value stackedShortCurrent radius time) F
  have normed := NativeWindowHighPressureCurrent.value_bound stackedShortCurrent radius time
  have B0 := (norm_nonneg _).trans normed
  apply actual.trans
  calc
    _≤2*NativeWindowHighTransportProduct.cap*NativeUnifiedCompleteSource.budget stackedShortCurrent*
      (12*Real.sqrt NativeUnheatedRieszKernel.constant*gradientTail radius time) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left normed (by positivity [NativeWindowHighTransportProduct.cap_nonnegative]))
          pressureBound (norm_nonneg _) (by positivity [NativeWindowHighTransportProduct.cap_nonnegative])
    _=_ := by unfold NativeWindowHighPressureCurrent.cap; ring

theorem convection_current_bound_ae : ∀ᵐ time : ℝ,∀ F radius,
    ‖NativeWindowHighTransportSource.current stackedShortCurrent F radius time‖≤
      NativeWindowHighTransportProduct.cap*NativeWindowPreparedSobolevSource.envelope time*
        ‖NativeUnheatedSourceWeightedTail.tail radius (NativeUnheatedSourceWeightedTail.velocity stackedShortCurrent time)‖ := by
  filter_upwards [NativeWindowPreparedSobolevSource.source_bound_ae] with time bound F radius
  have cap0 : 0≤NativeWindowHighTransportProduct.cap*NativeWindowPreparedSobolevSource.envelope time*
      ‖NativeUnheatedSourceWeightedTail.tail radius (NativeUnheatedSourceWeightedTail.velocity stackedShortCurrent time)‖ := by
    positivity [NativeWindowHighTransportProduct.cap_nonnegative,NativeWindowPreparedSobolevSource.envelope_nonnegative time]
  apply (pi_norm_le_iff_of_nonneg cap0).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg cap0).mpr
  intro output
  apply (pi_norm_le_iff_of_nonneg cap0).mpr
  intro input
  change ‖NativeWindowHighTransportSource.component stackedShortCurrent F radius j output input time‖≤_
  rw [NativeWindowHighTransportSource.component,norm_neg]
  apply (NativeWindowHighTransportProduct.product_bound _ _).trans
  have first := (NativeWindowHighTransportSource.vectorRead_bound j _).trans
    (NativeWindowHighTransportSource.high_bound stackedShortCurrent F radius time)
  have last := (NativeWindowHighTransportSource.tensorRead_bound (output,input) _).trans (bound.2 F)
  exact (mul_le_mul (mul_le_mul_of_nonneg_left first NativeWindowHighTransportProduct.cap_nonnegative)
    last (norm_nonneg _) (by positivity [NativeWindowHighTransportProduct.cap_nonnegative])).trans_eq (by ring)

def convectionWeight (radius : ℕ) (time : ℝ) : ℝ := NativeWindowPreparedSobolevSource.envelope time*
  ‖NativeUnheatedSourceWeightedTail.tail radius (NativeUnheatedSourceWeightedTail.velocity stackedShortCurrent time)‖

theorem convectionWeight_integrable (radius : ℕ) (horizon : ℝ) (nonnegative : 0≤horizon) :
    IntegrableOn (convectionWeight radius) (Icc (-1 : ℝ) (horizon+2)) := by
  apply (NativeWindowPreparedSobolevSource.envelope_integrable horizon nonnegative).mul_bdd
    (((NativeUnheatedSourceWeightedTail.tail_continuous radius).comp_aestronglyMeasurable
      (NativeUnheatedSourceWeightedTail.velocity_measurable stackedShortCurrent)).norm.restrict)
  exact Eventually.of_forall fun time => by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (NativeUnheatedSourceWeightedTail.tail_norm_bound radius _).trans
      (mul_le_mul_of_nonneg_left (NativeUnheatedSourceWeightedTail.velocity_bound stackedShortCurrent time) (by norm_num))

theorem convectionWeight_integral_tendsto (horizon : ℝ) (nonnegative : 0≤horizon) :
    Tendsto (fun radius => ∫ time in Icc (-1 : ℝ) (horizon+2),convectionWeight radius time) atTop (𝓝 0) :=
  NativeUnheatedSourceWeightedTail.weighted_tail_tendsto
    (NativeUnheatedSourceWeightedTail.velocity_measurable stackedShortCurrent).restrict
    (NativeWindowPreparedSobolevSource.envelope_integrable horizon nonnegative)
    (NativeUnifiedCompleteSource.budget stackedShortCurrent) (NativeUnheatedSourceWeightedTail.velocity_bound stackedShortCurrent)

end
end SaturationMonoid.NavierStokes.NativeWindowPreparedCurrentBudget
