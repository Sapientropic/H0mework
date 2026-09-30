import H0mework.NavierStokes.WindowHistory.Translation
import H0mework.NavierStokes.UnheatedWriterTail.Nonlinear
import H0mework.NavierStokes.SourceUnheated.WindowGradient
import H0mework.NavierStokes.UnheatedWriterPair.NegativeKernel

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryGradient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing NativeEndpointVelocityCarrier
open NativeUnheatedSourceGradient NativeUnheatedSourceWeightedTail NativeUnheatedGlobalNegativeOne
open NativePhysicalFourier NativePhysicalGradient NativeWindowHistoryGNS NativeForwardWindowPairingReadout
open NativeUnheatedPairNegativeKernel NativeCofinalStressPositivity
noncomputable section
variable {nu : Viscosity}

def gradientState (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : State :=
  nu.coeff⁻¹ • (nonlinear seed time-rate seed time)

theorem gradientState_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    gradientState seed time = gradientValue (physical seed time nonnegative) regular := by
  rw [gradientState, nonlinear, dif_pos nonnegative, dif_pos regular, rate, dif_pos nonnegative, dif_pos regular,
    NativeNegativeOneMomentum.momentum, sub_sub_cancel, inv_smul_smul₀ nu.coeff_pos.ne']

theorem gradientState_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (gradientState seed) (volume : Measure ℝ) :=
  ((nonlinear_measurable seed).sub (rate_measurable seed)).const_smul nu.coeff⁻¹

theorem gradientState_square (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖gradientState seed time‖^2 ≤ (2*Real.pi)^2*mass seed time := by
  by_cases nonnegative : 0 ≤ time
  · by_cases regular : H1 (physical seed time nonnegative)
    · rw [gradientState_original seed time nonnegative regular,gradientValue_norm_sq,physical_mass]
    · simp only [gradientState,nonlinear,rate,dif_pos nonnegative,dif_neg regular,sub_self,smul_zero,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact mul_nonneg (sq_nonneg _) (mass_nonnegative seed time)
  · simp only [gradientState,nonlinear,rate,dif_neg nonnegative,sub_self,smul_zero,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (mass_nonnegative seed time)

def ceiling : ℝ := Real.sqrt (NativeUnheatedWindowGradient.kernelCeiling 0)

theorem ceiling_nonnegative : 0 ≤ ceiling := Real.sqrt_nonneg _

theorem kernel_bound (shift : ℝ) : NativeForwardWindowSource.kernel shift ≤ ceiling := by
  by_cases inside : shift ∈ Icc (-2 : ℝ) (-1)
  · have paid := NativeUnheatedWindowGradient.kernel_square_le 0 shift inside
    simp only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero] at paid
    exact Real.le_sqrt_of_sq_le paid
  · have zero : NativeForwardWindowSource.kernel shift = 0 := by
      by_contra nonzero
      exact inside (NativeUnheatedWindowJensen.kernel_support 0 shift (by simpa only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero] using nonzero))
    rw [zero]
    exact ceiling_nonnegative

theorem mass_shift_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) :
    IntegrableOn (fun shift => mass seed (time-shift)) (Icc (-2 : ℝ) (-1)) := by
  have paid : IntegrableOn (mass seed) (Icc 0 (time+2)) := mass_integrable seed (time+2) (by linarith)
  have restricted := (paid.mono_set (show uIcc (time+1) (time+2) ⊆ Icc 0 (time+2) by
    rw [uIcc_of_le (by linarith)]; intro sample inside; exact ⟨by linarith [inside.1],inside.2⟩)).intervalIntegrable
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ -1)).mp
  convert! (restricted.comp_sub_left time).symm using 1 <;> ring

theorem mass_shift_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) :
    (∫ shift in Icc (-2 : ℝ) (-1), mass seed (time-shift)) ≤
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ -1),
    intervalIntegral.integral_comp_sub_left]
  have first : time-(-1 : ℝ)=time+1 := by ring
  have last : time-(-2 : ℝ)=time+2 := by ring
  rw [first,last]
  have total : IntegrableOn (mass seed) (Icc 0 (time+2)) := mass_integrable seed (time+2) (by linarith)
  have totalInt : IntervalIntegrable (mass seed) volume 0 (time+2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : 0 ≤ time+2)).mpr total
  have comparison := intervalIntegral.integral_mono_interval (show 0 ≤ time+1 by linarith) (show time+1 ≤ time+2 by linarith) le_rfl
    (Eventually.of_forall (mass_nonnegative seed)) totalInt
  apply comparison.trans
  rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ time+2), ← integral_Icc_eq_integral_Ioc]
  exact mass_integral_bound seed (time+2) (by linarith)

theorem weighted_mass_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) :
    Integrable (fun shift => mass seed (time-shift)) averageMeasure := by
  apply (integrable_withDensity_iff_integrable_smul density_measurable).mpr
  change Integrable (fun shift => NativeForwardWindowSource.kernel shift*mass seed (time-shift)) volume
  have supported : Function.support (fun shift => NativeForwardWindowSource.kernel shift*mass seed (time-shift)) ⊆ Icc (-2 : ℝ) (-1) := by
    intro shift nonzero
    apply NativeUnheatedWindowJensen.kernel_support 0 shift
    simpa only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero] using (mul_ne_zero_iff.mp nonzero).1
  apply (integrableOn_iff_integrable_of_support_subset supported).mp
  exact IntegrableOn.continuousOn_mul NativeForwardWindowSource.kernel_smooth.continuous.continuousOn
    (mass_shift_integrable seed time valid) isCompact_Icc

theorem weighted_mass_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) :
    (∫ shift, mass seed (time-shift) ∂averageMeasure) ≤
      ceiling*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2) := by
  rw [density_integral]
  have supported : Function.support (fun shift => NativeForwardWindowSource.kernel shift*mass seed (time-shift)) ⊆ Icc (-2 : ℝ) (-1) := by
    intro shift nonzero
    apply NativeUnheatedWindowJensen.kernel_support 0 shift
    simpa only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero] using (mul_ne_zero_iff.mp nonzero).1
  change (∫ shift, NativeForwardWindowSource.kernel shift*mass seed (time-shift)) ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun shift outside => by
    by_contra nonzero
    exact outside (supported nonzero))]
  have paid := integral_mono_ae
    (IntegrableOn.continuousOn_mul NativeForwardWindowSource.kernel_smooth.continuous.continuousOn (mass_shift_integrable seed time valid) isCompact_Icc)
    ((mass_shift_integrable seed time valid).const_mul ceiling)
    (Eventually.of_forall (fun shift => mul_le_mul_of_nonneg_right (kernel_bound shift) (mass_nonnegative seed (time-shift))))
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (mass_shift_bound seed time valid) ceiling_nonnegative)

theorem multiplier_root_bound (wave : IntegerWavevector) (direction : Coordinate) : ‖multiplier wave direction‖ ≤ root wave := by
  apply (sq_le_sq₀ (norm_nonneg _) (root_nonnegative wave)).mp
  rw [multiplier_norm_sq,root_sq]
  change (2*Real.pi)^2*(wave direction : ℝ)^2 ≤ (2*Real.pi)^2*∑ other : Coordinate, (wave other : ℝ)^2
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun other _ => sq_nonneg (wave other : ℝ)) (Finset.mem_univ direction)) (sq_nonneg _)

def polarization (direction : Coordinate) (wave : Wave) : ℂ := (root wave.1)⁻¹ • multiplier wave.1 direction

theorem polarization_bound (direction : Coordinate) (wave : Wave) : ‖polarization direction wave‖ ≤ 1 := by
  rw [polarization,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (root_nonnegative _))]
  exact (mul_le_mul_of_nonneg_left (multiplier_root_bound wave.1 direction) (inv_nonneg.mpr (root_nonnegative _))).trans_eq
    (inv_mul_cancel₀ (root_positive wave.1 wave.2).ne')

def directionCLM (direction : Coordinate) : State →L[ℝ] State :=
  lp.mapCLM 2 (fun wave : Wave => polarization direction wave • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ Coordinate))
    zero_le_one (fun wave => ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun value => by
      change ‖polarization direction wave • value‖ ≤ 1*‖value‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (polarization_bound direction wave) (norm_nonneg _)))

theorem direction_bound (direction : Coordinate) (value : State) : ‖directionCLM direction value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro wave
  change ‖polarization direction wave • value wave‖ ≤ ‖value wave‖
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (polarization_bound direction wave)

def derivativeRead (index : Index) (direction : Coordinate) : State →L[ℝ] ScalarSequence :=
  (NativePairedCarrierJets.shiftedCLM index.1 index.2).comp (wholeVelocityCLM.comp (directionCLM direction))

theorem derivativeRead_bound (index : Index) (direction : Coordinate) (value : State) : ‖derivativeRead index direction value‖ ≤ ‖value‖ := by
  change ‖NativePairedCarrierJets.shifted (wholeVelocity (directionCLM direction value)) index.1 index.2‖ ≤ _
  rw [NativePairedCarrierJets.shifted_norm]
  apply (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun wave => norm_le_pi_norm (wholeVelocity (directionCLM direction value) wave) index.2)).trans
  exact (wholeVelocity_norm_le _).trans (direction_bound direction value)

theorem derivativeRead_original (index : Index) (direction : Coordinate) (value : wholePhysical) (regular : H1 value) (wave : IntegerWavevector) :
    derivativeRead index direction (gradientValue value regular) wave =
      multiplier (wave-index.1) direction*wholeVelocity value.1 (wave-index.1) index.2 := by
  change wholeVelocity (directionCLM direction (gradientValue value regular)) (wave-index.1) index.2 = _
  by_cases zero : wave-index.1 = 0
  · simp only [zero,wholeVelocity_zero,Pi.zero_apply,mul_zero]
  · rw [wholeVelocity_nonzero _ ⟨wave-index.1,zero⟩,wholeVelocity_nonzero _ ⟨wave-index.1,zero⟩]
    change polarization direction ⟨wave-index.1,zero⟩*
      (root (wave-index.1) • value.1 ⟨wave-index.1,zero⟩ index.2) = _
    simp only [polarization,Complex.real_smul]
    push_cast
    field_simp [(root_positive (wave-index.1) zero).ne']

def sampleDerivative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) (direction : Coordinate) (shift : ℝ) : ScalarSequence :=
  derivativeRead index direction (gradientState seed (time-shift))

theorem sampleDerivative_measurable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) (direction : Coordinate) :
    AEStronglyMeasurable (sampleDerivative seed time index direction) averageMeasure := by
  have moved := (gradientState_measurable seed).comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) time)
  exact ((derivativeRead index direction).continuous.comp_aestronglyMeasurable moved).mono_ac
    (withDensity_absolutelyContinuous volume (fun shift => (density shift : ℝ≥0∞)))

theorem sampleDerivative_square (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) (direction : Coordinate) (shift : ℝ) :
    ‖sampleDerivative seed time index direction shift‖^2 ≤ (2*Real.pi)^2*mass seed (time-shift) :=
  (pow_le_pow_left₀ (norm_nonneg _) (derivativeRead_bound index direction (gradientState seed (time-shift))) 2).trans
    (gradientState_square seed (time-shift))

theorem sampleDerivative_memLp (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    MemLp (sampleDerivative seed time index direction) 2 averageMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (sampleDerivative_measurable seed time index direction)).mpr
  apply ((weighted_mass_integrable seed time valid).const_mul ((2*Real.pi)^2)).mono'
    ((sampleDerivative_measurable seed time index direction).norm.pow 2)
  filter_upwards with shift
  change ‖‖sampleDerivative seed time index direction shift‖^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sampleDerivative_square seed time index direction shift

def jet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) : HistoryHilbert :=
  (sampleDerivative_memLp seed time valid index direction).toLp (sampleDerivative seed time index direction)

theorem jet_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    jet seed time valid index direction =ᵐ[averageMeasure] sampleDerivative seed time index direction :=
  (sampleDerivative_memLp seed time valid index direction).coeFn_toLp

theorem sampleDerivative_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    ∀ᵐ shift ∂averageMeasure, ∀ wave, sampleDerivative seed time index direction shift wave =
      multiplier (wave-index.1) direction*(sample seed time index shift) wave := by
  have moved := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae (physical_H1_ae seed)
  have original := (withDensity_absolutelyContinuous volume (fun shift => (density shift : ℝ≥0∞))).ae_le moved
  filter_upwards [original, NativeWindowHistoryGNS.average_support] with shift actual inside wave
  have nonnegative : 0 ≤ time-shift := by linarith
  rw [sampleDerivative,gradientState_original seed (time-shift) nonnegative (actual nonnegative),derivativeRead_original]
  rfl

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    HasDerivAt (fun displacement => NativeWindowHistoryTranslation.action index.1 direction displacement (history seed time index))
      (jet seed time valid index direction) 0 := by
  apply NativeWindowHistoryTranslation.action_hasDerivAt_zero
  filter_upwards [jet_ae seed time valid index direction,history_ae seed time index,sampleDerivative_read seed time valid index direction]
    with shift gradient original actual wave
  rw [gradient,original,actual]

theorem jet_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    ‖jet seed time valid index direction‖^2 ≤ (2*Real.pi)^2*ceiling*
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2) := by
  rw [NativeWindowHistoryTranslation.norm_square]
  have first := (sampleDerivative_memLp seed time valid index direction).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have same : (∫ shift, ‖jet seed time valid index direction shift‖^2 ∂averageMeasure) =
      ∫ shift, ‖sampleDerivative seed time index direction shift‖^2 ∂averageMeasure := by
    apply integral_congr_ae
    filter_upwards [jet_ae seed time valid index direction] with shift equal
    rw [equal]
  rw [same]
  have paid := integral_mono first ((weighted_mass_integrable seed time valid).const_mul ((2*Real.pi)^2))
    (sampleDerivative_square seed time index direction)
  rw [integral_const_mul] at paid
  exact paid.trans ((mul_le_mul_of_nonneg_left (weighted_mass_bound seed time valid) (sq_nonneg _)).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryGradient
