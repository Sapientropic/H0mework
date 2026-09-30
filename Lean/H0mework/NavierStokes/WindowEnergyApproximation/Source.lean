import H0mework.NavierStokes.UnheatedWriterSobolev.Product
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowFiniteStressConvergence
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeEndpointVelocityCarrier NativeCompleteStressCarrier NativeHigherTimeJets
open NativeUnheatedStressProduct NativeMovingCriticalProductScalar
open NativeWindowSobolevStress (quarter quarter_nonnegative quarter_sq)
noncomputable section

def finite (value : WholeRestartVelocityEndpointState) (F : Finset IntegerWavevector) : Space :=
  NativeWindowSobolevProduct.state (complexSharpSupportProjection F (wholeVelocity value))
    (complexSharpSupportProjection F (wholeVelocity value))
    (projection_zero F _ (wholeVelocity_zero value)) (projection_zero F _ (wholeVelocity_zero value))
    (projection_H1 F _) (projection_H1 F _)

def full (value : WholeRestartVelocityEndpointState) (regular : H1 (wholeVelocity value)) : Space :=
  NativeWindowSobolevProduct.state (wholeVelocity value) (wholeVelocity value)
    (wholeVelocity_zero value) (wholeVelocity_zero value) regular regular

theorem finite_row (value : WholeRestartVelocityEndpointState) (F : Finset IntegerWavevector) (wave : IntegerWavevector) :
    finite value F wave = quarter wave • tensor (mixedFlux (complexSharpSupportProjection F (wholeVelocity value))
      (complexSharpSupportProjection F (wholeVelocity value)) wave) := rfl

theorem full_row (value : WholeRestartVelocityEndpointState) (regular : H1 (wholeVelocity value)) (wave : IntegerWavevector) :
    full value regular wave = quarter wave • tensor (mixedFlux (wholeVelocity value) (wholeVelocity value) wave) := rfl

theorem finite_supported (value : WholeRestartVelocityEndpointState) (F : Finset IntegerWavevector)
    (wave : IntegerWavevector) (outside : wave ∉ F+F) : finite value F wave = 0 := by
  rw [finite_row]
  have zero : mixedFlux (complexSharpSupportProjection F (wholeVelocity value))
      (complexSharpSupportProjection F (wholeVelocity value)) wave = 0 := by
    funext output input
    change -(∑' first, complexSharpSupportProjection F (wholeVelocity value) first input*
      complexSharpSupportProjection F (wholeVelocity value) (wave-first) output) = 0
    suffices all : ∀ first, complexSharpSupportProjection F (wholeVelocity value) first input*
        complexSharpSupportProjection F (wholeVelocity value) (wave-first) output = 0 by simp only [all,tsum_zero,neg_zero]
    intro first
    by_cases member : first ∈ F
    · have last : wave-first ∉ F := fun present => outside
        (Finset.mem_add.mpr ⟨first,member,wave-first,present,by abel⟩)
      simp [last]
    · simp [member]
  rw [zero]
  change quarter wave • (0 : Tensor) = 0
  exact smul_zero _

theorem tensor_majorant (stress : ThreeDimensionalVorticityCoefficientNativeFluidMedium.NativeFluidStressCoefficient)
    (bound : ℝ) (nonnegative : 0 ≤ bound) (rows : ∀ output input, ‖stress output input‖ ≤ bound) :
    ‖tensor stress‖ ≤ 3*bound := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [tensor_norm_sq]
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ =>
      pow_le_pow_left₀ (norm_nonneg _) (rows output input) 2
  convert! paid using 1
  simp
  ring

theorem finite_envelope (value : NativeWholeResolvent.wholePhysical) (F : Finset IntegerWavevector)
    (wave : IntegerWavevector) : ‖finite value.1 F wave‖ ≤
      3*quarter wave*NativeUnheatedQuarticEnvelope.row value wave := by
  rw [finite_row,norm_smul,Real.norm_of_nonneg (quarter_nonnegative wave)]
  have rows (output input : Coordinate) : ‖mixedFlux (complexSharpSupportProjection F (wholeVelocity value.1))
      (complexSharpSupportProjection F (wholeVelocity value.1)) wave output input‖ ≤ NativeUnheatedQuarticEnvelope.row value wave := by
    apply (finite_row_bound F _ _ wave output input).trans
    unfold NativeMovingCriticalProductScalar.convolution
    apply (Finset.sum_le_sum fun first _ => show (if wave-first ∈ F then _ else 0) ≤
      amplitude (wholeVelocity value.1) first*amplitude (wholeVelocity value.1) (wave-first) by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    exact (NativeUnheatedQuarticEnvelope.pair_summable value wave).sum_le_tsum F (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_mul_of_nonneg_left (tensor_majorant _ _ (NativeUnheatedQuarticEnvelope.row_nonnegative value wave) rows)
    (quarter_nonnegative wave)).trans_eq (by ring)

theorem full_envelope (value : NativeWholeResolvent.wholePhysical) (regular : H1 (wholeVelocity value.1))
    (wave : IntegerWavevector) : ‖full value.1 regular wave‖ ≤
      3*quarter wave*NativeUnheatedQuarticEnvelope.row value wave := by
  rw [full_row,norm_smul,Real.norm_of_nonneg (quarter_nonnegative wave)]
  exact (mul_le_mul_of_nonneg_left (tensor_majorant _ _ (NativeUnheatedQuarticEnvelope.row_nonnegative value wave)
    (NativeUnheatedHalfNonlinear.flux_row_bound value wave)) (quarter_nonnegative wave)).trans_eq (by ring)

theorem row_tendsto (value : WholeRestartVelocityEndpointState) (regular : H1 (wholeVelocity value)) (wave : IntegerWavevector) :
    Tendsto (fun radius => finite value (integerWaveFrequencyCube radius) wave) atTop (𝓝 (full value regular wave)) := by
  let observer : Space →L[ℝ] Tensor := (quarter wave*(weight wave)⁻¹) • lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave
  have continuous : Continuous (fun input : ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.ComplexVorticityHilbertState =>
      observer (NativeCompleteStressBilinear.mixed input input)) :=
    observer.continuous.comp (NativeCompleteStressBilinear.mixedCLM.continuous.clm_apply continuous_id)
  have actual := continuous.tendsto (wholeVelocity value) |>.comp (complexSharpSupportProjection_frequencyCube_tendsto (wholeVelocity value))
  have readout (input : ComplexVorticityHilbertState) : observer (NativeCompleteStressBilinear.mixed input input) =
      quarter wave • tensor (mixedFlux input input wave) := by
    have generated := NativeCompleteStressBilinear.mixed_read input input
    ext entry
    have row := congrFun (congrFun (congrFun generated wave) entry.1) entry.2
    change (weight wave)⁻¹ • NativeCompleteStressBilinear.mixed input input wave entry = _ at row
    change (quarter wave*(weight wave)⁻¹) • NativeCompleteStressBilinear.mixed input input wave entry = _
    rw [mul_smul,row]
    rfl
  simpa only [Function.comp_def,readout,finite_row,full_row] using actual

theorem strong_tendsto (value : NativeWholeResolvent.wholePhysical) (regular : NativeWholeH1Mixed.H1 value) :
    Tendsto (fun radius => finite value.1 (integerWaveFrequencyCube radius)) atTop
      (𝓝 (full value.1 regular)) := by
  let bound (wave : IntegerWavevector) := (6*quarter wave*NativeUnheatedQuarticEnvelope.row value wave)^2
  have paid : Summable bound := by
    have h := (NativeUnheatedQuarticHalfEnvelope.square_summable value regular).mul_left 36
    convert! h using 1
    funext wave
    simp only [bound,mul_pow,quarter_sq]
    ring
  have point (wave : IntegerWavevector) : Tendsto (fun radius =>
      ‖(finite value.1 (integerWaveFrequencyCube radius)-full value.1 regular) wave‖^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [lp.coeFn_sub,Pi.sub_apply,sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((row_tendsto value.1 regular wave).sub_const (full value.1 regular wave)).norm.pow 2
  have dominated (radius : ℕ) (wave : IntegerWavevector) :
      ‖‖(finite value.1 (integerWaveFrequencyCube radius)-full value.1 regular) wave‖^2‖ ≤ bound wave := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans ((add_le_add (finite_envelope value _ wave) (full_envelope value regular wave)).trans_eq (by ring))
  have limit := tendsto_tsum_of_dominated_convergence paid point (Eventually.of_forall dominated)
  have normed (radius : ℕ) : (∑' wave, ‖(finite value.1 (integerWaveFrequencyCube radius)-full value.1 regular) wave‖^2) =
      ‖finite value.1 (integerWaveFrequencyCube radius)-full value.1 regular‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (finite value.1 (integerWaveFrequencyCube radius)-full value.1 regular)).tsum_eq
  simp only [tsum_zero] at limit
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,normed,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using Real.continuous_sqrt.tendsto 0 |>.comp limit

variable {nu : Viscosity}

def finiteAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : Space :=
  finite (NativeAbsoluteEventualControl.velocity seed time) F

def source (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Space := by
  classical
  exact if regular : H1 (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) then
    full (NativeUnifiedCompleteSource.source seed time).fst regular else 0

theorem source_tendsto_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → Tendsto (fun radius => finiteAt seed (integerWaveFrequencyCube radius) time) atTop (𝓝 (source seed time)) := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with time regular nonnegative
  have actual := strong_tendsto (NativeUnheatedSourceGradient.physical seed time nonnegative) (regular nonnegative)
  have h : H1 (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := regular nonnegative
  simpa only [source,dif_pos h,finiteAt,NativeUnheatedSourceGradient.physical,NativeUnifiedCompleteSource.velocity_read] using actual

theorem source_row_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ wave, source seed time wave =
      quarter wave • tensor (read (NativeUnifiedCompleteSource.source seed time).snd wave) := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed,NativeUnifiedGlobalStressSource.stress_ae seed]
    with time regular stress nonnegative wave
  have h : H1 (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := regular nonnegative
  rw [source,dif_pos h,full_row,mixedFlux_diagonal,NativeUnifiedCompleteSource.velocity_read,NativeUnifiedCompleteSource.stress_read,stress]

def weightedRead (wave : IntegerWavevector) : Space →L[ℝ] Tensor :=
  (quarter wave*(weight wave)⁻¹) • lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave

theorem finiteAt_row (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) (wave : IntegerWavevector) :
    finiteAt seed F time wave = weightedRead wave (NativeUnheatedWindowStress.finiteStress seed F time) := by
  rw [finiteAt,finite_row]
  ext entry
  have row := congrFun (congrFun (congrFun (NativeCompleteStressBilinear.mixed_read
    (NativeUnheatedWindowStress.projection seed F time) (NativeUnheatedWindowStress.projection seed F time)) wave) entry.1) entry.2
  change (weight wave)⁻¹ • NativeUnheatedWindowStress.finiteStress seed F time wave entry = _ at row
  change quarter wave • mixedFlux _ _ wave entry.1 entry.2 = (quarter wave*(weight wave)⁻¹) •
    NativeUnheatedWindowStress.finiteStress seed F time wave entry
  rw [mul_smul,row]
  rfl

theorem finiteAt_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) : Continuous (finiteAt seed F) := by
  have series : finiteAt seed F = fun time => ∑ wave ∈ F+F, lp.single 2 wave
      (weightedRead wave (NativeUnheatedWindowStress.finiteStress seed F time)) := by
    funext time
    apply lp.ext
    funext wave
    rw [lp.coeFn_sum,Finset.sum_apply]
    simp only [lp.coeFn_single,Finset.sum_pi_single]
    split_ifs with inside
    · exact finiteAt_row seed F time wave
    · exact finite_supported _ F wave inside
  rw [series]
  exact continuous_finsetSum _ fun wave _ =>
    (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => Tensor) 2 wave).continuous.comp
      ((weightedRead wave).continuous.comp (NativeUnheatedWindowStress.finiteStress_continuous seed F))

def cap : ℝ := 12*Real.sqrt NativeUnheatedRieszKernel.constant

theorem cap_nonnegative : 0 ≤ cap := by unfold cap; positivity

theorem finite_bound (value : NativeWholeResolvent.wholePhysical) (regular : NativeWholeH1Mixed.H1 value) (F : Finset IntegerWavevector) :
    ‖finite value.1 F‖ ≤ cap*NativeWholeH1Mixed.gradientMass value := by
  have paid := NativeWindowSobolevProduct.state_bound (complexSharpSupportProjection F (wholeVelocity value.1))
    (complexSharpSupportProjection F (wholeVelocity value.1))
    (projection_zero F _ (wholeVelocity_zero value.1)) (projection_zero F _ (wholeVelocity_zero value.1))
    (projection_H1 F _) (projection_H1 F _)
  rw [projection_mass] at paid
  have sum : (∑ wave ∈ F, density (wholeVelocity value.1) wave) ≤ NativeWholeH1Mixed.gradientMass value :=
    regular.sum_le_tsum F (fun _ _ => mul_nonneg (integerWaveNormSq_nonneg _) (sq_nonneg _))
  exact paid.trans ((mul_le_mul_of_nonneg_left (add_le_add sum sum) (by positivity)).trans_eq (by unfold cap; ring))

theorem source_bound_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ‖source seed time‖ ≤ cap*NativeUnheatedSourceGradient.mass seed time ∧
      ∀ F, ‖finiteAt seed F time‖ ≤ cap*NativeUnheatedSourceGradient.mass seed time := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with time regular nonnegative
  have h : H1 (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := regular nonnegative
  constructor
  · rw [source,dif_pos h]
    have paid := NativeWindowSobolevProduct.state_bound _ _ (wholeVelocity_zero _) (wholeVelocity_zero _) h h
    have mass : gradientMass (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) =
        NativeUnheatedSourceGradient.mass seed time := NativeUnheatedSourceGradient.physical_mass seed time nonnegative
    exact paid.trans_eq (by rw [mass]; unfold cap; ring)
  · intro F
    have paid := finite_bound (NativeUnheatedSourceGradient.physical seed time nonnegative) (regular nonnegative) F
    rw [NativeUnheatedSourceGradient.physical_mass] at paid
    simpa only [finiteAt,NativeUnheatedSourceGradient.physical,NativeUnifiedCompleteSource.velocity_read] using paid

theorem source_measurable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    AEStronglyMeasurable (source seed) (volume.restrict (Icc 0 horizon)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun radius => (finiteAt_continuous seed (integerWaveFrequencyCube radius)).aestronglyMeasurable)
  filter_upwards [ae_restrict_of_ae (source_tendsto_ae seed),ae_restrict_mem measurableSet_Icc] with time actual inside
  exact actual inside.1

theorem source_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (source seed) (volume.restrict (Icc 0 horizon)) := by
  apply ((NativeUnheatedSourceGradient.mass_integrable seed horizon nonnegative).const_mul cap).mono'
    (source_measurable seed horizon)
  filter_upwards [ae_restrict_of_ae (source_bound_ae seed),ae_restrict_mem measurableSet_Icc] with time actual inside
  exact (actual inside.1).1

end
end SaturationMonoid.NavierStokes.NativeWindowFiniteStressConvergence
