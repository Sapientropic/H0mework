import H0mework.Versions.X.NavierStokes.UnheatedWriterHalf.Source
import H0mework.Versions.X.NavierStokes.WindowEnergyApproximation.Source

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowCutoffHalfAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open NativeResolventCompactness NativeCompleteStressCarrier NativeCompleteStressAction NativeTimeJetCarrier
open NativeUnheatedPairNegativeKernel NativeEndpointVelocityCarrier
noncomputable section

def factor (wave : NonzeroIntegerWavevector) : ℝ :=
  (NativeUnheatedHalfNonlinear.quarter wave.1*NativeWindowSobolevStress.quarter wave.1)⁻¹

theorem factor_bound (wave : NonzeroIntegerWavevector) :
    factor wave^2*integerWaveViscousMultiplier wave.1 ≤ 2*Real.pi := by
  have first := Real.sqrt_pos.mpr (root_positive wave.1 wave.2)
  change 0 < NativeUnheatedHalfNonlinear.quarter wave.1 at first
  have last := NativeWindowSobolevStress.quarter_positive wave.1
  calc
    _ = root wave.1/(NativeWindowSobolevStress.quarter wave.1)^2 := by
      rw [factor,inv_pow,mul_pow,NativeUnheatedHalfNonlinear.quarter_sq,← root_sq]
      field_simp [(root_positive wave.1 wave.2).ne',last.ne']
    _ ≤ 2*Real.pi := by
      apply (div_le_iff₀ (sq_pos_of_pos last)).mpr
      rw [NativeWindowSobolevStress.quarter_sq]
      exact NativeUnheatedHalfNonlinear.root_bound wave.1

def row (wave : NonzeroIntegerWavevector) : Tensor →L[ℝ] ComplexCoordinateEuclidean :=
  factor wave • (euclideanCLM.comp ((projectedDivergenceCLM wave.1).comp untensorCLM))

def cap : ℝ := Real.sqrt (2*Real.pi)
theorem cap_positive : 0 < cap := Real.sqrt_pos.mpr (by positivity)

theorem row_bound (wave : NonzeroIntegerWavevector) (value : Tensor) : ‖row wave value‖ ≤ cap*‖value‖ := by
  have original := (transverseProjection_amplitudeSq_le wave.1 wave.2
    (nativeFluidStressDivergenceCoefficient (fun _ => untensor value) wave.1)).trans
      (NativeFullOrderStress.divergence_amplitude_le (fun _ => untensor value) wave.1)
  have tensorSquare : (∑ output : Coordinate, ∑ input : Coordinate,
      Complex.normSq (untensor value output input)) = ‖value‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type]
    simp only [untensor,Complex.normSq_eq_norm_sq]
  rw [tensorSquare] at original
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg cap_positive.le (norm_nonneg _))).mp
  change ‖factor wave • euclideanCoordinateRow
    (transverseProjection wave.1 (nativeFluidStressDivergenceCoefficient (fun _ => untensor value) wave.1))‖^2 ≤ _
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,euclideanCoordinateRow_norm_sq]
  apply (mul_le_mul_of_nonneg_left original (sq_nonneg (factor wave))).trans
  have paid := mul_le_mul_of_nonneg_right (factor_bound wave) (sq_nonneg ‖value‖)
  simpa only [cap,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi),mul_assoc] using paid

def action (value : Space) : State :=
  ⟨fun wave => row wave (value wave.1),memℓp_gen (by
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    have source := (lp.hasSum_norm (p := (2:ℝ≥0∞)) (by norm_num) value).summable
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at source
    exact ((source.subtype (fun wave => wave ≠ 0)).mul_left (cap^2)).of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun wave => by simpa only [mul_pow,Function.comp_def] using! pow_le_pow_left₀ (norm_nonneg _) (row_bound wave (value wave.1)) 2))⟩

theorem action_bound (value : Space) : ‖action value‖ ≤ cap*‖value‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg cap_positive.le (norm_nonneg _))).mp
  have source := lp.hasSum_norm (p := (2:ℝ≥0∞)) (by norm_num) value
  have target := lp.hasSum_norm (p := (2:ℝ≥0∞)) (by norm_num) (action value)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at source target
  rw [target.tsum_eq.symm,mul_pow]
  calc
    _ ≤ ∑' wave : NonzeroIntegerWavevector, cap^2*‖value wave.1‖^2 :=
      target.summable.tsum_le_tsum (fun wave => by
        change ‖row wave (value wave.1)‖^2 ≤ _
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (row_bound wave (value wave.1)) 2)
        ((source.summable.subtype (fun wave => wave ≠ 0)).mul_left (cap^2))
    _ = cap^2*∑' wave : NonzeroIntegerWavevector, ‖value wave.1‖^2 := tsum_mul_left
    _ ≤ cap^2*‖value‖^2 := by
      rw [← source.tsum_eq]
      exact mul_le_mul_of_nonneg_left
        (source.summable.tsum_subtype_le _ {wave | wave ≠ 0} (fun _ => sq_nonneg _)) (sq_nonneg _)

def actionCLM : Space →L[ℝ] State :=
  LinearMap.mkContinuous
    { toFun := action
      map_add' := fun first last => by apply lp.ext; funext wave; exact (row wave).map_add _ _
      map_smul' := fun scalar value => by apply lp.ext; funext wave; exact (row wave).map_smul scalar _ }
    cap action_bound

theorem decode_action (value : Space) (wave : IntegerWavevector) (coordinate : Coordinate) :
    NativeUnheatedHalfNonlinear.decode wave coordinate (actionCLM value) =
      projectedDivergenceCLM wave ((NativeWindowSobolevStress.quarter wave)⁻¹ • untensor (value wave)) coordinate := by
  by_cases zero : wave=0
  · subst wave
    simp only [NativeUnheatedHalfNonlinear.decode,smul_apply,ContinuousLinearMap.comp_apply,
      wholeVelocityCLM,projectedDivergenceCLM_apply]
    simp [NativeUnheatedHalfNonlinear.quarter,root,integerWaveViscousMultiplier,integerWaveNormSq,transverseProjection]
  · have first := Real.sqrt_pos.mpr (root_positive wave zero)
    change 0 < NativeUnheatedHalfNonlinear.quarter wave at first
    change NativeUnheatedHalfNonlinear.quarter wave • wholeVelocity (actionCLM value) wave coordinate = _
    rw [wholeVelocity_nonzero _ ⟨wave,zero⟩,map_smul]
    change NativeUnheatedHalfNonlinear.quarter wave •
      (factor ⟨wave,zero⟩ • projectedDivergenceCLM wave (untensor (value wave)) coordinate) = _
    rw [smul_smul]
    congr 1
    unfold factor
    field_simp [first.ne',(NativeWindowSobolevStress.quarter_positive wave).ne']
    change 1 = NativeWindowSobolevStress.quarter wave*(NativeWindowSobolevStress.quarter wave)⁻¹
    rw [mul_inv_cancel₀ (NativeWindowSobolevStress.quarter_positive wave).ne']

theorem full_existing (value : NativeWholeResolvent.wholePhysical) (regular : NativeWholeH1Mixed.H1 value) :
    actionCLM (NativeWindowFiniteStressConvergence.full value.1 regular) = NativeUnheatedHalfNonlinear.ofPhysical value regular := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  change factor wave • (projectedDivergenceCLM wave.1
      (NativeWindowSobolevStress.quarter wave.1 • NativeHigherTimeJets.mixedFlux (wholeVelocity value.1) (wholeVelocity value.1) wave.1) coordinate) =
    NativeUnheatedHalfNonlinear.quarter wave.1 •
      ((root wave.1)⁻¹ • projectedDivergenceCLM wave.1
        (NativeHigherTimeJets.mixedFlux (wholeVelocity value.1) (wholeVelocity value.1) wave.1) coordinate)
  rw [map_smul,Pi.smul_apply,smul_smul,smul_smul]
  congr 1
  have positive : 0 < NativeUnheatedHalfNonlinear.quarter wave.1 := Real.sqrt_pos.mpr (root_positive wave.1 wave.2)
  unfold factor
  rw [← NativeUnheatedHalfNonlinear.quarter_sq]
  field_simp [positive.ne',(NativeWindowSobolevStress.quarter_positive wave.1).ne']

theorem finite_read (value : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.WholeRestartVelocityEndpointState)
    (F : Finset IntegerWavevector) (wave : IntegerWavevector) (coordinate : Coordinate) :
    NativeUnheatedHalfNonlinear.decode wave coordinate (actionCLM (NativeWindowFiniteStressConvergence.finite value F)) =
      projectedDivergenceCLM wave (NativeHigherTimeJets.mixedFlux (complexSharpSupportProjection F (wholeVelocity value))
        (complexSharpSupportProjection F (wholeVelocity value)) wave) coordinate := by
  rw [decode_action,NativeWindowFiniteStressConvergence.finite_row]
  have source : (NativeWindowSobolevStress.quarter wave)⁻¹ •
      untensor (NativeWindowSobolevStress.quarter wave • tensor
        (NativeHigherTimeJets.mixedFlux (complexSharpSupportProjection F (wholeVelocity value))
          (complexSharpSupportProjection F (wholeVelocity value)) wave)) =
      NativeHigherTimeJets.mixedFlux (complexSharpSupportProjection F (wholeVelocity value))
        (complexSharpSupportProjection F (wholeVelocity value)) wave := by
    funext output input
    change (NativeWindowSobolevStress.quarter wave)⁻¹ • (NativeWindowSobolevStress.quarter wave • (_ : ℂ)) = _
    exact inv_smul_smul₀ (NativeWindowSobolevStress.quarter_positive wave).ne' _
  rw [source]

end
end SaturationMonoid.NavierStokes.NativeWindowCutoffHalfAction
