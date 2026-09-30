import H0mework.NavierStokes.UnheatedWriterSobolev.Stress

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowSobolevProduct
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeHigherTimeJets NativeMovingCriticalProductScalar NativeCompleteStressCarrier
open NativeUnheatedStressProduct
noncomputable section

theorem sum_mass (F : Finset IntegerWavevector) (left right : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0) (leftH1 : H1 left) (rightH1 : H1 right) :
    mass F (fun wave => (weight wave)⁻¹) (fun wave => amplitude left wave+amplitude right wave) ≤
      2*(gradientMass left+gradientMass right) := by
  have rows : mass F (fun wave => (weight wave)⁻¹) (fun wave => amplitude left wave+amplitude right wave) ≤
      2*(mass F (fun wave => (weight wave)⁻¹) (amplitude left)+mass F (fun wave => (weight wave)⁻¹) (amplitude right)) := by
    simp only [mass,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro wave _
    have scalar : 0 ≤ (weight wave)⁻¹ := inv_nonneg.mpr (weight_pos wave).le
    nlinarith [mul_nonneg scalar (sq_nonneg (amplitude left wave-amplitude right wave))]
  rw [finite_mass left leftZero,finite_mass right rightZero] at rows
  have first := leftH1.sum_le_tsum F (fun wave _ => density_nonnegative left wave)
  have last := rightH1.sum_le_tsum F (fun wave _ => density_nonnegative right wave)
  exact rows.trans (mul_le_mul_of_nonneg_left (add_le_add first last) (by norm_num))

theorem finite_row (F : Finset IntegerWavevector) (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖mixedFlux (complexSharpSupportProjection F left) (complexSharpSupportProjection F right) wave output input‖ ≤
      convolution F (fun wave => amplitude left wave+amplitude right wave)
        (fun wave => amplitude left wave+amplitude right wave) wave := by
  apply (finite_row_bound F left right wave output input).trans
  unfold convolution
  apply Finset.sum_le_sum
  intro first _
  split_ifs
  · exact mul_le_mul (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
      (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  · rfl

theorem finite_control (F : Finset IntegerWavevector) (left right : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0) (leftH1 : H1 left) (rightH1 : H1 right)
    (output input : Coordinate) :
    (∑ wave ∈ F, Real.sqrt (1+integerWaveNormSq wave)*
      ‖mixedFlux (complexSharpSupportProjection F left) (complexSharpSupportProjection F right) wave output input‖^2) ≤
        4*NativeUnheatedRieszKernel.constant*(gradientMass left+gradientMass right)^2 := by
  have paid := NativeUnheatedQuarticHalfEnvelope.finite_control F (fun wave => amplitude left wave+amplitude right wave)
  have normed := Finset.sum_le_sum (s := F) fun wave _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (finite_row F left right wave output input) 2)
      (Real.sqrt_nonneg (1+integerWaveNormSq wave))
  have nonnegative : 0 ≤ mass F (fun wave => (weight wave)⁻¹) (fun wave => amplitude left wave+amplitude right wave) :=
    Finset.sum_nonneg fun wave _ => mul_nonneg (inv_nonneg.mpr (weight_pos wave).le) (sq_nonneg _)
  have massBound := pow_le_pow_left₀ nonnegative (sum_mass F left right leftZero rightZero leftH1 rightH1) 2
  exact normed.trans (paid.trans ((mul_le_mul_of_nonneg_left massBound NativeUnheatedRieszKernel.constant_nonnegative).trans_eq (by ring)))

theorem observed_control (left right : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0) (leftH1 : H1 left) (rightH1 : H1 right)
    (F : Finset IntegerWavevector) (output input : Coordinate) :
    (∑ wave ∈ F, Real.sqrt (1+integerWaveNormSq wave)*‖mixedFlux left right wave output input‖^2) ≤
      4*NativeUnheatedRieszKernel.constant*(gradientMass left+gradientMass right)^2 := by
  have limit (wave : IntegerWavevector) : Tendsto (fun radius => Real.sqrt (1+integerWaveNormSq wave)*
      ‖mixedFlux (complexSharpSupportProjection (integerWaveFrequencyCube radius) left)
        (complexSharpSupportProjection (integerWaveFrequencyCube radius) right) wave output input‖^2)
        atTop (𝓝 (Real.sqrt (1+integerWaveNormSq wave)*‖mixedFlux left right wave output input‖^2)) := by
    have continuous : Continuous (fun pair : ComplexVorticityHilbertState × ComplexVorticityHilbertState =>
        mixedFlux pair.1 pair.2 wave output input) :=
      ((mixedFluxCLM wave output input).continuous.comp continuous_fst).clm_apply continuous_snd
    exact ((continuous.tendsto _ |>.comp ((complexSharpSupportProjection_frequencyCube_tendsto left).prodMk_nhds
      (complexSharpSupportProjection_frequencyCube_tendsto right))).norm.pow 2).const_mul _
  apply le_of_tendsto (tendsto_finsetSum F (fun wave _ => limit wave))
  have included : ∀ᶠ radius in atTop, F ⊆ integerWaveFrequencyCube radius :=
    (eventually_all_finset F).mpr fun wave _ => integerWave_eventually_mem_frequencyCube wave
  filter_upwards [included] with radius subset
  exact (Finset.sum_le_sum_of_subset_of_nonneg subset (fun wave _ _ =>
    mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))).trans
      (finite_control (integerWaveFrequencyCube radius) left right leftZero rightZero leftH1 rightH1 output input)

theorem tensor_bound (left right : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0) (leftH1 : H1 left) (rightH1 : H1 right)
    (F : Finset IntegerWavevector) :
    (∑ wave ∈ F, Real.sqrt (1+integerWaveNormSq wave)*‖tensor (mixedFlux left right wave)‖^2) ≤
      36*NativeUnheatedRieszKernel.constant*(gradientMass left+gradientMass right)^2 := by
  simp only [tensor_norm_sq,Finset.mul_sum]
  rw [Finset.sum_comm]
  have each (output : Coordinate) :
      (∑ wave ∈ F, ∑ input : Coordinate, Real.sqrt (1+integerWaveNormSq wave)*‖mixedFlux left right wave output input‖^2) ≤
        ∑ _input : Coordinate, 4*NativeUnheatedRieszKernel.constant*(gradientMass left+gradientMass right)^2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun input _ => observed_control left right leftZero rightZero leftH1 rightH1 F output input
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ => each output
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,
    ← mul_assoc,show (3 : ℝ)*3*4=36 by norm_num] using paid

theorem summable (left right : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0) (leftH1 : H1 left) (rightH1 : H1 right) :
    Summable (fun wave => Real.sqrt (1+integerWaveNormSq wave)*‖tensor (mixedFlux left right wave)‖^2) :=
  summable_of_sum_le (fun _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
    (tensor_bound left right leftZero rightZero leftH1 rightH1)

def state (left right : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0) (leftH1 : H1 left) (rightH1 : H1 right) : Space :=
  ⟨fun wave => NativeWindowSobolevStress.quarter wave • tensor (mixedFlux left right wave), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,NativeWindowSobolevStress.quarter_sq]
      using summable left right leftZero rightZero leftH1 rightH1⟩

theorem state_row (left right : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0) (leftH1 : H1 left) (rightH1 : H1 right)
    (wave : IntegerWavevector) (output input : Coordinate) :
    state left right leftZero rightZero leftH1 rightH1 wave (output,input) =
      NativeWindowSobolevStress.quarter wave • mixedFlux left right wave output input := rfl

theorem state_bound (left right : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0) (leftH1 : H1 left) (rightH1 : H1 right) :
    ‖state left right leftZero rightZero leftH1 rightH1‖ ≤
      6*Real.sqrt NativeUnheatedRieszKernel.constant*(gradientMass left+gradientMass right) := by
  have masses : 0 ≤ gradientMass left+gradientMass right := add_nonneg
    (tsum_nonneg (density_nonnegative left)) (tsum_nonneg (density_nonnegative right))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have normed := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (state left right leftZero rightZero leftH1 rightH1)
  have row (wave : IntegerWavevector) : state left right leftZero rightZero leftH1 rightH1 wave =
      NativeWindowSobolevStress.quarter wave • tensor (mixedFlux left right wave) := rfl
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,row,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,NativeWindowSobolevStress.quarter_sq] at normed
  rw [normed]
  have paid := (summable left right leftZero rightZero leftH1 rightH1).tsum_le_of_sum_le
    (tensor_bound left right leftZero rightZero leftH1 rightH1)
  convert paid using 1
  rw [mul_pow,mul_pow,Real.sq_sqrt NativeUnheatedRieszKernel.constant_nonnegative]
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowSobolevProduct
