import H0mework.NavierStokes.StressMovingSource.ProductPhysical
import H0mework.NavierStokes.UnheatedWriterTree.HeatKernel
import H0mework.NavierStokes.WindowHistory.Gradient
import H0mework.NavierStokes.UnheatedWriterTriad.Sum

set_option autoImplicit false
open scoped BigOperators Matrix ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowPressureLowKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeStressCurlAlgebra NativeUnheatedSexticLatticePower
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing NativeEndpointVelocityCarrier
noncomputable section

def tensor (first last : ComplexCoordinateVector) (output input : Coordinate) : ℂ := -first input*last output

def pair (first last : IntegerWavevector) (x y : ComplexCoordinateVector) (output : Coordinate) : ℂ :=
  -(Complex.I*(2*Real.pi : ℝ)*stressPressureCoefficient (first+last) (tensor x y))*complexWavevector (first+last) output

theorem contraction (first last : IntegerWavevector) (x y : ComplexCoordinateVector)
    (transverse : complexWavevector last ⬝ᵥ y = 0) :
    stressPressureCoefficient (first+last) (tensor x y) =
      if first+last=0 then 0 else
        -((complexWavevector (first+last) ⬝ᵥ x)*(complexWavevector first ⬝ᵥ y))/(integerWaveNormSq (first+last) : ℂ) := by
  have dot : complexWavevector (first+last) ⬝ᵥ y = complexWavevector first ⬝ᵥ y := by
    have add : complexWavevector (first+last) = complexWavevector first+complexWavevector last := by
      funext coordinate
      simp [complexWavevector]
    rw [add,add_dotProduct,transverse,add_zero]
  unfold stressPressureCoefficient
  split_ifs with zero
  · rfl
  · congr 1
    have algebra : complexWavevector (first+last) ⬝ᵥ
        (fun i => ∑ j : Coordinate, complexWavevector (first+last) j*tensor x y i j) =
        -((complexWavevector (first+last) ⬝ᵥ x)*(complexWavevector (first+last) ⬝ᵥ y)) := by
      simp only [tensor,dotProduct,Fin.sum_univ_three]
      ring
    rw [algebra,dot]

theorem dot_bound (wave : IntegerWavevector) (x : ComplexCoordinateVector) :
    ‖complexWavevector wave ⬝ᵥ x‖^2 ≤ 3*integerWaveNormSq wave*‖x‖^2 := by
  have paid := (complexWavevector_dot_normSq_le wave x).trans
    (mul_le_mul_of_nonneg_left (complexCoordinateAmplitudeSq_le_three_mul_norm_sq x) (integerWaveNormSq_nonneg wave))
  simpa only [Complex.normSq_eq_norm_sq,mul_assoc,mul_left_comm] using paid

theorem coordinate_bound (wave : IntegerWavevector) (output : Coordinate) :
    (wave output : ℝ)^2 ≤ integerWaveNormSq wave :=
  Finset.single_le_sum (fun other _ => sq_nonneg (wave other : ℝ)) (Finset.mem_univ output)

theorem pair_bound (first last : IntegerWavevector) (x y : ComplexCoordinateVector)
    (transverse : complexWavevector last ⬝ᵥ y = 0) (output : Coordinate) :
    ‖pair first last x y output‖ ≤ (3*(2*Real.pi)*Real.sqrt (integerWaveNormSq first))*‖x‖*‖y‖ := by
  by_cases zero : first+last=0
  · simp only [pair,stressPressureCoefficient,if_pos zero,mul_zero,neg_zero,zero_mul,norm_zero]
    positivity [integerWaveNormSq_nonneg first]
  have positive := integerWaveNormSq_pos zero
  have firstBound := dot_bound (first+last) x
  have lastBound := dot_bound first y
  have outputBound := coordinate_bound (first+last) output
  have square := mul_le_mul (mul_le_mul firstBound lastBound (sq_nonneg _) (by positivity : 0 ≤ 3*integerWaveNormSq (first+last)*‖x‖^2))
    outputBound (sq_nonneg _) (by positivity [integerWaveNormSq_nonneg first] : 0 ≤ (3*integerWaveNormSq (first+last)*‖x‖^2)*(3*integerWaveNormSq first*‖y‖^2))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity [integerWaveNormSq_nonneg first])).mp
  rw [pair,contraction first last x y transverse,if_neg zero]
  simp only [norm_mul,norm_neg,norm_div,Complex.norm_I,one_mul,Complex.norm_real,
    Real.norm_of_nonneg (le_of_lt (by positivity : 0 < 2*Real.pi)),Real.norm_of_nonneg positive.le,
    complexWavevector,Real.norm_eq_abs,mul_pow,div_pow,sq_abs,Real.sq_sqrt (integerWaveNormSq_nonneg first)]
  rw [← mul_div_assoc,div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos positive)).mpr
  convert! mul_le_mul_of_nonneg_left square (sq_nonneg (2*Real.pi)) using 1 <;> ring

theorem radical_shift (first last : IntegerWavevector) :
    radical (first+last) ≤ 2*radical first*radical last := by
  apply (pow_le_pow_iff_left₀ (radical_positive _).le (by positivity [radical_positive first,radical_positive last]) (by decide : (4:ℕ) ≠ 0)).mp
  rw [mul_pow,mul_pow,radical_fourth,radical_fourth,radical_fourth]
  have bound := NativeUnheatedTreeHeatKernel.mass_add first last
  have firstOne := mass_one first
  have lastOne := mass_one last
  nlinarith only [bound,firstOne,lastOne,mul_nonneg (sub_nonneg.mpr firstOne) (sub_nonneg.mpr lastOne)]

def cap (first : IntegerWavevector) : ℝ := 6*(2*Real.pi)*Real.sqrt (integerWaveNormSq first)*radical first

theorem cap_nonnegative (first : IntegerWavevector) : 0 ≤ cap first := by
  unfold cap
  positivity [radical_positive first]

theorem weighted_bound (first last : IntegerWavevector) (x y : ComplexCoordinateVector)
    (transverse : complexWavevector last ⬝ᵥ y = 0) (output : Coordinate) :
    radical (first+last)*‖pair first last x y output‖ ≤ cap first*‖x‖*(radical last*‖y‖) := by
  have paid := mul_le_mul (radical_shift first last) (pair_bound first last x y transverse output)
    (norm_nonneg _) (by positivity [radical_positive first,radical_positive last])
  exact paid.trans_eq (by unfold cap; ring)

theorem radical_le_root (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    radical wave ≤ NativeUnheatedPairNegativeKernel.root wave := by
  have size := ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy.one_le_integerWaveNormSq ⟨wave,nonzero⟩
  have one := mass_one wave
  have square := Real.sq_sqrt (mass_positive wave).le
  have sqrtBound : Real.sqrt (mass wave) ≤ mass wave := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mass_positive wave).le).mp
    nlinarith
  apply (sq_le_sq₀ (radical_positive wave).le (NativeUnheatedPairNegativeKernel.root_nonnegative wave)).mp
  rw [radical_square,NativeUnheatedPairNegativeKernel.root_sq]
  have constant : (2:ℝ) ≤ (2*Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  have scaled := mul_le_mul_of_nonneg_right constant (integerWaveNormSq_nonneg wave)
  change Real.sqrt (mass wave) ≤ (2*Real.pi)^2*integerWaveNormSq wave
  dsimp only [mass] at sqrtBound
  change Real.sqrt (1+integerWaveNormSq wave) ≤ _
  change 1 ≤ integerWaveNormSq wave at size
  linarith

theorem weighted_velocity (value : wholePhysical) (regular : H1 value) (wave : IntegerWavevector) :
    radical wave*‖wholeVelocity value.1 wave‖ ≤ ‖wholeVelocity (gradientValue value regular) wave‖ := by
  by_cases zero : wave=0
  · simp only [zero,wholeVelocity_zero,norm_zero,mul_zero,le_refl]
  · have read (input : State) : wholeVelocity input wave = fun i => input ⟨wave,zero⟩ i :=
      funext (wholeVelocity_nonzero input ⟨wave,zero⟩)
    rw [read,read]
    change radical wave*‖fun i => value.1 ⟨wave,zero⟩ i‖ ≤
      ‖Real.sqrt (integerWaveViscousMultiplier wave) • (fun i => value.1 ⟨wave,zero⟩ i)‖
    rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (radical_le_root wave zero) (norm_nonneg _)

abbrev Scalar := lp (fun _ : IntegerWavevector => ℝ) 2

def shift (value : Scalar) (wave : IntegerWavevector) : Scalar :=
  ⟨fun k => value (k-wave), memℓp_gen (by
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    have paid := (lp.hasSum_norm (p := (2:ℝ≥0∞)) (by norm_num) value).summable
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at paid
    exact paid.comp_injective (fun _ _ equal => sub_left_injective equal))⟩

theorem shift_norm (value : Scalar) (wave : IntegerWavevector) : ‖shift value wave‖ = ‖value‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have first := lp.norm_rpow_eq_tsum (p := (2:ℝ≥0∞)) (by norm_num) (shift value wave)
  have last := lp.norm_rpow_eq_tsum (p := (2:ℝ≥0∞)) (by norm_num) value
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at first last
  rw [first,last,← (Equiv.addRight wave).tsum_eq]
  simp only [shift,Equiv.coe_addRight,add_sub_cancel_right]

def rows (value : wholePhysical) (L : Finset IntegerWavevector) (output : Coordinate) (wave : IntegerWavevector) : ℂ :=
  ∑ first ∈ L, pair first (wave-first) (wholeVelocity value.1 first) (wholeVelocity value.1 (wave-first)) output

def majorant (value : wholePhysical) (regular : H1 value) (L : Finset IntegerWavevector) : Scalar :=
  ∑ first ∈ L, (cap first*‖wholeVelocity value.1 first‖) •
    shift (NativeUnheatedTriadSum.rowNorms (wholeVelocity (gradientValue value regular))) first

theorem majorant_apply (value : wholePhysical) (regular : H1 value) (L : Finset IntegerWavevector) (wave : IntegerWavevector) :
    majorant value regular L wave = ∑ first ∈ L, cap first*‖wholeVelocity value.1 first‖*
      ‖wholeVelocity (gradientValue value regular) (wave-first)‖ := by
  simp only [majorant,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  rfl

theorem rows_bound (value : wholePhysical) (regular : H1 value) (L : Finset IntegerWavevector)
    (output : Coordinate) (wave : IntegerWavevector) :
    ‖(radical wave : ℂ)*rows value L output wave‖ ≤ majorant value regular L wave := by
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (radical_positive wave).le,rows,majorant_apply]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (radical_positive wave).le).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  have paid := weighted_bound first (wave-first) (wholeVelocity value.1 first) (wholeVelocity value.1 (wave-first))
    (whole_transverse value (wave-first)) output
  rw [show first+(wave-first)=wave by abel] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (weighted_velocity value regular (wave-first))
    (mul_nonneg (cap_nonnegative first) (norm_nonneg _)))

def space (value : wholePhysical) (regular : H1 value) (L : Finset IntegerWavevector) (output : Coordinate) :
    lp (fun _ : IntegerWavevector => ℂ) 2 :=
  ⟨fun wave => (radical wave : ℂ)*rows value L output wave,
    (majorant value regular L).2.mono (rows_bound value regular L output)⟩

theorem space_norm (value : wholePhysical) (regular : H1 value) (L : Finset IntegerWavevector) (output : Coordinate) :
    ‖space value regular L output‖ ≤ (∑ first ∈ L, cap first)*‖value.1‖*‖gradientValue value regular‖ := by
  have compare : ‖space value regular L output‖ ≤ ‖majorant value regular L‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro wave
    exact (rows_bound value regular L output wave).trans (le_abs_self _)
  apply compare.trans
  unfold majorant
  apply (norm_sum_le _ _).trans
  have normed (first : IntegerWavevector) :
      ‖(cap first*‖wholeVelocity value.1 first‖) • shift (NativeUnheatedTriadSum.rowNorms (wholeVelocity (gradientValue value regular))) first‖ ≤
        cap first*‖value.1‖*‖gradientValue value regular‖ := by
    rw [norm_smul,Real.norm_of_nonneg (mul_nonneg (cap_nonnegative first) (norm_nonneg _)),shift_norm,NativeUnheatedTriadSum.rowNorms_norm]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ((lp.norm_apply_le_norm (by norm_num) _ first).trans (wholeVelocity_norm_le value.1))
      (cap_nonnegative first)) (wholeVelocity_norm_le _) (norm_nonneg _) (mul_nonneg (cap_nonnegative first) (norm_nonneg _))
  exact (Finset.sum_le_sum fun first _ => normed first).trans_eq (by simp only [Finset.sum_mul])

theorem rows_original (value : wholePhysical) (L : Finset IntegerWavevector) (output : Coordinate) (wave : IntegerWavevector) :
    rows value L output wave = -(Complex.I*(2*Real.pi:ℝ)*stressPressureCoefficient wave
      (NativeHigherTimeJets.mixedFlux (complexSharpSupportProjection L (wholeVelocity value.1)) (wholeVelocity value.1) wave))*
        complexWavevector wave output := by
  have flux : NativeHigherTimeJets.mixedFlux (complexSharpSupportProjection L (wholeVelocity value.1)) (wholeVelocity value.1) wave =
      ∑ first ∈ L, tensor (wholeVelocity value.1 first) (wholeVelocity value.1 (wave-first)) := by
    funext i j
    simp only [NativeHigherTimeJets.mixedFlux,Finset.sum_apply,tensor,neg_mul,Finset.sum_neg_distrib]
    congr 1
    rw [tsum_eq_sum (s := L) (fun first outside => by simp only [complexSharpSupportProjection_apply,if_neg outside,Pi.zero_apply,zero_mul])]
    apply Finset.sum_congr rfl
    intro first inside
    simp only [complexSharpSupportProjection_apply,if_pos inside]
  rw [flux,← NativeCofinalStress.stressPressureCLM_apply,map_sum]
  simp only [rows,Finset.mul_sum,← Finset.sum_neg_distrib,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro first _
  simp only [pair,show first+(wave-first)=wave by abel,NativeCofinalStress.stressPressureCLM_apply]

theorem full_pressure_split (value : wholePhysical) (L : Finset IntegerWavevector) (output : Coordinate) (wave : IntegerWavevector) :
    -(Complex.I*(2*Real.pi:ℝ)*stressPressureCoefficient wave (NativeHigherTimeJets.mixedFlux (wholeVelocity value.1) (wholeVelocity value.1) wave))*
      complexWavevector wave output = rows value L output wave-
      (Complex.I*(2*Real.pi:ℝ)*stressPressureCoefficient wave
        (NativeHigherTimeJets.mixedFlux (wholeVelocity value.1-complexSharpSupportProjection L (wholeVelocity value.1))
          (wholeVelocity value.1) wave))*complexWavevector wave output := by
  have split : NativeHigherTimeJets.mixedFlux (wholeVelocity value.1) (wholeVelocity value.1) =
      NativeHigherTimeJets.mixedFlux (complexSharpSupportProjection L (wholeVelocity value.1)) (wholeVelocity value.1)+
      NativeHigherTimeJets.mixedFlux (wholeVelocity value.1-complexSharpSupportProjection L (wholeVelocity value.1)) (wholeVelocity value.1) := by
    funext k i j
    simp only [Pi.add_apply]
    rw [← NativeHigherTimeJets.mixedFlux_add_left,add_sub_cancel]
  rw [split,Pi.add_apply,rows_original,← NativeCofinalStress.stressPressureCLM_apply,map_add]
  simp only [NativeCofinalStress.stressPressureCLM_apply]
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowPressureLowKernel
