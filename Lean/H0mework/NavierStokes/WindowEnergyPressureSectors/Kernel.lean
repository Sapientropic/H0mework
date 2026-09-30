import H0mework.NavierStokes.WindowEnergyPressure.Source
import H0mework.NavierStokes.SourceAction.Pressure

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Matrix Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowPressureSectors
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeStressCurlAlgebra NativeHigherTimeJets NativeUnheatedSexticLatticePower NativeTimeJetCarrier
open NativeEndpointVelocityCarrier NativeWholeResolvent NativeWholeH1Mixed
noncomputable section

theorem mixed_swap (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector)
    (output input : Coordinate) : mixedFlux left right wave output input = mixedFlux right left wave input output := by
  unfold mixedFlux
  congr 1
  rw [← (Equiv.subLeft wave).tsum_eq]
  apply tsum_congr
  intro first
  change left (wave-first) input*right (wave-(wave-first)) output = _
  rw [sub_sub_cancel,mul_comm]

theorem pressure_transpose (wave : IntegerWavevector) (value : NativeFluidStressCoefficient) :
    stressPressureCoefficient wave (fun i j => value j i) = stressPressureCoefficient wave value := by
  unfold stressPressureCoefficient
  split_ifs
  · rfl
  · congr 1
    simp only [dotProduct,Fin.sum_univ_three]
    ring

def force (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) (output : Coordinate) : ℂ :=
  -(Complex.I*(2*Real.pi:ℝ)*stressPressureCoefficient wave (mixedFlux left right wave))*complexWavevector wave output

theorem force_swap (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) (output : Coordinate) :
    force left right wave output = force right left wave output := by
  have transpose : mixedFlux left right wave = fun i j => mixedFlux right left wave j i :=
    funext fun i => funext fun j => mixed_swap left right wave i j
  rw [force,transpose,pressure_transpose]
  rfl

theorem force_add_left (left other right : ComplexVorticityHilbertState) (wave : IntegerWavevector) (output : Coordinate) :
    force (left+other) right wave output = force left right wave output+force other right wave output := by
  have add : mixedFlux (left+other) right wave = mixedFlux left right wave+mixedFlux other right wave :=
    funext fun i => funext fun j => mixedFlux_add_left left other right wave i j
  simp only [force,add,← NativeCofinalStress.stressPressureCLM_apply,map_add]
  ring

theorem force_add_right (left right other : ComplexVorticityHilbertState) (wave : IntegerWavevector) (output : Coordinate) :
    force left (right+other) wave output = force left right wave output+force left other wave output := by
  rw [force_swap,force_add_left,force_swap right left,force_swap other left]

theorem force_sub_left (left other right : ComplexVorticityHilbertState) (wave : IntegerWavevector) (output : Coordinate) :
    force (left-other) right wave output = force left right wave output-force other right wave output := by
  have add := force_add_left (left-other) other right wave output
  rw [sub_add_cancel] at add
  exact eq_sub_of_add_eq add.symm

theorem force_sub_right (left right other : ComplexVorticityHilbertState) (wave : IntegerWavevector) (output : Coordinate) :
    force left (right-other) wave output = force left right wave output-force left other wave output := by
  rw [force_swap,force_sub_left,force_swap right left,force_swap other left]

theorem force_zero (left right : ComplexVorticityHilbertState) (output : Coordinate) : force left right 0 output=0 := by
  simp [force,stressPressureCoefficient]

theorem force_original (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) (output : Coordinate) :
    projectedDivergenceCLM wave (mixedFlux left right wave) output =
      nativeFluidStressDivergenceCoefficient (mixedFlux left right) wave output+force left right wave output := by
  have original := congrFun (nativeFluidStressDivergenceCoefficient_eq_leray_add_pressure wave (mixedFlux left right wave)) output
  change nativeFluidStressDivergenceCoefficient (mixedFlux left right) wave output =
    projectedDivergenceCLM wave (mixedFlux left right wave) output+
      (Complex.I*(2*Real.pi:ℝ)*stressPressureCoefficient wave (mixedFlux left right wave))*complexWavevector wave output at original
  rw [force]
  linear_combination -original

theorem force_low (value : wholePhysical) (L : Finset IntegerWavevector) (wave : IntegerWavevector) (output : Coordinate) :
    force (complexSharpSupportProjection L (wholeVelocity value.1)) (wholeVelocity value.1) wave output =
      NativeWindowPressureLowKernel.rows value L output wave := (NativeWindowPressureLowKernel.rows_original value L output wave).symm

def trilinear (left right last : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (output input : Coordinate) (test : NativeWindowPressureLowSource.Sequence) : ℂ :=
  ∑ p ∈ F, ∑ q ∈ F, star ((density 1 (p+q):ℂ)*test (p+q))*force left right p output*last q input

theorem trilinear_sectors (value low : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (output input : Coordinate) (test : NativeWindowPressureLowSource.Sequence) :
    trilinear value value value F output input test =
      2*trilinear low value value F output input test-trilinear low low value F output input test+
      trilinear (value-low) (value-low) low F output input test+
      trilinear (value-low) (value-low) (value-low) F output input test := by
  simp only [trilinear,force_sub_left,force_sub_right,lp.coeFn_sub,Pi.sub_apply,force_swap value low]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem trilinear_low (value : wholePhysical) (L F : Finset IntegerWavevector) (output input : Coordinate)
    (test : NativeWindowPressureLowSource.Sequence) :
    trilinear (complexSharpSupportProjection L (wholeVelocity value.1)) (wholeVelocity value.1) (wholeVelocity value.1)
      F output input test = NativeWindowPressureLowSource.form value L F output input test := by
  simp only [trilinear,force_low,NativeWindowPressureLowSource.form,NativeWindowPressureLowSource.integrand]

theorem pressure_norm (wave : IntegerWavevector) (value : NativeFluidStressCoefficient) :
    ‖stressPressureCoefficient wave value‖ ≤ ‖NativeCompleteStressCarrier.tensor value‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [Complex.normSq_eq_norm_sq,NativeCompleteStressCarrier.tensor_norm_sq] using
    NativePressureFullOrder.pressure_contraction_normSq_le wave value

def pressureSequence (value : NativeCompleteStressCarrier.Space) : NativeWindowPressureLowSource.Sequence :=
  ⟨fun wave => stressPressureCoefficient wave (NativeCompleteStressCarrier.untensor (value wave)),
    value.2.mono' (fun wave => by
      have same : NativeCompleteStressCarrier.tensor (NativeCompleteStressCarrier.untensor (value wave))=value wave := by ext i; rfl
      simpa only [same] using pressure_norm wave (NativeCompleteStressCarrier.untensor (value wave)))⟩

theorem pressureSequence_norm (value : NativeCompleteStressCarrier.Space) : ‖pressureSequence value‖ ≤ ‖value‖ := by
  apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
  intro wave
  have same : NativeCompleteStressCarrier.tensor (NativeCompleteStressCarrier.untensor (value wave))=value wave := by ext i; rfl
  exact (pressure_norm wave _).trans_eq (congrArg norm same)

theorem radical_neg (wave : IntegerWavevector) : radical (-wave)=radical wave := by
  simp [radical,mass,integerWaveNormSq]

theorem density_le_one (wave : IntegerWavevector) : density 1 wave ≤ 1 := by
  simp only [density,pow_one]
  exact inv_le_one_of_one_le₀ (by simpa using radical_lower 1 wave (by simpa using mass_one wave))

theorem gradient_shift (p q : IntegerWavevector) :
    density 1 (p+q)*Real.sqrt (integerWaveNormSq p)*density 1 p ≤ 2*radical q := by
  have shift := NativeWindowPressureLowKernel.radical_shift (p+q) (-q)
  rw [add_neg_cancel_right,radical_neg] at shift
  have root : Real.sqrt (integerWaveNormSq p) ≤ radical p^2 := by
    rw [radical_square]
    apply Real.sqrt_le_sqrt
    change integerWaveNormSq p ≤ 1+integerWaveNormSq p
    linarith
  simp only [density,pow_one]
  calc
    _ ≤ (radical (p+q))⁻¹*(radical p)^2*(radical p)⁻¹ := by gcongr <;> positivity [radical_positive p,radical_positive (p+q)]
    _ = radical p/radical (p+q) := by field_simp
    _ ≤ 2*radical q := (div_le_iff₀ (radical_positive _)).mpr (by nlinarith only [shift])

theorem shifted_pair_bound (left right : NativeWindowPressureLowSource.Sequence)
    (F : Finset IntegerWavevector) (shift : IntegerWavevector) :
    (∑ wave ∈ F, ‖left wave‖*‖right (wave+shift)‖) ≤ ‖left‖*‖right‖ := by
  let L := NativeWindowPressureLowSource.norms left
  let R := NativeWindowPressureLowKernel.shift (NativeWindowPressureLowSource.norms right) (-shift)
  have read (wave : IntegerWavevector) : R wave=‖right (wave+shift)‖ := by simp [R,NativeWindowPressureLowKernel.shift,NativeWindowPressureLowSource.norms]
  have conjugate : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := by rw [Real.holderConjugate_iff]; norm_num
  have summable := lp.summable_mul conjugate L R
  have bound := lp.tsum_mul_le_mul_norm' conjugate L R
  have normed : ‖L‖*‖R‖=‖left‖*‖right‖ := by
    simp only [L,R,NativeWindowPressureLowKernel.shift_norm,NativeWindowPressureLowSource.norms_norm]
  rw [normed] at bound
  have lhs : (fun wave => ‖L wave‖*‖R wave‖) = fun wave => ‖left wave‖*‖right (wave+shift)‖ := by
    funext wave
    simp only [L,NativeWindowPressureLowSource.norms,Real.norm_of_nonneg (norm_nonneg _),read]
  rw [lhs] at summable bound
  exact (summable.sum_le_tsum F (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans bound

def velocityCoordinate (value : ComplexVorticityHilbertState) (input : Coordinate) : NativeWindowPressureLowSource.Sequence :=
  ⟨fun wave => value wave input,value.2.mono' (fun _wave => norm_le_pi_norm _ input)⟩

theorem velocityCoordinate_norm (value : ComplexVorticityHilbertState) (input : Coordinate) :
    ‖velocityCoordinate value input‖ ≤ ‖value‖ :=
  lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) (fun wave => norm_le_pi_norm _ input)

theorem force_bound (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) (output : Coordinate) :
    ‖force left right wave output‖ ≤ 9*(2*Real.pi)*Real.sqrt (integerWaveNormSq wave)*‖left‖*‖right‖ := by
  have tensor := NativeWindowFiniteStressConvergence.tensor_majorant (mixedFlux left right wave)
    (3*‖left‖*‖right‖) (by positivity) (mixedFlux_norm_le left right wave)
  have coordinate : ‖complexWavevector wave output‖ ≤ Real.sqrt (integerWaveNormSq wave) := by
    apply Real.le_sqrt_of_sq_le
    simpa [complexWavevector,Real.norm_eq_abs,sq_abs] using NativeWindowPressureLowKernel.coordinate_bound wave output
  rw [force,norm_mul,norm_neg,norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
  have paid := mul_le_mul (mul_le_mul_of_nonneg_left ((pressure_norm wave _).trans tensor) (by positivity : 0 ≤ 2*Real.pi))
    coordinate (norm_nonneg _) (by positivity : 0 ≤ (2*Real.pi)*(3*(3*‖left‖*‖right‖)))
  exact paid.trans_eq (by ring)

theorem trilinear_bound (left right last : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (output input : Coordinate) (test : NativeWindowPressureLowSource.Sequence) :
    ‖trilinear left right last F output input test‖ ≤ (∑ p ∈ F, ‖force left right p output‖)*‖last‖*‖test‖ := by
  have each (p : IntegerWavevector) : ‖∑ q ∈ F,
      star ((density 1 (p+q):ℂ)*test (p+q))*force left right p output*last q input‖ ≤
      ‖force left right p output‖*‖last‖*‖test‖ := by
    apply (norm_sum_le _ _).trans
    have rows (q : IntegerWavevector) : ‖star ((density 1 (p+q):ℂ)*test (p+q))*force left right p output*last q input‖ ≤
        ‖force left right p output‖*(‖last q input‖*‖test (q+p)‖) := by
      rw [norm_mul,norm_mul,norm_star,norm_mul,Complex.norm_real,Real.norm_of_nonneg (density_positive 1 _).le]
      have paid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (density_le_one (p+q)) (norm_nonneg (test (p+q)))) (norm_nonneg (force left right p output)))
          (norm_nonneg (last q input))
      exact paid.trans_eq (by rw [add_comm p q]; ring)
    apply (Finset.sum_le_sum (fun q _ => rows q)).trans
    rw [← Finset.mul_sum]
    have pair := shifted_pair_bound (velocityCoordinate last input) test F p
    apply (mul_le_mul_of_nonneg_left pair (norm_nonneg _)).trans
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (velocityCoordinate_norm last input) (norm_nonneg _))
      (norm_nonneg _)).trans_eq (by ring)
  unfold trilinear
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun p _ => each p)).trans_eq (by simp only [Finset.sum_mul]))

def lowLowCap (L : Finset IntegerWavevector) : ℝ := ∑ p ∈ L+L, 9*(2*Real.pi)*Real.sqrt (integerWaveNormSq p)

theorem lowLowCap_nonnegative (L : Finset IntegerWavevector) : 0 ≤ lowLowCap L :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem low_low_bound (value : ComplexVorticityHilbertState) (L F : Finset IntegerWavevector)
    (output input : Coordinate) (test : NativeWindowPressureLowSource.Sequence) :
    ‖trilinear (complexSharpSupportProjection L value) (complexSharpSupportProjection L value) value F output input test‖ ≤
      lowLowCap L*‖value‖^3*‖test‖ := by
  let low := complexSharpSupportProjection L value
  have outside (p : IntegerWavevector) (absent : p ∉ L+L) : force low low p output=0 := by
    have flux : mixedFlux low low p=0 := by
      funext i j
      unfold mixedFlux
      have zero (a : IntegerWavevector) : low a j*low (p-a) i=0 := by
        by_cases inside : a ∈ L
        · have last : p-a ∉ L := fun present => absent (Finset.mem_add.mpr ⟨a,inside,p-a,present,by abel⟩)
          simp [low,last]
        · simp [low,inside]
      simp only [zero,tsum_zero,neg_zero,Pi.zero_apply]
    simp only [force,flux,← NativeCofinalStress.stressPressureCLM_apply,map_zero,mul_zero,neg_zero,zero_mul]
  have sum : (∑ p ∈ F, ‖force low low p output‖) ≤ lowLowCap L*‖value‖^2 := by
    apply (Finset.sum_le_sum fun p _ => show ‖force low low p output‖ ≤
        if p ∈ L+L then 9*(2*Real.pi)*Real.sqrt (integerWaveNormSq p)*‖value‖^2 else 0 by
      split_ifs with member
      · have paid := force_bound low low p output
        have small := complexSharpSupportProjection_norm_le L value
        apply paid.trans
        dsimp only [low]
        nlinarith only [mul_self_le_mul_self (norm_nonneg _) small,
          mul_nonneg (by positivity : 0 ≤ 9*(2*Real.pi)*Real.sqrt (integerWaveNormSq p))
            (sub_nonneg.mpr (mul_self_le_mul_self (norm_nonneg _) small))]
      · rw [outside p member,norm_zero]).trans
    rw [← Finset.sum_filter]
    apply (Finset.sum_le_sum_of_subset_of_nonneg (show F.filter (fun p => p ∈ L+L) ⊆ L+L from
      fun p member => (Finset.mem_filter.mp member).2) (fun _ _ _ => by positivity)).trans_eq
    simp only [lowLowCap,Finset.sum_mul]
  exact (trilinear_bound low low value F output input test).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right sum (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring))

theorem force_half_bound (left right : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0)
    (leftH1 : NativeUnheatedStressProduct.H1 left) (rightH1 : NativeUnheatedStressProduct.H1 right)
    (p q : IntegerWavevector) (output : Coordinate) :
    density 1 (p+q)*‖force left right p output‖ ≤ (2*(2*Real.pi)*radical q)*
      ‖pressureSequence (NativeWindowSobolevProduct.state left right leftZero rightZero leftH1 rightH1) p‖ := by
  let state := NativeWindowSobolevProduct.state left right leftZero rightZero leftH1 rightH1
  have read : pressureSequence state p = (radical p:ℂ)*stressPressureCoefficient p (mixedFlux left right p) := by
    change NativeCofinalStress.stressPressureCLM p (radical p • mixedFlux left right p) = _
    exact (NativeCofinalStress.stressPressureCLM p |>.restrictScalars ℝ).map_smul (radical p) _
  have scalar : ‖stressPressureCoefficient p (mixedFlux left right p)‖=density 1 p*‖pressureSequence state p‖ := by
    rw [read,norm_mul,Complex.norm_real,Real.norm_of_nonneg (radical_positive _).le]
    simp only [density,pow_one,← mul_assoc,inv_mul_cancel₀ (radical_positive _).ne',one_mul]
  have coordinate : ‖complexWavevector p output‖ ≤ Real.sqrt (integerWaveNormSq p) := by
    apply Real.le_sqrt_of_sq_le
    simpa [complexWavevector,Real.norm_eq_abs,sq_abs] using NativeWindowPressureLowKernel.coordinate_bound p output
  rw [force,norm_mul,norm_neg,norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi),scalar]
  calc
    _ ≤ density 1 (p+q)*((2*Real.pi)*(density 1 p*‖pressureSequence state p‖)*Real.sqrt (integerWaveNormSq p)) := by
      gcongr <;> positivity [density_positive 1 p,density_positive 1 (p+q)]
    _ = (density 1 (p+q)*Real.sqrt (integerWaveNormSq p)*density 1 p)*((2*Real.pi)*‖pressureSequence state p‖) := by ring
    _ ≤ (2*radical q)*((2*Real.pi)*‖pressureSequence state p‖) :=
      mul_le_mul_of_nonneg_right (gradient_shift p q) (by positivity)
    _ = _ := by ring

def thirdCap (L : Finset IntegerWavevector) : ℝ := ∑ q ∈ L, 2*(2*Real.pi)*radical q

theorem thirdCap_nonnegative (L : Finset IntegerWavevector) : 0 ≤ thirdCap L :=
  Finset.sum_nonneg (fun q _ => by positivity [radical_positive q])

theorem third_low_bound (left right last : ComplexVorticityHilbertState)
    (leftZero : left 0=0) (rightZero : right 0=0)
    (leftH1 : NativeUnheatedStressProduct.H1 left) (rightH1 : NativeUnheatedStressProduct.H1 right)
    (L F : Finset IntegerWavevector) (output input : Coordinate) (test : NativeWindowPressureLowSource.Sequence) :
    ‖trilinear left right (complexSharpSupportProjection L last) F output input test‖ ≤
      thirdCap L*‖last‖*‖NativeWindowSobolevProduct.state left right leftZero rightZero leftH1 rightH1‖*‖test‖ := by
  let state := NativeWindowSobolevProduct.state left right leftZero rightZero leftH1 rightH1
  let pressure := pressureSequence state
  have each (q : IntegerWavevector) : ‖∑ p ∈ F,
      star ((density 1 (p+q):ℂ)*test (p+q))*force left right p output*
        complexSharpSupportProjection L last q input‖ ≤
      if q ∈ L then (2*(2*Real.pi)*radical q)*‖last‖*‖state‖*‖test‖ else 0 := by
    by_cases member : q ∈ L
    · rw [if_pos member]
      simp only [complexSharpSupportProjection_apply,if_pos member]
      apply (norm_sum_le _ _).trans
      have rows (p : IntegerWavevector) :
          ‖star ((density 1 (p+q):ℂ)*test (p+q))*force left right p output*last q input‖ ≤
          ((2*(2*Real.pi)*radical q)*‖last‖)*(‖pressure p‖*‖test (p+q)‖) := by
        rw [norm_mul,norm_mul,norm_star,norm_mul,Complex.norm_real,Real.norm_of_nonneg (density_positive 1 _).le]
        have velocity := (norm_le_pi_norm (last q) input).trans (lp.norm_apply_le_norm (by norm_num) last q)
        have bound := force_half_bound left right leftZero rightZero leftH1 rightH1 p q output
        have paid := mul_le_mul (mul_le_mul_of_nonneg_right bound (norm_nonneg (test (p+q)))) velocity
          (norm_nonneg _) (by positivity [radical_positive q] : 0 ≤ (2*(2*Real.pi)*radical q)*‖pressure p‖*‖test (p+q)‖)
        convert! paid using 1 <;> ring
      apply (Finset.sum_le_sum fun p _ => rows p).trans
      rw [← Finset.mul_sum]
      have paid := mul_le_mul_of_nonneg_left (shifted_pair_bound pressure test F q)
        (by positivity [radical_positive q] : 0 ≤ (2*(2*Real.pi)*radical q)*‖last‖)
      exact paid.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pressureSequence_norm state) (norm_nonneg _))
        (by positivity [radical_positive q])).trans_eq (by ring))
    · simp only [if_neg member,complexSharpSupportProjection_apply,Pi.zero_apply,mul_zero,Finset.sum_const_zero,norm_zero,le_refl]
  unfold trilinear
  rw [Finset.sum_comm]
  apply (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun q _ => each q)).trans ?_)
  rw [← Finset.sum_filter]
  apply (Finset.sum_le_sum_of_subset_of_nonneg (show F.filter (fun q => q ∈ L) ⊆ L from
    fun q member => (Finset.mem_filter.mp member).2) (fun q _ _ => by positivity [radical_positive q])).trans_eq
  simp only [thirdCap,Finset.sum_mul]
  rfl

open NativePhysicalFourier NativeWindowStressHeatSource
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem trilinear_physical (left right last : ComplexVorticityHilbertState) (F : Finset IntegerWavevector)
    (output input : Coordinate) (test : NativeWindowPressureLowSource.Sequence) (field : ScalarField)
    (read : ∀ wave, (UnitAddTorus.mFourierBasis (d := Coordinate)).repr field wave =
      (NativeUnheatedSexticLatticePower.density 1 wave:ℂ)*test wave) :
    trilinear left right last F output input test = inner ℂ field
      ((polynomial F (fun wave => force left right wave output) 0 0*
        polynomial F (fun wave => last wave input) 0 0).toLp 2 volume ℂ) := by
  rw [NativeWindowPressureLowSource.polynomial_product]
  simp only [map_sum,map_smul,inner_sum,inner_smul_right,trilinear]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  have basis : (UnitAddTorus.mFourier (p+q)).toLp 2 volume ℂ = UnitAddTorus.mFourierBasis (p+q) := by
    rw [show UnitAddTorus.mFourierBasis (p+q) = UnitAddTorus.mFourierLp 2 (p+q) from congrFun UnitAddTorus.coe_mFourierBasis (p+q)]
  rw [basis,← inner_conj_symm,← HilbertBasis.repr_apply_apply,read]
  simp only [starRingEnd_apply]
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowPressureSectors
