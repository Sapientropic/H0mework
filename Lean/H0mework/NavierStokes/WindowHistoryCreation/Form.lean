import H0mework.NavierStokes.WindowSourceGreen.FormTest
import H0mework.NavierStokes.WindowEnergyTraceTerminal.Synthesis

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCreationForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open NativePhysicalFourier UnitAddTorus
open NativeWindowStressHeatSource (physical)
open NativeWindowFiniteGramFourier (fourierRead)
open NativeWindowGreenTestForm (Test decode gradient form form_summable testKernel)
open NativeWindowGreenProduct (ComplexSpace)
open NativeCompleteStressCarrier (weight weight_pos)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def test (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) : Test ℂ :=
  ∑ k∈F,lp.single 2 k ((Real.sqrt (weight k))⁻¹ • a k)

theorem test_decode (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) (k : IntegerWavevector) :
    decode (test F a) k=if k∈F then a k else 0 := by
  change Real.sqrt (weight k) • ((∑ p∈F,lp.single (2 : ℝ≥0∞) p ((Real.sqrt (weight p))⁻¹ • a p)) k)=_
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  split_ifs
  · rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr (weight_pos k)).ne',one_smul]
  · exact smul_zero _

theorem test_mass (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) :
    ‖decode (test F a)‖^2=∑ k∈F,‖a k‖^2 := by
  rw [NativeWindowGreenTestForm.norm_square,tsum_eq_sum (s := F) (fun k outside => by
    rw [test_decode,if_neg outside,norm_zero,zero_pow (by decide : (2:ℕ)≠0)])]
  exact Finset.sum_congr rfl fun k inside => by rw [test_decode,if_pos inside]

theorem test_gradient (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) :
    gradient (test F a)=∑ k∈F,integerWaveNormSq k*‖a k‖^2 := by
  rw [NativeWindowGreenTestForm.gradient,tsum_eq_sum (s := F) (fun k outside => by
    rw [test_decode,if_neg outside,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero])]
  exact Finset.sum_congr rfl fun k inside => by rw [test_decode,if_pos inside]

private def differenceEquiv : (IntegerWavevector × IntegerWavevector) ≃ (IntegerWavevector × IntegerWavevector) where
  toFun index := (index.1-index.2,index.1)
  invFun index := (index.2,index.2-index.1)
  left_inv index := by ext <;> simp
  right_inv index := by ext <;> simp

theorem form_finite (c : ComplexSpace) (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ) :
    form c (ContinuousLinearMap.id ℂ ℂ) (test F a)=
      ∑ p∈F,∑ q∈F,c (p-q)*inner ℂ (a p) (a q) := by
  have paid:=differenceEquiv.summable_iff.mpr (form_summable c (ContinuousLinearMap.id ℂ ℂ) (test F a)).of_norm
  rw [form,← differenceEquiv.tsum_eq]
  simp only [differenceEquiv,Equiv.coe_fn_mk,NativeWindowGreenTestForm.integrand,sub_sub_cancel,ContinuousLinearMap.id_apply]
  simp only [Function.comp_def,differenceEquiv,Equiv.coe_fn_mk,NativeWindowGreenTestForm.integrand,sub_sub_cancel,
    ContinuousLinearMap.id_apply] at paid
  rw [Summable.tsum_prod paid,tsum_eq_sum (s := F) (fun p outside => by simp [test_decode,if_neg outside])]
  apply Finset.sum_congr rfl
  intro p inside
  rw [tsum_eq_sum (s := F) (fun q outside => by simp [test_decode,if_neg outside])]
  exact Finset.sum_congr rfl fun q included => by simp only [test_decode,if_pos inside,if_pos included]

def coefficients (f : C(Torus,ℝ)) : ComplexSpace := (mFourierBasis (d := Coordinate)).repr (physical f)

theorem coefficients_read (f : C(Torus,ℝ)) (k : IntegerWavevector) : coefficients f k=mFourierCoeff (fun x => (f x : ℂ)) k := by
  rw [coefficients,mFourierBasis_repr,NativeWindowTraceTerminalCubic.physical_fourier,NativeWindowFiniteGramFourier.fourierRead_apply]

theorem coefficients_norm (f : C(Torus,ℝ)) : ‖coefficients f‖=‖physical f‖ := (mFourierBasis (d := Coordinate)).repr.norm_map _

theorem physical_identity (f w : C(Torus,ℝ)) (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ)
    (original : ∀ x : Torus,(w x : ℂ)=∑ k∈F,mFourier k x*a k) :
    (∫x : Torus,f x*(w x)^2)=(form (coefficients f) (ContinuousLinearMap.id ℂ ℂ) (test F a)).re := by
  have modulated (p q : IntegerWavevector) : Integrable (fun x : Torus => mFourier (-(p-q)) x*(f x : ℂ)) := by
    exact ((mFourier (-(p-q))).continuous.mul (Complex.continuous_ofReal.comp f.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have pointwise (x : Torus) : (f x : ℂ)*(w x)^2=
      ∑ p∈F,∑ q∈F,(mFourier (-(p-q)) x*(f x : ℂ))*inner ℂ (a p) (a q) := by
    have square : (w x : ℂ)^2=inner ℂ (w x : ℂ) (w x : ℂ) := by
      change (w x : ℂ)^2=(w x : ℂ)*conj (w x : ℂ)
      rw [Complex.conj_ofReal,pow_two]
    rw [square,original]
    change (f x : ℂ)*inner ℂ (∑ k∈F,mFourier k x • a k) (∑ k∈F,mFourier k x • a k)=_
    simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [← mFourier_neg]
    have phase:mFourier (-p) x*mFourier q x=mFourier (-(p-q)) x := by rw [← mFourier_add]; congr 1; abel_nf
    change _=mFourier (-(p-q)) x*(f x : ℂ)*inner ℂ (a p) (a q)
    calc
      _=(mFourier (-p) x*mFourier q x)*(f x : ℂ)*inner ℂ (a p) (a q) := by ring
      _=_ := by rw [phase]
  have complexIdentity:(∫x : Torus,(f x : ℂ)*(w x)^2)=form (coefficients f) (ContinuousLinearMap.id ℂ ℂ) (test F a) := by
    simp_rw [pointwise]
    rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => (modulated p q).mul_const _)),form_finite]
    apply Finset.sum_congr rfl
    intro p _
    rw [integral_finsetSum _ (fun q _ => (modulated p q).mul_const _)]
    exact Finset.sum_congr rfl fun q _ => by rw [integral_mul_const,coefficients_read]; rfl
  have paid:Integrable (fun x : Torus => (f x : ℂ)*(w x)^2) :=
    ((Complex.continuous_ofReal.comp f.continuous).mul ((Complex.continuous_ofReal.comp w.continuous).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← complexIdentity]
  change _=RCLike.re (∫x : Torus,(f x : ℂ)*(w x)^2)
  rw [← integral_re paid]
  congr 1
  funext x
  change f x*(w x)^2=((f x : ℂ)*(w x)^2).re
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]

def budget (B epsilon : ℝ) : ℝ := epsilon+(Real.sqrt testKernel.cap*B)^8*epsilon⁻¹^7

theorem physical_absorption (f w : C(Torus,ℝ)) (F : Finset IntegerWavevector) (a : IntegerWavevector → ℂ)
    (original : ∀ x : Torus,(w x : ℂ)=∑ k∈F,mFourier k x*a k)
    (epsilon : ℝ) (positive : 0<epsilon) :
    |∫x : Torus,f x*(w x)^2|≤epsilon*(∑ k∈F,integerWaveNormSq k*‖a k‖^2)+
      budget ‖physical f‖ epsilon*(∑ k∈F,‖a k‖^2) := by
  rw [physical_identity f w F a original]
  apply (Complex.abs_re_le_norm _).trans
  have paid:=NativeWindowGreenTestForm.form_absorption (coefficients f) (ContinuousLinearMap.id ℂ ℂ) (test F a) epsilon positive
  simpa only [ContinuousLinearMap.norm_id,one_mul,coefficients_norm,test_gradient,test_mass,budget] using paid

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCreationForm
