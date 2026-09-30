import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Fourier

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteMassForm
open MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativePhysicalFourier (Torus)
open NativeWindowGreenTestForm NativeWindowGreenProduct
open NativeCompleteStressCarrier (weight weight_pos)
open NativeWindowAbsoluteTimeFourier (polynomial)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def test (F : Finset IntegerWavevector) (a : IntegerWavevector → SpinFiber E) : Test (SpinFiber E) :=
  ∑ k ∈ F,lp.single 2 k ((Real.sqrt (weight k))⁻¹ • a k)

theorem test_decode (F : Finset IntegerWavevector) (a : IntegerWavevector → SpinFiber E) (k : IntegerWavevector) :
    decode (test F a) k=if k∈F then a k else 0 := by
  change Real.sqrt (weight k) • ((∑ p∈F,lp.single (2 : ℝ≥0∞) p ((Real.sqrt (weight p))⁻¹ • a p)) k)=_
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  split_ifs
  · rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr (weight_pos k)).ne',one_smul]
  · exact smul_zero _

theorem project_decode (F : Finset IntegerWavevector) (a : IntegerWavevector → SpinFiber E) (k : IntegerWavevector) :
    decode (NativeWindowGreenSourceForm.project F (test F a)) k=if k∈F then a k else 0 := by
  rw [NativeWindowGreenSourceForm.project_read,test_decode]
  split_ifs <;> rfl

theorem project_mass (F : Finset IntegerWavevector) (a : IntegerWavevector → SpinFiber E) :
    ‖decode (NativeWindowGreenSourceForm.project F (test F a))‖^2=∑ k∈F,‖a k‖^2 := by
  rw [norm_square,tsum_eq_sum (s := F) (fun k outside => by simp [project_decode,if_neg outside])]
  exact Finset.sum_congr rfl fun k inside => by rw [project_decode,if_pos inside]

theorem project_gradient (F : Finset IntegerWavevector) (a : IntegerWavevector → SpinFiber E) :
    gradient (NativeWindowGreenSourceForm.project F (test F a))=∑ k∈F,integerWaveNormSq k*‖a k‖^2 := by
  rw [NativeWindowGreenTestForm.gradient,tsum_eq_sum (s := F) (fun k outside => by simp [project_decode,if_neg outside])]
  exact Finset.sum_congr rfl fun k inside => by rw [project_decode,if_pos inside]

theorem physical_test (F : Finset IntegerWavevector) (a : IntegerWavevector → SpinFiber E) (x : Torus) :
    NativeWindowGreenSourceForm.physicalTest F (test F a) x=polynomial F a x := by
  apply Finset.sum_congr rfl
  intro k inside
  rw [test_decode,if_pos inside]

def cap (B epsilon : ℝ) : ℝ := epsilon+(Real.sqrt testKernel.cap*B)^8*epsilon⁻¹^7

theorem finite_absorption (f : Torus → ℂ) (regular : Integrable f) (c : ComplexSpace)
    (read : ∀ k,c k=mFourierCoeff f k) (F : Finset IntegerWavevector) (a : IntegerWavevector → SpinFiber E)
    (A : SpinFiber E →L[ℂ] SpinFiber E) (contractive : ‖A‖≤1) (B : ℝ) (bound : ‖c‖≤B)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ‖∫ x : Torus,f x*inner ℂ (polynomial F a x) (A (polynomial F a x))‖≤
      epsilon*(∑ k∈F,integerWaveNormSq k*‖a k‖^2)+cap B epsilon*(∑ k∈F,‖a k‖^2) := by
  have actual:=NativeWindowGreenSourceForm.physical_integral_of_coefficients f regular c read A F (test F a)
  simp only [physical_test] at actual
  rw [actual]
  have paid:=form_absorption c A (NativeWindowGreenSourceForm.project F (test F a)) epsilon positive
  rw [project_gradient,project_mass] at paid
  apply paid.trans
  have coefficient : ‖A‖*Real.sqrt testKernel.cap*‖c‖≤Real.sqrt testKernel.cap*B :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right contractive (Real.sqrt_nonneg _)) (norm_nonneg _)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_left bound (Real.sqrt_nonneg testKernel.cap))
  dsimp only [cap]
  gcongr

def pair (u v : E) : SpinFiber E :=
  WithLp.toLp 2 fun entry => if entry=(0,0) then u else if entry=(1,0) then v else 0

def transfer : SpinFiber E →L[ℂ] SpinFiber E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 × Fin 2 => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun entry => if entry=(0,0) then
      PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 × Fin 2 => E) (1,0) else 0)

theorem transfer_apply (v : SpinFiber E) (entry : Fin 4 × Fin 2) :
    (transfer (E := E) v) entry=if entry=(0,0) then v (1,0) else 0 := by
  simp only [transfer,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,PiLp.continuousLinearEquiv_symm_apply,ContinuousLinearMap.pi_apply]
  split_ifs <;> simp_all

theorem transfer_norm : ‖transfer (E := E)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have component:=Finset.single_le_sum (s := (Finset.univ : Finset (Fin 4 × Fin 2)))
    (fun entry _ => sq_nonneg ‖v entry‖) (Finset.mem_univ (1,0))
  simpa [PiLp.norm_sq_eq_of_L2,transfer_apply,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two] using component

omit [InnerProductSpace ℂ E] in
theorem pair_square (u v : E) : ‖pair u v‖^2=‖u‖^2+‖v‖^2 := by
  simp [pair,PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two]

theorem pair_inner (u v : E) : inner ℂ (pair u v) (transfer (E := E) (pair u v))=inner ℂ u v := by
  simp [pair,PiLp.inner_apply,transfer_apply,Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_two]

theorem polynomial_pair (F : Finset IntegerWavevector) (u v : IntegerWavevector → E) (x : Torus) :
    polynomial F (fun k => pair (u k) (v k)) x=pair (polynomial F u x) (polynomial F v x) := by
  apply PiLp.ext
  intro entry
  simp only [polynomial,ContinuousMap.coe_mk,pair,PiLp.toLp_apply]
  split_ifs <;> simp_all

theorem mixed_absorption (f : Torus → ℂ) (regular : Integrable f) (c : ComplexSpace)
    (read : ∀ k,c k=mFourierCoeff f k) (F : Finset IntegerWavevector) (u v : IntegerWavevector → E)
    (B : ℝ) (bound : ‖c‖≤B) (epsilon : ℝ) (positive : 0<epsilon) :
    ‖∫ x : Torus,f x*inner ℂ (polynomial F u x) (polynomial F v x)‖≤
      epsilon*(∑ k∈F,integerWaveNormSq k*(‖u k‖^2+‖v k‖^2))+
        cap B epsilon*(∑ k∈F,(‖u k‖^2+‖v k‖^2)) := by
  have paid:=finite_absorption f regular c read F (fun k => pair (u k) (v k)) transfer transfer_norm B bound epsilon positive
  simpa only [polynomial_pair,pair_inner,pair_square] using paid

def coefficients (f : Lp ℂ 2 (volume : Measure Torus)) : ComplexSpace :=
  (mFourierBasis (d := Coordinate)).repr f

theorem coefficients_read (f : Lp ℂ 2 (volume : Measure Torus)) (k : IntegerWavevector) :
    coefficients f k=mFourierCoeff f k := by
  rw [coefficients,mFourierBasis_repr]

theorem coefficients_norm (f : Lp ℂ 2 (volume : Measure Torus)) : ‖coefficients f‖=‖f‖ :=
  (mFourierBasis (d := Coordinate)).repr.norm_map f

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteMassForm
