import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarFlatJoint
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarNativeComparison
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseVolumeHardy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarFlatJoint SourceScalarNativeComparison SourcePhysicalKineticSquare
open SourceScalarInverseNativeEnergy
open scoped ContDiff InnerProductSpace BigOperators
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def coordinate (i : SliceIndex) (z : SourceCoordinateSlice) : ℝ :=
  inner ℝ (z.2.1 : Scalar) (scalarFrame i : Scalar)

private theorem coordinate_smooth (i : SliceIndex) : ContDiff ℝ ∞ (coordinate i) :=
  scalarCoordinate.contDiff.inner ℝ contDiff_const

private theorem coordinate_derivative (i : SliceIndex) (z : SourceCoordinateSlice) :
    fderiv ℝ (coordinate i) z (scalarAxis (scalarFrame i))=1 := by
  change fderiv ℝ (fun w => inner ℝ (scalarCoordinate w) (scalarFrame i : Scalar)) z _=1
  rw [fderiv_inner_apply ℝ (scalarCoordinate.differentiableAt) (differentiableAt_const (scalarFrame i : Scalar)),
    ContinuousLinearMap.fderiv, (hasFDerivAt_const (scalarFrame i : Scalar) z).fderiv,
    zero_apply,inner_zero_right,zero_add]
  change inner ℝ (scalarFrame i : Scalar) (scalarFrame i : Scalar)=1
  rw [real_inner_self_eq_norm_sq]
  change ‖scalarFrame i‖^2=1
  rw [scalarFrame.orthonormal.norm_eq_one i,one_pow]

private theorem reciprocal_axis (i : SliceIndex) (z : SourceCoordinateSlice) :
    fderiv ℝ reciprocal z (scalarAxis (scalarFrame i))=
      -coordinate i z/(4*radius z^3) := reciprocal_derivative _ _

def hardyCoefficient (i : SliceIndex) (z : SourceCoordinateSlice) : ℝ :=
  coordinate i z*reciprocal z^2/4

private theorem hardy_smooth (i : SliceIndex) : ContDiff ℝ ∞ (hardyCoefficient i) :=
  ((coordinate_smooth i).mul (reciprocal_smooth.pow 2)).div_const 4

def derivativeCoefficient (i : SliceIndex) (z : SourceCoordinateSlice) : ℝ :=
  reciprocal z^2/4-coordinate i z^2*reciprocal z^4/8

private theorem derivative_smooth (i : SliceIndex) : ContDiff ℝ ∞ (derivativeCoefficient i) :=
  ((reciprocal_smooth.pow 2).div_const 4).sub
    (((coordinate_smooth i).pow 2).mul (reciprocal_smooth.pow 4) |>.div_const 8)

theorem original_hardy_derivative (i : SliceIndex) (z : SourceCoordinateSlice) :
    fderiv ℝ (hardyCoefficient i) z (scalarAxis (scalarFrame i))=derivativeCoefficient i z := by
  have hq := ((coordinate_smooth i).differentiable (by simp) z).hasFDerivAt
  have hs := (reciprocal_smooth.differentiable (by simp) z).hasFDerivAt
  have h := (hq.mul (hs.pow 2)).mul_const (4 : ℝ)⁻¹
  change HasFDerivAt (hardyCoefficient i) _ z at h
  rw [h.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [coordinate_derivative,reciprocal_axis]
  norm_num only [Nat.reduceSub,pow_one,two_smul]
  unfold derivativeCoefficient reciprocal
  field_simp [(radius_pos z).ne']
  ring

def hardyAction (i : SliceIndex) : End :=
  multiply (hardyCoefficient i) (fun _ => (hardy_smooth i).contDiffAt)

def derivativeAction (i : SliceIndex) : End :=
  multiply (derivativeCoefficient i) (fun _ => (derivative_smooth i).contDiffAt)

private theorem scalar_product_derivative (a : SourceCoordinateSlice → ℝ)
    (ha : ContDiff ℝ ∞ a) (f : QuantumTest) (v z : SourceCoordinateSlice) :
    fderiv ℝ (fun w => (a w : ℂ) • f w) z v=
      (a z : ℂ) • fderiv ℝ f z v+(fderiv ℝ a z v : ℂ) • f z := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z ((ha.differentiable (by simp) z).hasFDerivAt)
  have hf := (f.contDiff.differentiable (by simp) z).hasFDerivAt
  have h := hc.smul hf
  change HasFDerivAt (fun w => (a w : ℂ) • f w) _ z at h
  rw [h.fderiv]
  rfl

theorem original_hardy_commutator (i : SliceIndex) (f : QuantumTest) :
    flatMomentum (scalarFrame i) (hardyAction i f)-hardyAction i (flatMomentum (scalarFrame i) f)=
      (-Complex.I) • derivativeAction i f := by
  apply DFunLike.ext
  intro z
  change (-Complex.I) • GaussCoframeCore.derivative (scalarAxis (scalarFrame i)) (hardyAction i f) z-
    (hardyCoefficient i z : ℂ) • ((-Complex.I) •
      GaussCoframeCore.derivative (scalarAxis (scalarFrame i)) f z)=
    (-Complex.I) • ((derivativeCoefficient i z : ℂ) • f z)
  rw [GaussCoframeCore.derivative_apply,GaussCoframeCore.derivative_apply]
  have he : (hardyAction i f : SourceCoordinateSlice → FockFiber)=
      fun w => (hardyCoefficient i w : ℂ) • f w := rfl
  rw [he,scalar_product_derivative _ (hardy_smooth i),original_hardy_derivative]
  simp only [smul_add,smul_comm (-Complex.I) (hardyCoefficient i z : ℂ),add_sub_cancel_left]

private theorem coordinate_square (z : SourceCoordinateSlice) :
    (∑ i : SliceIndex,coordinate i z^2)=‖(z.2.1 : Scalar)‖^2 := by
  change (∑ i : SliceIndex,(inner ℝ z.2.1 (scalarFrame i))^2)=‖z.2.1‖^2
  exact scalarFrame.sum_sq_inner_left _

private theorem radius_square (z : SourceCoordinateSlice) :
    radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 :=
  Real.sq_sqrt (by positivity)

theorem original_hardy_divergence (z : SourceCoordinateSlice) :
    (∑ i : SliceIndex,derivativeCoefficient i z)=
      (59/4 : ℝ)*reciprocal z^2+(1/2 : ℝ)*reciprocal z^4 := by
  have hn := radius_square z
  simp only [derivativeCoefficient,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    actual_scalar_frame_dimension,nsmul_eq_mul,←Finset.sum_div,←Finset.sum_mul,coordinate_square]
  unfold reciprocal
  field_simp [(radius_pos z).ne']
  norm_num
  nlinarith [hn]

theorem original_hardy_coefficient_square (z : SourceCoordinateSlice) :
    (∑ i : SliceIndex,hardyCoefficient i z^2)=
      (1/4 : ℝ)*(reciprocal z^2-reciprocal z^4) := by
  have hn := radius_square z
  simp only [hardyCoefficient,div_pow,mul_pow,←Finset.sum_div,←Finset.sum_mul,coordinate_square]
  unfold reciprocal
  field_simp [(radius_pos z).ne']
  nlinarith [hn]

theorem original_hardy_divergence_action (f : QuantumTest) :
    (∑ i : SliceIndex,derivativeAction i f)=
      (59/4 : ℂ) • inverseAction (inverseAction f)+
        (1/2 : ℂ) • inverseAction (inverseAction (inverseAction (inverseAction f))) := by
  apply DFunLike.ext
  intro z
  simp only [sum_apply]
  change (∑ i : SliceIndex,(derivativeCoefficient i z : ℂ) • f z)=
    (59/4 : ℂ) • ((reciprocal z : ℂ) • ((reciprocal z : ℂ) • f z))+
    (1/2 : ℂ) • ((reciprocal z : ℂ) • ((reciprocal z : ℂ) •
      ((reciprocal z : ℂ) • ((reciprocal z : ℂ) • f z))))
  rw [←Finset.sum_smul,←Complex.ofReal_sum,original_hardy_divergence]
  simp only [smul_smul,←add_smul]
  apply congrArg (fun c : ℂ => c • f z)
  push_cast
  ring

theorem original_hardy_square_action (f : QuantumTest) :
    (∑ i : SliceIndex,hardyAction i (hardyAction i f))=
      (1/4 : ℂ) • (inverseAction (inverseAction f)-
        inverseAction (inverseAction (inverseAction (inverseAction f)))) := by
  apply DFunLike.ext
  intro z
  simp only [sum_apply]
  change (∑ i : SliceIndex,(hardyCoefficient i z : ℂ) • ((hardyCoefficient i z : ℂ) • f z))=
    (1/4 : ℂ) • ((reciprocal z : ℂ) • ((reciprocal z : ℂ) • f z)-
      (reciprocal z : ℂ) • ((reciprocal z : ℂ) • ((reciprocal z : ℂ) • ((reciprocal z : ℂ) • f z))))
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [original_hardy_coefficient_square]
  simp only [smul_smul,←sub_smul]
  apply congrArg (fun c : ℂ => c • f z)
  push_cast
  ring

private theorem inverse_core_pair (f g : QuantumTest) :
    sourcePair f (inverseAction g)=sourcePair (inverseAction f) g := multiply_pair _ _ _ _

private theorem inverse_square_pair (f : QuantumTest) :
    sourcePair f (inverseAction (inverseAction f))=(‖embed (inverseAction f)‖^2 : ℂ) := by
  rw [inverse_core_pair]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _

private theorem inverse_fourth_pair (f : QuantumTest) :
    sourcePair f (inverseAction (inverseAction (inverseAction (inverseAction f))))=
      (‖embed (inverseAction (inverseAction f))‖^2 : ℂ) := by
  rw [inverse_core_pair,inverse_core_pair]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _

theorem original_hardy_divergence_form (f : QuantumTest) :
    (∑ i : SliceIndex,(sourcePair f (derivativeAction i f)).re)=
      (59/4 : ℝ)*‖embed (inverseAction f)‖^2+
        (1/2 : ℝ)*‖embed (inverseAction (inverseAction f))‖^2 := by
  have h := congrArg (sourcePair f) (original_hardy_divergence_action f)
  have hh : (∑ i : SliceIndex,sourcePair f (derivativeAction i f))=
      (59/4 : ℂ)*sourcePair f (inverseAction (inverseAction f))+
      (1/2 : ℂ)*sourcePair f (inverseAction (inverseAction (inverseAction (inverseAction f)))) := by
    simpa only [sourcePair,map_sum,map_add,map_smul,inner_sum,inner_add_right,inner_smul_right] using h
  rw [inverse_square_pair,inverse_fourth_pair] at hh
  have hr := congrArg Complex.re hh
  norm_num [Complex.re_sum,Complex.add_re,Complex.mul_re,Complex.div_re] at hr
  simp only [←Complex.ofReal_pow,Complex.ofReal_re] at hr
  exact hr

theorem original_hardy_square_form (f : QuantumTest) :
    (∑ i : SliceIndex,‖embed (hardyAction i f)‖^2)=
      (1/4 : ℝ)*(‖embed (inverseAction f)‖^2-‖embed (inverseAction (inverseAction f))‖^2) := by
  have h := congrArg (sourcePair f) (original_hardy_square_action f)
  have hh : (∑ i : SliceIndex,sourcePair f (hardyAction i (hardyAction i f)))=
      (1/4 : ℂ)*(sourcePair f (inverseAction (inverseAction f))-
        sourcePair f (inverseAction (inverseAction (inverseAction (inverseAction f))))) := by
    simpa only [sourcePair,map_sum,map_sub,map_smul,inner_sum,inner_sub_right,inner_smul_right] using h
  have hs (i : SliceIndex) : sourcePair f (hardyAction i (hardyAction i f))=
      (‖embed (hardyAction i f)‖^2 : ℂ) :=
    (multiply_pair _ _ _ _).trans (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _)
  simp_rw [hs,inverse_square_pair,inverse_fourth_pair] at hh
  have hr := congrArg Complex.re hh
  norm_num [Complex.re_sum,Complex.sub_re,Complex.mul_re,Complex.div_re] at hr
  simp only [←Complex.ofReal_pow,Complex.ofReal_re] at hr
  exact hr

private theorem square_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (α : ℝ) (u v : E) (c : ℂ)
    (h : inner ℂ u v-inner ℂ v u= -Complex.I*c) :
    ‖u‖^2=‖u-(Complex.I*(α : ℂ)) • v‖^2+α*c.re-α^2*‖v‖^2 := by
  have hi := congrArg Complex.im h
  have hswap : (inner ℂ v u).im= -(inner ℂ u v).im := inner_im_symm (𝕜 := ℂ) v u
  simp only [Complex.sub_im,Complex.mul_im,Complex.neg_im,
    Complex.I_re,Complex.I_im,zero_mul,neg_mul,one_mul,zero_add,hswap] at hi
  have he : c.re= -2*(inner ℂ u v).im := by linarith
  rw [norm_sub_sq (𝕜 := ℂ),inner_smul_right,norm_smul,mul_pow,norm_mul,mul_pow,
    Complex.norm_I,one_pow,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs,he]
  change ‖u‖^2=‖u‖^2-2*(Complex.I*(α : ℂ)*inner ℂ u v).re+
    α^2*‖v‖^2+α*(-2*(inner ℂ u v).im)-α^2*‖v‖^2
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add]
  ring

def alpha : ℝ := 59/2
def completedAction (i : SliceIndex) : End :=
  flatMomentum (scalarFrame i)-(Complex.I*(alpha : ℂ)) • hardyAction i
def completedEnergy (f : QuantumTest) : ℝ :=
  ∑ i : SliceIndex,‖embed (completedAction i f)‖^2

private theorem original_hardy_row_square (i : SliceIndex) (f : QuantumTest) :
    ‖embed (flatMomentum (scalarFrame i) f)‖^2=
      ‖embed (completedAction i f)‖^2+alpha*(sourcePair f (derivativeAction i f)).re-
        alpha^2*‖embed (hardyAction i f)‖^2 := by
  have h0 := congrArg (sourcePair f) (original_hardy_commutator i f)
  have hp := flat_momentum_pair (scalarFrame i) f (hardyAction i f)
  have ha : sourcePair f (hardyAction i (flatMomentum (scalarFrame i) f))=
      sourcePair (hardyAction i f) (flatMomentum (scalarFrame i) f) := multiply_pair _ _ _ _
  simp only [sourcePair] at hp ha
  have h : inner ℂ (embed (flatMomentum (scalarFrame i) f)) (embed (hardyAction i f))-
      inner ℂ (embed (hardyAction i f)) (embed (flatMomentum (scalarFrame i) f))=
        -Complex.I*sourcePair f (derivativeAction i f) := by
    simpa only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right,hp,ha] using h0
  have hs := square_shift alpha (embed (flatMomentum (scalarFrame i) f))
    (embed (hardyAction i f)) (sourcePair f (derivativeAction i f)) h
  simpa only [completedAction,LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul] using hs

/-- The original sixty-one source rows generate the full positive-square Hardy decomposition. -/
theorem original_hardy_square_completion (f : QuantumTest) :
    (sourcePair f (flatKinetic f)).re=completedEnergy f+
      (3481/16 : ℝ)*‖embed (inverseAction f)‖^2+
      (3717/16 : ℝ)*‖embed (inverseAction (inverseAction f))‖^2 := by
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset SliceIndex)) rfl
    (fun i _ => original_hardy_row_square i f)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum] at hs
  rw [original_hardy_divergence_form,original_hardy_square_form] at hs
  rw [actual_flat_kinetic_square]
  calc
    _=completedEnergy f+alpha*((59/4 : ℝ)*‖embed (inverseAction f)‖^2+
        (1/2 : ℝ)*‖embed (inverseAction (inverseAction f))‖^2)-
      alpha^2*((1/4 : ℝ)*(‖embed (inverseAction f)‖^2-
        ‖embed (inverseAction (inverseAction f))‖^2)) := hs
    _=_ := by unfold alpha; ring

theorem original_flat_hardy (f : QuantumTest) :
    (3481/16 : ℝ)*‖embed (inverseAction f)‖^2 ≤ (sourcePair f (flatKinetic f)).re := by
  rw [original_hardy_square_completion]
  have h : 0 ≤ completedEnergy f := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [sq_nonneg ‖embed (inverseAction (inverseAction f))‖]

/-- The same source Hardy term is paid by native70, retaining all nine orthogonal rows. -/
theorem original_native_hardy (f : QuantumTest) :
    (3481/16 : ℝ)*‖embed (inverseAction f)‖^2 ≤ nativeScalarEnergy f := by
  apply (original_flat_hardy f).trans
  rw [actual_scalar_energy_split]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The generated Hardy bound is evaluated on the original inverse-volume core vector. -/
theorem original_inverse_native_hardy (f : QuantumTest) :
    ‖embed (inverseAction (inverseVolumeAction f))‖^2 ≤
      (16/(59 : ℝ)^2)*inverseNativeEnergy f := by
  have h := original_native_hardy (inverseVolumeAction f)
  rw [original_inverse_native_return] at h
  norm_num at ⊢
  nlinarith only [h]

/-- Actual inverse Ward energy directly pays the regularized inverse-volume contact weight. -/
theorem original_inverse_form_hardy (f : QuantumTest) :
    (3481*sourceTime 0/4)*‖embed (inverseAction (inverseVolumeAction f))‖^2 ≤ inverseForm f := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have h := mul_le_mul_of_nonneg_left (original_native_hardy (inverseVolumeAction f))
    (show 0 ≤ 4*sourceTime 0 by positivity)
  rw [original_inverse_native_return] at h
  have hb := original_inverse_native_bound f
  nlinarith only [h,hb]

end LowEnergy.SourceInverseVolumeHardy
