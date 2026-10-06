import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScalarAffineScaleTransport
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceNativeCutoffContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.SourceScalarVacuumRadialJet
open GaussCoreHilbert GaussCoreDifferential GaussRadialDomain GaussYukawaCoefficient GaussRadialMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarAffineScaleTransport
open scoped ContDiff InnerProductSpace

def affineQ (z : SourceCoordinateSlice) : ℝ :=
  reciprocal z*(1-(reciprocal z)^2)-radialDerivative ((vacuum : Scalar),0) z

private theorem reciprocal_phi (z : SourceCoordinateSlice) :
    fderiv ℝ reciprocal z (phiEuler z)= -affineQ z := by
  rw [reciprocal_derivative]
  change -inner ℝ (z.2.1 : Scalar) ((vacuum : Scalar)+(z.2.1 : Scalar))/(4*radius z^3)=_
  rw [inner_add_right,real_inner_self_eq_norm_sq]
  have hr : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 := Real.sq_sqrt (by positivity)
  have hn : ‖(z.2.1 : Scalar)‖^2=4*(radius z^2-1) := by nlinarith
  rw [hn]
  unfold affineQ radialDerivative reciprocal
  field_simp [(radius_pos z).ne']
  ring

private theorem affine_q_bound (z : SourceCoordinateSlice) :
    |affineQ z| ≤ (1+‖vacuum‖/2)*reciprocal z := by
  let s := reciprocal z
  have hs : 0 ≤ s := (inv_pos.mpr (radius_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hfactor : 0 ≤ 1-s^2 := by nlinarith
  have hfactor1 : 1-s^2 ≤ 1 := by nlinarith
  have hd := SourceNativeCutoffContact.reciprocal_native_bound ((vacuum : Scalar),0) z
  have ha : 0 ≤ s*(1-s^2) := mul_nonneg hs hfactor
  have hb : s*(1-s^2) ≤ s := mul_le_of_le_one_right hs hfactor1
  have hdn := neg_le_of_abs_le hd
  have hdp := le_of_abs_le hd
  dsimp [affineQ]
  rw [abs_le]
  constructor <;> nlinarith [norm_nonneg (vacuum : Scalar)]

private def vacuumInner (z : SourceCoordinateSlice) : ℝ := inner ℝ (z.2.1 : Scalar) vacuum

private theorem inner_phi (z : SourceCoordinateSlice) :
    fderiv ℝ vacuumInner z (phiEuler z)=vacuumInner z+‖vacuum‖^2 := by
  have h := (scalarCoordinate.hasFDerivAt (x := z)).inner ℝ (hasFDerivAt_const (vacuum : Scalar) z)
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ => D (phiEuler z)) h.fderiv
  change fderiv ℝ vacuumInner z (phiEuler z)=_ at he
  change fderiv ℝ vacuumInner z (phiEuler z)=inner ℝ (z.2.1 : Scalar) 0+
    inner ℝ ((vacuum : Scalar)+(z.2.1 : Scalar)) vacuum at he
  rw [inner_zero_right,zero_add,inner_add_left,real_inner_self_eq_norm_sq] at he
  exact he.trans (add_comm _ _)

/-- The actual vacuum radial term is differentiated along the original affine source field. -/
theorem actual_vacuum_radial_phi (z : SourceCoordinateSlice) :
    fderiv ℝ (radialDerivative ((vacuum : Scalar),0)) z (phiEuler z)=
      -(1/4 : ℝ)*(vacuumInner z+‖vacuum‖^2)*(reciprocal z)^3+
        (3/4 : ℝ)*vacuumInner z*(reciprocal z)^2*affineQ z := by
  have hj := (scalarCoordinate.hasFDerivAt (x := z)).inner ℝ (hasFDerivAt_const (vacuum : Scalar) z)
  have hs := (reciprocal_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z)
  have hp : (radialDerivative ((vacuum : Scalar),0) : SourceCoordinateSlice → ℝ)=
      fun x => (-1/4 : ℝ)*vacuumInner x*(reciprocal x)^3 := by
    funext x
    unfold radialDerivative vacuumInner reciprocal
    field_simp
  have h := (hj.const_mul (-1/4)).mul (hs.pow 3)
  have he := congrArg (fun D : SourceCoordinateSlice →L[ℝ] ℝ => D (phiEuler z)) h.fderiv
  change fderiv ℝ (fun x => (-1/4 : ℝ)*vacuumInner x*(reciprocal x)^3) z (phiEuler z)=_ at he
  rw [←hp] at he
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,nsmul_eq_mul]
  have hi : fderiv ℝ vacuumInner z=
      (fderivInnerCLM ℝ (scalarCoordinate z,vacuum)).comp (scalarCoordinate.prod 0) := hj.fderiv
  rw [←hi,reciprocal_phi,inner_phi]
  change (-1/4 : ℝ)*vacuumInner z*(3*reciprocal z^2*(-affineQ z))+
    reciprocal z^3*((-1/4 : ℝ)*(vacuumInner z+‖vacuum‖^2))=_
  ring

private theorem inner_reciprocal_bound (z : SourceCoordinateSlice) :
    |vacuumInner z| * reciprocal z ≤ 2*‖vacuum‖ := by
  have hr : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 := Real.sq_sqrt (by positivity)
  have hp := radius_pos z
  have hx : ‖(z.2.1 : Scalar)‖≤2*radius z := by nlinarith [norm_nonneg (z.2.1 : Scalar)]
  have hi := (abs_real_inner_le_norm (z.2.1 : Scalar) vacuum).trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  unfold vacuumInner reciprocal
  rw [←div_eq_mul_inv]
  calc
    _ ≤ (2*radius z*‖vacuum‖)/radius z := (div_le_div_iff_of_pos_right hp).mpr hi
    _ = _ := by field_simp

private theorem abs_plus (a b : ℝ) : |a+b| ≤ |a|+|b| := by
  simpa only [Real.norm_eq_abs] using norm_add_le a b

/-- This coefficient decays like the same source reciprocal; its bound is generated without a state premise. -/
theorem actual_vacuum_radial_phi_bound (z : SourceCoordinateSlice) :
    |fderiv ℝ (radialDerivative ((vacuum : Scalar),0)) z (phiEuler z)| ≤
      (2*‖vacuum‖+‖vacuum‖^2)*reciprocal z := by
  rw [actual_vacuum_radial_phi]
  let s := reciprocal z
  let v := ‖vacuum‖
  have hs : 0 ≤ s := (inv_pos.mpr (radius_pos z)).le
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hv : 0 ≤ v := norm_nonneg _
  have hi := inner_reciprocal_bound z
  have ha := affine_q_bound z
  have h1 : |vacuumInner z+v^2| * s^3 ≤ (2*v+v^2)*s^2 := by
    have hb := abs_plus (vacuumInner z) (v^2)
    rw [abs_of_nonneg (sq_nonneg v)] at hb
    have hc := mul_le_mul_of_nonneg_right hi (sq_nonneg s)
    have hd := mul_le_mul_of_nonneg_right hs1 (mul_nonneg (sq_nonneg v) (sq_nonneg s))
    have he := mul_le_mul_of_nonneg_right hb (pow_nonneg hs 3)
    nlinarith
  have h2 : |vacuumInner z| * s^2*|affineQ z| ≤ (2*v*(1+v/2))*s^2 := by
    have hb := mul_le_mul_of_nonneg_left ha (mul_nonneg (abs_nonneg (vacuumInner z)) (sq_nonneg s))
    have hc := mul_le_mul_of_nonneg_right hi (mul_nonneg (by positivity : 0 ≤ 1+v/2) (sq_nonneg s))
    dsimp [s,v] at *
    nlinarith
  have ht := abs_plus (-(1/4 : ℝ)*(vacuumInner z+‖vacuum‖^2)*(reciprocal z)^3)
    ((3/4 : ℝ)*vacuumInner z*(reciprocal z)^2*affineQ z)
  have hsAbs : |reciprocal z|=reciprocal z := abs_of_nonneg hs
  simp only [abs_mul,abs_neg,abs_pow,hsAbs] at ht
  norm_num at ht
  have hs2 : s^2 ≤ s := by nlinarith
  have hc := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ 2*v+v^2 by positivity)
  change _ ≤ (2*v+v^2)*s
  dsimp [s,v] at h1 h2 ht hc ⊢
  simp only [neg_mul] at ht ⊢
  nlinarith

end LowEnergy.SourceScalarVacuumRadialJet
