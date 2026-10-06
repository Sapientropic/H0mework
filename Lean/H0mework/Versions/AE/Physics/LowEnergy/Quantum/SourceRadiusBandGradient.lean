import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceRadiusBandPolynomial
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusBandGradient
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceRadiusBandPolynomial SourceRadiusPairedScalarPrice SourceRelativePowerTail
open scoped ContDiff InnerProductSpace

def coefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ := band m ell (1-reciprocal z)
theorem coefficient_smooth (m ell : ℕ) : ContDiff ℝ ∞ (coefficient m ell) := by
  unfold coefficient band
  exact ContDiff.sum (fun j _ => (contDiff_const.sub reciprocal_smooth).pow (j+1))
def bandAction (m ell : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply (coefficient m ell) (fun _ => (coefficient_smooth m ell).contDiffAt)

def derivative (v : Ambient) (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  -slope m ell (1-reciprocal z)*radialDerivative v z

theorem derivative_smooth (v : Ambient) (m ell : ℕ) : ContDiff ℝ ∞ (derivative v m ell) :=
  (ContDiff.sum (fun j _ => contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow j))).neg.mul
    (radialDerivative_smooth v)

/-- The finite positive radius band is differentiated in the original native source directions. -/
theorem original_direction_band (v : Ambient) (m ell : ℕ) (z : physicalChart) :
    fderiv ℝ (coefficient m ell) z.val (direction v z.val)=derivative v m ell z.val := by
  have hd := (hasFDerivAt_const (1 : ℝ) z.val).sub
    ((reciprocal_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have he := (HasFDerivAt.fun_sum (u := Finset.Ico m ell) (fun j _ => hd.pow (j+1))).fderiv
  change fderiv ℝ (coefficient m ell) z.val=_ at he
  rw [he]
  simp only [sum_apply,smul_apply,smul_eq_mul,zero_sub,neg_apply,
    Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.sub_apply,nsmul_eq_mul]
  rw [direction_reciprocal]
  unfold derivative SourceRadiusBandPolynomial.slope
  simp only [neg_mul,Finset.sum_mul,Finset.sum_neg_distrib,mul_neg]

private theorem radial_square (z : SourceCoordinateSlice) :
    (∑ i : ScalarIndex,(radialDerivative (scalarDirection i) z)^2)=
      (1-(1-reciprocal z))^4*(1-reciprocal z)*(2-(1-reciprocal z))/4 := by
  have hs : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 := Real.sq_sqrt (by positivity)
  simp only [radialDerivative,neg_sq,div_pow]
  change (∑ i : ScalarIndex,(inner ℝ (z.2.1 : Scalar) (scalarBasis i))^2/(4*radius z^3)^2)=_
  rw [←Finset.sum_div,scalarBasis.sum_sq_inner_left]
  unfold reciprocal
  field_simp [(radius_pos z).ne']
  nlinarith only [hs]

/-- The whole native70 gradient has an ell-independent price against its own first-radius multiplier. -/
theorem original_native_gradient_price (m ell : ℕ) (z : SourceCoordinateSlice) :
    (∑ i : ScalarIndex,(derivative (scalarDirection i) m ell z)^2) ≤
      (3/(m+1 : ℝ))*coefficient m ell z := by
  have hp := inv_pos.mpr (radius_pos z)
  have hq : 0≤1-reciprocal z := sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_radius z))
  have hq1 : 1-reciprocal z<1 := by change 1-(radius z)⁻¹<1;linarith
  have h := original_gradient_price m ell (1-reciprocal z) hq hq1
  have he : (∑ i : ScalarIndex,(derivative (scalarDirection i) m ell z)^2)=
      slope m ell (1-reciprocal z)^2*
        ((1-(1-reciprocal z))^4*(1-reciprocal z)*(2-(1-reciprocal z))/4) := by
    simp only [derivative,mul_pow,neg_sq,←Finset.mul_sum,radial_square]
  rw [he]
  have hn : 0<(m+1 : ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hn).mp
  unfold coefficient
  field_simp
  nlinarith only [h]

private theorem complement_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (((1-inverseAction)^n) f) z=((1-reciprocal z)^n : ℂ) • f z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((1-inverseAction)^n) f) z-(reciprocal z : ℂ) • (((1-inverseAction)^n) f) z=_
    rw [ih]
    apply PiLp.ext
    intro word
    simp only [PiLp.sub_apply,PiLp.smul_apply]
    rw [pow_succ]
    ring

private theorem complement_core (n : ℕ) (f : QuantumTest) :
    embed (((1-inverseAction)^n) f)=(sourceComplement^n) (embed f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change embed (((1-inverseAction)^n) f-inverseAction (((1-inverseAction)^n) f))=
      (sourceComplement^n) (embed f)-inverseRadius ((sourceComplement^n) (embed f))
    rw [map_sub,←inverse_core,ih]

/-- The multiplier is the previously generated radiusBand on the same original Hilbert carrier. -/
theorem original_band_core (m ell : ℕ) (f : QuantumTest) :
    embed (bandAction m ell f)=radiusBand m ell (embed f) := by
  have he : bandAction m ell=(∑ j ∈ Finset.Ico m ell,(1-inverseAction)^(j+1)) := by
    apply LinearMap.ext
    intro q
    apply DFunLike.ext
    intro z
    let ev : QuantumTest →ₗ[ℂ] FockFiber := { toFun := fun f => f z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    change ev (bandAction m ell q)=ev ((∑ j ∈ Finset.Ico m ell,(1-inverseAction)^(j+1)) q)
    simp only [LinearMap.sum_apply,map_sum]
    change (coefficient m ell z : ℂ) • q z=∑ j ∈ Finset.Ico m ell,(((1-inverseAction)^(j+1)) q) z
    simp_rw [complement_apply]
    simp only [coefficient,band,Complex.ofReal_sum,Finset.sum_smul,
      Complex.ofReal_pow,Complex.ofReal_sub,Complex.ofReal_one]
  rw [he]
  simp only [LinearMap.sum_apply,map_sum,complement_core]
  rw [Finset.sum_Ico_add' (fun j => (sourceComplement^j) (embed f)) m ell 1]
  simp only [radiusBand,sum_apply]

end LowEnergy.SourceRadiusBandGradient
