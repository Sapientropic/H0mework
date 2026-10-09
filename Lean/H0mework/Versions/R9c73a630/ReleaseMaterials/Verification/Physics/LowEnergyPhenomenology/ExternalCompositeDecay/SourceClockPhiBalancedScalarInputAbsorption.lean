import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedPrimitiveDefectPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedInputCommonPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.BalancedInputPrimitivePayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore SourceQuantumConfigurationHilbert
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarShiftedBulk SourceScalarPositiveBulkWard SourceScalarPairedTransport
open SourceDilationRemainder SourcePhysicalKineticSquare SourceClockPhiRadiusSourceCurrent SourceClockPhiRadiusAcceleration
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare ScalarBalancedPrimitive ReverseBalancedForcePayer ReverseScalarGaugeWard
open SourceInverseNoetherEnergy
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev B:End:=scalarBulkComplete
private abbrev A:End:=gaugeBalancedNativeForce
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed scalarKinetic gaugeKinetic matterAction scalarBulkComplete positivePrimitive
  gaugeBalancedNativeForce balancedCompressionForce sourceTime
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem inverse_pair(f g:QuantumTest):sourcePair f (U g)=sourcePair (U f) g:=multiply_pair _ _ _ _

def bulkForceRemainder:End:=
  (32:ℂ) • (U*matterAction)+(96:ℂ) • (U*magneticAction)+(48:ℂ) • (U*localAction)+
    (56:ℂ) • (U*scalarSpatialAction)+(2:ℂ) • (U*vacuumConstantAction)

/-- The original scalar bulk's second-order slot is the same compensated force, with only actual local/matter source words left over. -/
theorem actual_scalar_bulk_force:
    B=(4/3:ℂ) • (U*A)+bulkForceRemainder:=by
  have h:=original_bulk_complete_split
  rw [bulkAction,positiveBulk,original_filtered_bulk] at h
  simp only [mul_add,mul_sub,mul_smul_comm] at h
  rw [show A=gaugeBalancedNativeForce from rfl,actual_balanced_native_departments]
  unfold bulkForceRemainder
  linear_combination (norm:=(noncomm_ring;module)) -h

theorem actual_scalar_bulk_compression(F:Index):
    B=(4/3:ℂ) • (U*balancedCompressionForce F)-
      (4/3:ℂ) • (U*balancedOwnDefect F)+bulkForceRemainder:=by
  have h:=actual_balanced_compression_departments F
  have he:balancedCompressionForce F=A+balancedOwnDefect F:=by
    unfold A gaugeBalancedNativeForce balancedOwnDefect
    linear_combination (norm:=module) h
  rw [he,actual_scalar_bulk_force]
  simp only [mul_add,smul_add]
  module

/-- The literal field radius in Pplus provides a full original Hilbert-norm floor. -/
theorem actual_positive_primitive_norm_lower(w:QuantumTest):
    (2/n)*‖embed w‖^2 ≤ primitiveEnergy w:=by
  have hi:phiInverseAction (phiRadiusAction w)=w:=by
    apply DFunLike.ext;intro z
    change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • w z)=w z
    rw [smul_smul,←Complex.ofReal_mul]
    have hp:0<phiRadius z:=Real.sqrt_pos.2 (by positivity)
    unfold phiReciprocal
    rw [inv_mul_cancel₀ hp.ne',Complex.ofReal_one,one_smul]
  have hc(f:QuantumTest):phiInverseBounded (embed f)=embed (phiInverseAction f):=by
    unfold phiInverseAction
    exact GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
  have hn:‖phiInverseBounded‖ ≤ 1:=GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
  have hnorm:‖embed w‖ ≤ ‖embed (phiRadiusAction w)‖:=by
    calc ‖embed w‖=‖phiInverseBounded (embed (phiRadiusAction w))‖:=by rw [hc,hi]
         _ ≤ ‖embed (phiRadiusAction w)‖:=
           (phiInverseBounded.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _))
  have hsq:‖embed w‖^2 ≤ ‖embed (phiRadiusAction w)‖^2:=sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hnorm
  rw [(actual_positive_primitive_energy w).1]
  have he:=JointElectricSource.actual_electric_energy_nonnegative w
  have h0:0 ≤ 2/n:=div_nonneg (by norm_num) n_pos.le
  exact (mul_le_mul_of_nonneg_left hsq h0).trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) he))

private theorem force_square(a:ℝ)(v y:QuantumTest):
    -(8*a/3)*(sourcePair v y).re-(2/(21*n))*‖embed y‖^2=
      (56*n*a^2/3)*‖embed v‖^2-
        (2/(21*n))*‖embed y+((14*n*a:ℝ):ℂ) • embed v‖^2:=by
  have he:=norm_add_sq (𝕜:=ℂ) (embed y) (((14*n*a:ℝ):ℂ) • embed v)
  simp only [inner_smul_right,RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at he
  have hc:(sourcePair y v).re=(sourcePair v y).re:=by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) (embed y) (embed v)
  have hc' : (inner ℂ (embed y) (embed v)).re=(sourcePair v y).re:=by
    unfold sourcePair at hc ⊢
    exact hc
  rw [hc'] at he
  rw [he]
  field_simp [n_pos.ne']
  ring

/-- The native scalar input is paid by the existing negative Pplus force square. Its new price is the actual inverse-volume input norm, while own-CF and local/matter words remain ordered and signed. -/
theorem actual_scalar_input_primitive_absorption(F:Index)(a:ℝ)(input w:QuantumTest):
    -2*a*(sourcePair input (B w)).re-primitiveEnergy (balancedCompressionForce F w)/21 ≤
      (56*n*a^2/3)*‖embed (U input)‖^2+
        (8*a/3)*(sourcePair (U input) (balancedOwnDefect F w)).re-
        2*a*(sourcePair input (bulkForceRemainder w)).re:=by
  have hs:sourcePair input (B w)=(4/3:ℂ)*sourcePair (U input) (balancedCompressionForce F w)-
      (4/3:ℂ)*sourcePair (U input) (balancedOwnDefect F w)+sourcePair input (bulkForceRemainder w):=by
    rw [actual_scalar_bulk_compression F]
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
      pair_add_r,pair_sub_r,pair_smul_r,inverse_pair]
  have hr:=congrArg Complex.re hs
  norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.div_re,Complex.div_im,
    Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat,zero_mul,sub_zero] at hr
  have hp:=actual_positive_primitive_norm_lower (balancedCompressionForce F w)
  have he:=force_square a (U input) (balancedCompressionForce F w)
  have hnon:0 ≤ (2/(21*n))*‖embed (balancedCompressionForce F w)+((14*n*a:ℝ):ℂ) • embed (U input)‖^2:=
    mul_nonneg (div_nonneg (by norm_num) (mul_nonneg (by norm_num) n_pos.le)) (sq_nonneg _)
  have hc:(2/n)/21=2/(21*n):=by field_simp [n_pos.ne']
  have hp':(2/(21*n))*‖embed (balancedCompressionForce F w)‖^2 ≤ primitiveEnergy (balancedCompressionForce F w)/21:=by
    have hh:=div_le_div_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 21)
    calc _=((2/n)*‖embed (balancedCompressionForce F w)‖^2)/21:=by rw [←hc];ring
         _ ≤ _:=hh
  rw [hr]
  nlinarith only [he,hnon,hp']
private theorem radius_inverse_pair(v y:QuantumTest):
    sourcePair (phiInverseAction v) (phiRadiusAction y)=sourcePair v y:=by
  have h:phiRadiusAction (phiInverseAction v)=v:=by
    apply DFunLike.ext;intro z
    change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • v z)=v z
    rw [smul_smul,←Complex.ofReal_mul]
    have hp:0<phiRadius z:=Real.sqrt_pos.2 (by positivity)
    unfold phiReciprocal
    rw [mul_inv_cancel₀ hp.ne',Complex.ofReal_one,one_smul]
  have hr(f g:QuantumTest):sourcePair f (phiRadiusAction g)=sourcePair (phiRadiusAction f) g:=multiply_pair _ _ _ _
  rw [hr,h]

/-- Keeping the original field radius inside the negative primitive square improves the actual input price to the inverse-radius/inverse-volume word. -/
theorem actual_scalar_input_radial_absorption(F:Index)(a:ℝ)(input w:QuantumTest):
    -2*a*(sourcePair input (B w)).re-primitiveEnergy (balancedCompressionForce F w)/21 ≤
      (56*n*a^2/3)*‖embed (phiInverseAction (U input))‖^2+
        (8*a/3)*(sourcePair (U input) (balancedOwnDefect F w)).re-
        2*a*(sourcePair input (bulkForceRemainder w)).re:=by
  have hs:sourcePair input (B w)=(4/3:ℂ)*sourcePair (U input) (balancedCompressionForce F w)-
      (4/3:ℂ)*sourcePair (U input) (balancedOwnDefect F w)+sourcePair input (bulkForceRemainder w):=by
    rw [actual_scalar_bulk_compression F]
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
      pair_add_r,pair_sub_r,pair_smul_r,inverse_pair]
  have hr:=congrArg Complex.re hs
  norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.div_re,Complex.div_im,
    Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat,zero_mul,sub_zero] at hr
  have hp:(2/n)*‖embed (phiRadiusAction (balancedCompressionForce F w))‖^2 ≤
      primitiveEnergy (balancedCompressionForce F w):=by
    rw [(actual_positive_primitive_energy _).1]
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (JointElectricSource.actual_electric_energy_nonnegative _))
  have he:=force_square a (phiInverseAction (U input)) (phiRadiusAction (balancedCompressionForce F w))
  rw [radius_inverse_pair] at he
  have hnon:0 ≤ (2/(21*n))*‖embed (phiRadiusAction (balancedCompressionForce F w))+
      ((14*n*a:ℝ):ℂ) • embed (phiInverseAction (U input))‖^2:=
    mul_nonneg (div_nonneg (by norm_num) (mul_nonneg (by norm_num) n_pos.le)) (sq_nonneg _)
  have hc:(2/n)/21=2/(21*n):=by field_simp [n_pos.ne']
  have hp':(2/(21*n))*‖embed (phiRadiusAction (balancedCompressionForce F w))‖^2 ≤
      primitiveEnergy (balancedCompressionForce F w)/21:=by
    have hh:=div_le_div_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 21)
    calc _=((2/n)*‖embed (phiRadiusAction (balancedCompressionForce F w))‖^2)/21:=by rw [←hc];ring
         _ ≤ _:=hh
  rw [hr]
  nlinarith only [he,hnon,hp']
end LowEnergy.BalancedInputPrimitivePayment
