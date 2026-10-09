import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedPrimitiveAccelerationSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedWholeForceDebit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarBalancedPrimitive
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore SourceQuantumConfigurationHilbert
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarPairedTransport SourceDilationRemainder SourcePhysicalKineticSquare
open SourceClockPhiRadiusAcceleration SourceClockPhiRadiusSourceCurrent SourceClockPhiMatchedElectricSource
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare ReverseNativeClock ReverseScalarGaugeWard ReverseBalancedForcePayer
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev Phi:End:=SourceScalarAffineScaleTransport.generator
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev P:End:=positivePrimitive
private abbrev A:End:=gaugeBalancedNativeForce
private abbrev Zbar:End:=reverseNativeClock-(9:ℂ) • G
attribute [local irreducible] sourcePair embed diagonalAction scalarKinetic gaugeKinetic matterAction
  gaugeBalancedNativeForce positivePrimitive balancedCompressionForce
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_neg_r(f g:QuantumTest):sourcePair f (-g)= -sourcePair f g:=by simp only [sourcePair,map_neg,inner_neg_right]
private theorem primitive_pair(f g:QuantumTest):sourcePair f (P g)=sourcePair (P f) g:=by
  have hp(a b:QuantumTest):sourcePair a (phiSquare b)=sourcePair (phiSquare a) b:=by
    change sourcePair a (phiRadiusAction (phiRadiusAction b))=sourcePair (phiRadiusAction (phiRadiusAction a)) b
    have hr(c d:QuantumTest):sourcePair c (phiRadiusAction d)=sourcePair (phiRadiusAction c) d:=multiply_pair _ _ _ _
    rw [hr,hr]
  have he(a b:QuantumTest):sourcePair a (electricAction b)=sourcePair (electricAction a) b:=multiply_pair _ _ _ _
  unfold P positivePrimitive
  simp only [LinearMap.add_apply,LinearMap.smul_apply,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,
    hp,he,Complex.star_def,map_div₀,map_ofNat,map_one,Complex.conj_ofReal]

/-- The full signed native force is symmetric on the actual original test space. -/
theorem actual_balanced_native_pair(f g:QuantumTest):sourcePair f (A g)=sourcePair (A f) g:=by
  have hc(a b:QuantumTest):sourcePair a (centeredAction b)=sourcePair (centeredAction a) b:=multiply_pair _ _ _ _
  have hv(a b:QuantumTest):sourcePair a (vacuumLinearAction b)=sourcePair (vacuumLinearAction a) b:=multiply_pair _ _ _ _
  have hm(a b:QuantumTest):sourcePair a (magneticAction b)=sourcePair (magneticAction a) b:=multiply_pair _ _ _ _
  have hl(a b:QuantumTest):sourcePair a (localAction b)=sourcePair (localAction a) b:=multiply_pair _ _ _ _
  have hs(a b:QuantumTest):sourcePair a (scalarSpatialAction b)=sourcePair (scalarSpatialAction a) b:=multiply_pair _ _ _ _
  rw [show A=gaugeBalancedNativeForce from rfl,actual_balanced_native_departments]
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,pair_sub_l,pair_sub_r,
    pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,scalarKinetic_pair,matter_pair,hc,hv,hm,hl,hs,
    Complex.star_def,map_neg,map_ofNat]

private theorem acceleration_pair(T:End)
    (hT:∀f g,sourcePair f (T g)=sourcePair (T f) g)(w:QuantumTest):
    (sourcePair w (-bracket T (bracket T P) w)).re=
      2*primitiveEnergy (T w)-2*(sourcePair (T (T w)) (P w)).re:=by
  have hx:sourcePair w (-bracket T (bracket T P) w)=
      -sourcePair (T (T w)) (P w)+2*sourcePair (T w) (P (T w))-
        sourcePair (P w) (T (T w)):=by
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub,
      pair_neg_r,pair_sub_r,hT,primitive_pair]
    ring
  have hc:=congrArg Complex.re (GaussNativeForm.pair_conjugate (T (T w)) (P w))
  rw [hx]
  simp only [Complex.conj_re] at hc
  simp only [Complex.sub_re,Complex.add_re,Complex.neg_re,Complex.mul_re,Complex.re_ofNat,
    Complex.im_ofNat,zero_mul,sub_zero,primitiveEnergy,P]
  linarith only [hc]

/-- The negative force acceleration is the difference of two ordered positive-primitive energies. -/
theorem actual_balanced_native_primitive_pair(w:QuantumTest):
    (sourcePair w (balancedPrimitiveAcceleration w)).re=
      2*primitiveEnergy (A w)-2*(sourcePair (A (A w)) (P w)).re:=by
  rw [←actual_balanced_primitive_acceleration]
  exact acceleration_pair A actual_balanced_native_pair w

/-- The same acceleration is a first-current ordered pair; no independent force-square budget is required. -/
theorem actual_balanced_native_first_current_pair(w:QuantumTest):
    (sourcePair w (balancedPrimitiveAcceleration w)).re=
      12*(sourcePair (A w) (U (Phi w))).re:=by
  have h:=congrArg (fun v=>sourcePair (A w) v)
    (LinearMap.congr_fun actual_balanced_primitive_current w)
  simp only [bracket,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    pair_sub_r,pair_smul_r,actual_balanced_native_pair] at h
  have hr:=congrArg Complex.re h
  simp only [Complex.sub_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.re_ofNat,Complex.im_ofNat,neg_zero,zero_mul,sub_zero] at hr
  rw [actual_balanced_native_primitive_pair]
  change 2*(sourcePair (A w) (P (A w))).re-2*(sourcePair (A (A w)) (P w)).re=_
  linarith only [hr]

/-- This is exactly the same own-compression defect carried by the compensated frequency Ward. -/
def balancedOwnDefect(F:Index):End:=
  (18:ℂ) • defectAction F-bracket Zbar (defectAction F)
def balancedPrimitiveProjection(F:Index):End:=
  bracket A (bracket (balancedOwnDefect F) P)+
    bracket (balancedOwnDefect F) (bracket A P)+
    bracket (balancedOwnDefect F) (bracket (balancedOwnDefect F) P)
private theorem compression_split(F:Index):balancedCompressionForce F=A+balancedOwnDefect F:=by
  have h:=actual_balanced_compression_departments F
  unfold A gaugeBalancedNativeForce balancedOwnDefect Zbar
  linear_combination (norm:=module) h

/-- All three own-defect currents survive the full-CF primitive acceleration. -/
theorem actual_balanced_compression_primitive_acceleration(F:Index):
    -bracket (balancedCompressionForce F) (bracket (balancedCompressionForce F) P)=
      balancedPrimitiveAcceleration-balancedPrimitiveProjection F:=by
  rw [compression_split,←actual_balanced_primitive_acceleration]
  unfold balancedPrimitiveProjection bracket
  noncomm_ring

theorem actual_balanced_compression_primitive_pair(F:Index)(w:QuantumTest):
    (sourcePair w (balancedPrimitiveAcceleration w)).re=
      2*primitiveEnergy (balancedCompressionForce F w)-
      2*(sourcePair (balancedCompressionForce F (balancedCompressionForce F w)) (P w)).re+
      (sourcePair w (balancedPrimitiveProjection F w)).re:=by
  have h:=acceleration_pair (balancedCompressionForce F)
    (fun f g=>(actual_balanced_compression_pair F f g).symm) w
  have he:=congrArg (fun T:End=>(sourcePair w (T w)).re)
    (actual_balanced_compression_primitive_acceleration F)
  have ht:=he.symm.trans h
  simp only [LinearMap.sub_apply,pair_sub_r,Complex.sub_re] at ht
  linarith only [ht]

/-- The actual signed spatial term is paid by the negative primitive square and its ordered force/source remainder, with the whole own-CF defect retained. -/
theorem actual_balanced_scalar_spatial_payment(F:Index)(w:QuantumTest):
    -12*(sourcePair w (U (scalarSpatialAction w))).re=
      -(1/21:ℝ)*primitiveEnergy (balancedCompressionForce F w)+
      (1/21:ℝ)*(sourcePair (balancedCompressionForce F (balancedCompressionForce F w)) (P w)).re-
      (1/42:ℝ)*(sourcePair w (balancedPrimitiveProjection F w)).re-
      (12/7:ℝ)*(sourcePair w (U (scalarKinetic w))).re+
      (60/7:ℝ)*(sourcePair w (U (centeredAction w))).re-
      (66/7:ℝ)*(sourcePair w (U (vacuumLinearAction w))).re:=by
  have h:=actual_balanced_compression_primitive_pair F w
  unfold balancedPrimitiveAcceleration at h
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    pair_add_r,pair_sub_r,pair_smul_r,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.neg_re,
    Complex.neg_im,Complex.re_ofNat,Complex.im_ofNat,neg_zero,zero_mul,sub_zero] at h
  linear_combination (norm:=ring) -(1/42:ℝ)*h
end LowEnergy.ScalarBalancedPrimitive
