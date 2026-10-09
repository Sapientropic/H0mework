import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaugeOuterQuadraticSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseScalarGaugeWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceScalarDoubleCurrent SourceScalarVirialBulk
open SourceCoframeVolume SourcePhysicalKineticSquare SourceGaugeRadius SourceGaugeRadiusMetric SourceGaugeRadialCurrent
open SourceGaugeRadialPair SourceClockPhiMatchedElectricSource SourceClockPhiOriginalGaussianH0RealPrimitives
open SourceClockPhiCombinedScalePressure FirstCurrentGeometricPayer SourceScalarShiftedBulk SourceScalarEssentialBudget
open SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceClockYukawaCubicCurrent ReverseNativeFrequencyWard ReverseGaugeOuterPayment
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev Ggen:End:=SourceGaugeScaleTransport.generator
private abbrev B:End:=scalarBulkComplete
private abbrev U:End:=inverseVolumeAction
private abbrev V:End:=volumeAction
private abbrev E:End:=electricAction
private abbrev CE:End:=fullElectricCurrent
private abbrev W:End:=magneticVolumeWeight
private abbrev X:End:=weightedElectricCurrent
attribute [local irreducible] sourcePair embed scalarBulkComplete diagonalAction compressionCore resolventCore
private theorem electric_smooth_local(z:physicalChart):ContDiffAt ℝ ∞ electricWeight z.val:=
  (reciprocal_volume_smooth z).mul (SourceGaugeRadialCurrent.electric_square_smooth z)
private theorem real_multiply(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest):
    (multiply c hc f:SourceCoordinateSlice→FockFiber)=(fun z=>c z • f z):=by
  funext z;apply PiLp.ext;intro word
  exact Complex.real_smul.symm
private theorem electric_gauge_derivative(z:physicalChart):
    fderiv ℝ electricWeight z.val (gaugeEuler z.val)=2*electricWeight z.val := by
  have hc:=((electric_smooth_local z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (gauge_scale_derivative z.val 1) (gauge_scale_one z.val).symm
  have hs(r:ℝ):electricWeight (gaugeScale r z.val)=r^2*electricWeight z.val:=by
    unfold electricWeight
    rw [electric_square_scale]
    change reciprocalVolume z.val*(r^2*electricSquare z.val)=_
    ring
  have ht:HasDerivAt (fun r:ℝ=>electricWeight (gaugeScale r z.val)) (2*electricWeight z.val) 1:=by
    simpa only [hs,id_eq,Pi.pow_apply,one_pow,mul_one,Nat.cast_ofNat,Nat.reduceSub] using!
      ((hasDerivAt_id (1:ℝ)).pow 2).mul_const (electricWeight z.val)
  exact hc.unique ht
private theorem electric_gauge:bracket Ggen electricAction=(2:ℂ) • electricAction := by
  have h:bracket gaugeEulerAction electricAction=(2:ℂ) • electricAction:=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    by_cases hz:z∈physicalChart
    · change gaugeEulerAction (electricAction f) z-(electricWeight z:ℂ) • gaugeEulerAction f z=(2:ℂ) • ((electricWeight z:ℂ) • f z)
      rw [gauge_euler_apply]
      change fderiv ℝ (multiply electricWeight electric_smooth_local f) z (gaugeEuler z)-_=_
      rw [real_multiply,
        fderiv_fun_smul ((electric_smooth_local ⟨z,hz⟩).differentiableAt (by simp))
          (f.contDiff.differentiable (by simp)).differentiableAt]
      change electricWeight z • fderiv ℝ f z (gaugeEuler z)+
        fderiv ℝ electricWeight z (gaugeEuler z) • f z-(electricWeight z:ℂ) • gaugeEulerAction f z=_
      rw [electric_gauge_derivative ⟨z,hz⟩,gauge_euler_apply]
      apply PiLp.ext;intro word
      simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul,smul_eq_mul]
      push_cast
      ring
    · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
      exact (h0 _).trans (h0 _).symm
  unfold Ggen SourceGaugeScaleTransport.generator bracket at *
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  linear_combination (norm:=module) h
private theorem electric_scalar_weight (t : ℝ) (z : SourceCoordinateSlice) :
    electricWeight (SourceScalarAffineScaleTransport.scaleEquiv t z) = electricWeight z := rfl

private theorem bracket_product(A C D:End):bracket A (C*D)=bracket A C*D+C*bracket A D:=by
  unfold bracket;noncomm_ring
private theorem bracket_smul_left(c:ℂ)(A C:End):bracket (c • A) C=c • bracket A C:=by
  unfold bracket;simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_smul_right(c:ℂ)(A C:End):bracket A (c • C)=c • bracket A C:=by
  unfold bracket;simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_jacobi(A C D:End):bracket A (bracket C D)=bracket (bracket A C) D+bracket C (bracket A D):=by
  unfold bracket;noncomm_ring
private theorem gauge_inverse:bracket G U=0:=by
  have h:=SourceGaugeScaleTransport.generator_commutator U
  have hi:=gauge_invariant_local U (fun z=>(reciprocalVolume z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _=>rfl) (fun _ _=>rfl)
  rw [hi] at h
  exact h
private theorem gauge_weight:bracket G W=0:=by
  have h:=SourceGaugeScaleTransport.generator_commutator W
  have hi:=gauge_invariant_local W (fun z=>((volume z^3:ℝ):ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _=>rfl) (fun _ _=>rfl)
  rw [hi] at h
  exact h
private theorem gauge_coframe_electric:bracket G coframeElectricCurrent=(2:ℂ) • coframeElectricCurrent:=by
  have hc:bracket G GaussCoframeForm.coframeAction=0:=by
    have h:=SourceGaugeScaleTransport.generator_commutator GaussCoframeForm.coframeAction
    rw [original_coframe_gauge] at h
    exact h
  unfold coframeElectricCurrent
  rw [bracket_smul_right,bracket_jacobi,hc,electric_gauge,bracket_smul_right]
  have hz:bracket (0:End) electricAction=0:=by unfold bracket;noncomm_ring
  rw [hz,zero_add]
  module
private theorem gauge_electric(F:Index)(g:diagonal.domain):bracket G CE=(2:ℂ) • CE+(2:ℂ) • (U*G):=by
  have he:CE=coframeElectricCurrent-U*G:=(actual_matched_electric_source 0 0 F Complex.I (by simp) g).1
  have hu:bracket G (U*G)=0:=by
    rw [bracket_product,gauge_inverse]
    have hg:bracket G G=0:=by unfold bracket;noncomm_ring
    rw [hg,mul_zero,zero_mul,add_zero]
  have hc:=gauge_coframe_electric
  rw [he]
  unfold bracket at hu hc ⊢
  linear_combination (norm:=(noncomm_ring;module)) hc-hu
private theorem weight_inverse:W*U=V^2 ∧ U*W=V^2:=by
  have hv:W=V*V*V:=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z;apply PiLp.ext;intro word
    change ((volume z^3:ℝ):ℂ)*f z word=(volume z:ℂ)*((volume z:ℂ)*((volume z:ℂ)*f z word))
    push_cast;ring
  have vu:V*U=(1:End):=LinearMap.ext volume_inverse
  have uv:U*V=(1:End):=by
    have hh:U*V=V*U:=by
      apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
      exact smul_comm (reciprocalVolume z:ℂ) (volume z:ℂ) (f z)
    exact hh.trans vu
  rw [hv]
  constructor
  · change V*V*(V*U)=V^2
    rw [vu,mul_one,pow_two]
  · change (U*V)*(V*V)=V^2
    rw [uv,one_mul,pow_two]

/-- The actual gauge action on the whole electric source closes on its original electric and volume-squared gauge words. -/
theorem actual_gauge_electric_outer(F:Index)(g:diagonal.domain):
    bracket G X=(2:ℂ) • X+(2:ℂ) • (V^2*G):=by
  have hg:G*W=W*G:=sub_eq_zero.mp gauge_weight
  have h1:W*(U*G)=V^2*G:=by
    change (W*U)*G=V^2*G
    rw [weight_inverse.1]
  have h2:(U*G)*W=V^2*G:=by
    change U*(G*W)=V^2*G
    rw [hg]
    change (U*W)*G=V^2*G
    rw [weight_inverse.2]
  unfold X weightedElectricCurrent
  have hadd(A C D:End):bracket A (C+D)=bracket A C+bracket A D:=by unfold bracket;noncomm_ring
  rw [bracket_smul_right,hadd,bracket_product,bracket_product,gauge_weight,gauge_electric F g]
  simp only [zero_mul,mul_zero,add_zero,zero_add,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,h1,h2,smul_add,smul_smul]
  module

/-- The scalar Ward generated by the same gauge flow has exactly zero real work. -/
theorem actual_scalar_gauge_zero(w:QuantumTest):(sourcePair (G w) (B w)).re=0:=by
  have hc:=LinearMap.congr_fun actual_gauge_scalar_commute.eq w
  change G (B w)=B (G w) at hc
  have hp:sourcePair (G w) (B w)= -sourcePair (B w) (G w):=by
    rw [actual_gauge_pair,hc,original_scalar_pair]
  have hr:=congrArg Complex.re hp
  simp only [Complex.neg_re] at hr
  have hs:(sourcePair (B w) (G w)).re=(sourcePair (G w) (B w)).re:=by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) (embed (B w)) (embed (G w))
  linarith

def gaugeCompressionForce(F:Index):End:=bracket G (compressionCore F)
theorem actual_gauge_compression_force(F:Index):
    gaugeCompressionForce F=bracket G diagonalAction-bracket G (defectAction F):=by
  unfold gaugeCompressionForce defectAction bracket
  noncomm_ring
private theorem inverse_commutator(A C R:End)(hL:R*C=1)(hR:C*R=1):bracket A R= -R*bracket A C*R:=by
  symm
  calc
    _= -(R*A*(C*R))+(R*C)*A*R:=by unfold bracket;noncomm_ring
    _=bracket A R:=by rw [hR,hL];unfold bracket;noncomm_ring

theorem actual_gauge_resolvent_ward(F:Index)(z:ℂ)(hz:z.im≠0):
    bracket G (resolventCore F z hz)= -resolventCore F z hz*gaugeCompressionForce F*resolventCore F z hz:=by
  have hi:=actual_original_cf_inverses F z hz
  have h:=inverse_commutator G (compressionCore F-z • (1:End)) (resolventCore F z hz) hi.2 hi.1
  have he:bracket G (compressionCore F-z • (1:End))=gaugeCompressionForce F:=by
    unfold gaugeCompressionForce bracket
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
    module
  rw [he] at h
  exact h

/-- The original CF response supplies the complete gauge source equation, including its own compression defect. -/
theorem actual_gauge_source_word(F:Index)(z:ℂ)(hz:z.im≠0)(L:End)(f:QuantumTest):
    G (L (resolventCore F z hz f))=
      bracket G L (resolventCore F z hz f)+L (resolventCore F z hz (G f))-
        L (resolventCore F z hz (gaugeCompressionForce F (resolventCore F z hz f))):=by
  have h:=congrArg L (LinearMap.congr_fun (actual_gauge_resolvent_ward F z hz) f)
  simp only [bracket,LinearMap.sub_apply,LinearMap.neg_apply,Module.End.mul_apply,map_sub,map_neg] at h ⊢
  linear_combination (norm:=module) h
end LowEnergy.ReverseScalarGaugeWard
