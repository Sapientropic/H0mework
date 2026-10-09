import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFullReverseScaleNoetherCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseCompressionWard
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseForceNoetherPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockYukawaCubicCurrent SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget SourceScalarVirialBulk SourceScalarSpatialCurrent
open SourceCoframeVolumeCurrent SourceCoframeDilation SourceScalarPairedTransport
open ReverseNativeClock ReverseNativeFrequencyWard FullYSourceResolventGraphSplice
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev Z:End:=reverseNativeClock
private abbrev B:End:=scalarBulkComplete
private abbrev U:End:=inverseVolumeAction
private abbrev H0:End:=diagonalAction
attribute [local irreducible] sourcePair embed diagonalAction compressionCore resolventCore
  reverseNativeClock reverseScaleForce reverseCompressionForce scalarBulkComplete
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=(starRingEnd ℂ) c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem flow_pair_generator(flow:ℝ→End)(G:End)
    (hzero:∀f,flow 0 f=f)(hpair:∀t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv:∀f,HasDerivAt (fun t:ℝ=>embed (flow t f)) (embed (G f)) 0)(f g:QuantumTest):
    sourcePair f (G g)= -sourcePair (G f) g:=by
  unfold sourcePair at hpair ⊢
  have h:=(hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he:(fun t:ℝ=>inner ℂ (embed (flow t f)) (embed (flow t g)))=fun _=>inner ℂ (embed f) (embed g):=
    funext (fun t=>hpair t f g)
  rw [he] at h
  exact eq_neg_of_add_eq_zero_left (h.unique (hasDerivAt_const (0:ℝ) (inner ℂ (embed f) (embed g))))
private theorem reverse_pair(f g:QuantumTest):sourcePair (Z f) g= -sourcePair f (Z g):=by
  have hp:=flow_pair_generator SourceScalarAffineScaleTransport.coreFlow SourceScalarAffineScaleTransport.generator
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
  have hg:=flow_pair_generator SourceGaugeScaleTransport.coreFlow SourceGaugeScaleTransport.generator
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
  have hd:=dilation_pair f g
  unfold Z reverseNativeClock
  change sourcePair (((3:ℂ) • (SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)-
    (9*Complex.I:ℂ) • dilation) f) g=
    -sourcePair f (((3:ℂ) • (SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)-
      (9*Complex.I:ℂ) • dilation) g)
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_l,pair_sub_r,pair_smul_l,pair_smul_r,
    map_mul,Complex.conj_ofNat,Complex.conj_I]
  linear_combination 3*hp-3*hg-9*Complex.I*hd
private theorem compression_pair(F:Index)(f g:QuantumTest):
    sourcePair f (compressionCore F g)=sourcePair (compressionCore F f) g:=by
  have he(q:QuantumTest):embed (compressionCore F q)=GaussGradedCompression.compression F (embed q):=by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [sourcePair,he]
  exact (GaussGradedCompression.compression_pair F (embed f) (embed g)).symm
private theorem force_pair_from(T:End)(hT:∀f g,sourcePair f (T g)=sourcePair (T f) g)(f g:QuantumTest):
    sourcePair ((bracket Z T-(18:ℂ) • T) f) g=
      sourcePair f ((bracket Z T-(18:ℂ) • T) g):=by
  simp only [bracket,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    pair_sub_l,pair_sub_r,pair_smul_l,pair_smul_r,Complex.conj_ofNat]
  rw [reverse_pair (T f) g,←hT f (Z g),←hT (Z f) g,reverse_pair f (T g),←hT f g]
  ring

/-- The complete compression force is a real source action; its delta_Z is not supplied as a separate symmetric operator. -/
theorem actual_compression_force_pair(F:Index)(f g:QuantumTest):
    sourcePair (reverseCompressionForce F f) g=sourcePair f (reverseCompressionForce F g):=by
  have he:reverseCompressionForce F=bracket Z (compressionCore F)-(18:ℂ) • compressionCore F:=by
    rw [actual_reverse_compression_scale]
    module
  rw [he]
  exact force_pair_from _ (compression_pair F) f g

def forceScalarProjectionCurrent(F:Index):End:=
  (18:ℂ) • bracket (defectAction F) B-bracket (bracket Z (defectAction F)) B
/-- The native source current and the whole compression delta_Z meet in one actual scalar force. -/
theorem actual_compression_force_scalar_current(F:Index):
    bracket (reverseCompressionForce F) B=
      (-18:ℂ) • SourceScalarOscillatorAbsorption.scalarCurrent-
        (192:ℂ) • (U*scalarSpatialDivergence)+forceScalarProjectionCurrent F:=by
  have h:=actual_reverse_force_scalar_current
  unfold reverseCompressionForce forceScalarProjectionCurrent
  unfold bracket at h ⊢
  simp only [add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
  linear_combination (norm:=module) h
private theorem force_current_pair(F:Index)(w:QuantumTest):
    2*(sourcePair (reverseCompressionForce F w) (B w)).im=
      (sourcePair w (bracket (reverseCompressionForce F) B w)).im:=by
  have h1:=actual_compression_force_pair F w (B w)
  have h2:=original_scalar_pair w (reverseCompressionForce F w)
  have hc:(sourcePair (B w) (reverseCompressionForce F w)).im= -(sourcePair (reverseCompressionForce F w) (B w)).im:=by
    simpa only [Complex.conj_im] using (congrArg Complex.im (GaussNativeForm.pair_conjugate (reverseCompressionForce F w) (B w))).symm
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r,Complex.sub_im,h1.symm,h2,hc]
  ring

/-- No force norm is estimated: the imaginary scalar force price is exactly its native current and its own projection current. -/
theorem actual_compression_force_scalar_price(F:Index)(w:QuantumTest):
    (sourcePair (reverseCompressionForce F w) (B w)).im=
      -9*(sourcePair w (SourceScalarOscillatorAbsorption.scalarCurrent w)).im-
        96*(sourcePair w (U (scalarSpatialDivergence w))).im+
          (sourcePair w (forceScalarProjectionCurrent F w)).im/2:=by
  have h:=force_current_pair F w
  rw [actual_compression_force_scalar_current] at h
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    pair_add_r,pair_sub_r,pair_smul_r,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.re_ofNat,
    Complex.im_ofNat,Complex.neg_re,Complex.neg_im,zero_mul,add_zero] at h
  linarith only [h]

theorem actual_full_source_mixed_scalar_noether(z:ℂ)(w f v p:QuantumTest)
    (hw:H0 w=f+z • w)(hv:H0 v=p+z • v):
    2*z.im*(sourcePair v (B w)).re=
      (sourcePair p (B w)).im-(sourcePair (B v) f).im-(sourcePair v (bracket H0 B w)).im:=by
  have h:sourcePair p (B w)-sourcePair (B v) f-sourcePair v (bracket H0 B w)=
      (z-(starRingEnd ℂ) z)*sourcePair v (B w):=by
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r]
    rw [diagonalAction_pair v (B w),original_scalar_pair v (H0 w),hv,hw]
    simp only [pair_add_l,pair_add_r,pair_smul_l,pair_smul_r]
    rw [←original_scalar_pair v w]
    ring
  have hi:=congrArg Complex.im h
  simp only [Complex.sub_im,Complex.mul_im,Complex.sub_re,Complex.conj_re,Complex.conj_im,
    sub_self,zero_mul,zero_add] at hi
  linarith only [hi]

def forceResponse(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):QuantumTest:=
  resolventCore F z hz (reverseCompressionForce F (resolventCore F z hz f))
private theorem response_equation(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    H0 (resolventCore F z hz f)=f+defectAction F (resolventCore F z hz f)+z • resolventCore F z hz f:=by
  have h:=LinearMap.congr_fun (actual_original_cf_inverses F z hz).1 f
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,Module.End.one_apply] at h
  unfold defectAction
  simp only [LinearMap.sub_apply]
  linear_combination (norm:=module) h

/-- The original force response carries the full H0 forcing on both legs. The seed, delta, native force current, and geometric scalar current remain in one signed debit. -/
theorem actual_force_response_full_noether(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    let w:=resolventCore F z hz f
    let v:=forceResponse F z hz f
    H0 w=f+defectAction F w+z • w ∧
    H0 v=reverseCompressionForce F w+defectAction F v+z • v ∧
    2*z.im*(sourcePair v (B w)).re=
      -9*(sourcePair w (SourceScalarOscillatorAbsorption.scalarCurrent w)).im-
        96*(sourcePair w (U (scalarSpatialDivergence w))).im+
          (sourcePair w (forceScalarProjectionCurrent F w)).im/2+
          (sourcePair (defectAction F v) (B w)).im-
          (sourcePair (B v) (f+defectAction F w)).im-(sourcePair v (bracket H0 B w)).im:=by
  dsimp only
  have hw:=response_equation F z hz f
  have hv:=response_equation F z hz (reverseCompressionForce F (resolventCore F z hz f))
  refine ⟨hw,hv,?_⟩
  have h:=actual_full_source_mixed_scalar_noether z _ (f+defectAction F (resolventCore F z hz f)) _
    (reverseCompressionForce F (resolventCore F z hz f)+defectAction F (forceResponse F z hz f)) hw hv
  rw [pair_add_l,Complex.add_im,actual_compression_force_scalar_price] at h
  exact h
end LowEnergy.ReverseForceNoetherPayer
