import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0FirstJet
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceClockPhiOriginalGaussianH0Recognition
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy SourceCoframeVolume
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiOriginalGaussianH0FirstJet SourceClockPhiMatchedDiffusionSource
open SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure
open SourceScalarVirialBulk
open SourceScalarGaugeScale
open SourceScalarDoubleCurrent
open Filter
open scoped Topology InnerProductSpace ContDiff
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev V:End:=volumeAction
private abbrev D:End:=combinedGenerator

private theorem inverse_volume_left(q:QuantumTest):U (V q)=q:=by
  have hc:U (V q)=V (U q):=by
    apply DFunLike.ext
    intro z
    exact smul_comm (reciprocalVolume z:ℂ) (volume z:ℂ) (q z)
  rw [hc,volume_inverse]
private theorem combined_inverse_commute:Commute D U:=by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator U
  have hg:=SourceGaugeScaleTransport.generator_commutator U
  rw [SourceScalarInverseBulk.inverse_phi] at hp
  rw [SourceScalarInverseBulk.inverse_gauge] at hg
  change (SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)*U=
    U*(SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)
  linear_combination (norm:=noncomm_ring) hp-hg
private theorem flow_pair_generator (flow:ℝ→End)(G:End)
    (hzero:∀f,flow 0 f=f)
    (hpair:∀t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv:∀f,HasDerivAt (fun t:ℝ=>embed (flow t f)) (embed (G f)) 0)
    (f g:QuantumTest):sourcePair f (G g)= -sourcePair (G f) g:=by
  unfold sourcePair at hpair ⊢
  have h:=(hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he:(fun t:ℝ=>inner ℂ (embed (flow t f)) (embed (flow t g)))=
      fun _=>inner ℂ (embed f) (embed g):=funext (fun t=>hpair t f g)
  rw [he] at h
  have heq:=h.unique (hasDerivAt_const (0:ℝ) (inner ℂ (embed f) (embed g)))
  exact eq_neg_of_add_eq_zero_left heq
private theorem phi_pair(f g:QuantumTest):
    sourcePair f (SourceScalarAffineScaleTransport.generator g)=
      -sourcePair (SourceScalarAffineScaleTransport.generator f) g:=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow
    SourceScalarAffineScaleTransport.generator
    SourceScalarAffineScaleTransport.coreFlow_zero
    SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
private theorem gauge_pair(f g:QuantumTest):
    sourcePair f (SourceGaugeScaleTransport.generator g)=
      -sourcePair (SourceGaugeScaleTransport.generator f) g:=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow
    SourceGaugeScaleTransport.generator
    SourceGaugeScaleTransport.coreFlow_zero
    SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
private theorem combined_pair_source(f g:QuantumTest):sourcePair f (D g)= -sourcePair (D f) g:=by
  have hp:=phi_pair f g
  have hg:=gauge_pair f g
  change sourcePair f (SourceScalarAffineScaleTransport.generator g-
      SourceGaugeScaleTransport.generator g)=
    -sourcePair (SourceScalarAffineScaleTransport.generator f-
      SourceGaugeScaleTransport.generator f) g
  simp only [sourcePair,map_sub,inner_sub_left,inner_sub_right] at hp hg ⊢
  linear_combination hp-hg
private theorem combined_pair(f g:QuantumTest):sourcePair (D f) g= -sourcePair f (D g):=by
  simpa only [neg_neg] using congrArg Neg.neg (combined_pair_source f g).symm

theorem stochastic_jet_operator(f g:QuantumTest):
    stochasticPairJet f g=
      sourcePair f (((-3*sourceTime 0/8:ℂ) • (U*U*D*D)) g):=by
  have hc(q:QuantumTest):D (U q)=U (D q):=
    LinearMap.congr_fun combined_inverse_commute.eq q
  have hc2(q:QuantumTest):D (U (U q))=U (U (D q)):=by rw [hc,hc]
  unfold stochasticPairJet
  change (sourceTime 0/48:ℂ)*((18:ℂ)*sourcePair (D f)
    (U (U (U (V (D g))))))=_
  rw [inverse_volume_left,combined_pair f (U (U (D g))),hc2]
  simp only [Module.End.mul_apply,LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right]
  ring

private abbrev A:End:=combinedConjugate
private abbrev Dc:End:=SourceCoframeVolumeCurrent.dilation
private theorem inverse_volume_right:V*U=(1:End):=by
  apply LinearMap.ext
  exact volume_inverse
private theorem inverse_volume_left_op:U*V=(1:End):=by
  apply LinearMap.ext
  exact inverse_volume_left
private theorem combined_volume_commute:Commute D V:=by
  have hd:=congrArg (fun T:End=>V*T*V) combined_inverse_commute.eq
  change V*(D*U)*V=V*(U*D)*V at hd
  have h1:=inverse_volume_right
  have h2:=inverse_volume_left_op
  calc
    D*V=V*(U*D)*V:=by
      calc
        D*V=(V*U)*(D*V):=by rw [h1,one_mul]
        _=_:=by noncomm_ring
    _=V*(D*U)*V:=hd.symm
    _=V*D:=by
      calc
        V*(D*U)*V=(V*D)*(U*V):=by noncomm_ring
        _=_:=by rw [h2,mul_one]
private theorem root_volume_commute:Commute inverseRootAction V:=by
  apply LinearMap.ext
  intro q
  apply DFunLike.ext
  intro z
  exact smul_comm (inverseRootVolume z:ℂ) (volume z:ℂ) (q z)
private theorem conjugate_volume_commute:Commute A V:=by
  change Commute (inverseRootAction*D) V
  exact root_volume_commute.mul_left combined_volume_commute
private theorem drift_volume:
    SourceClockPhiMatchedDiffusionSource.driftClock*V-
      V*SourceClockPhiMatchedDiffusionSource.driftClock=(6:ℂ) • (1:End):=by
  have hd:=SourceDilationKinetic.volume_scale_current
  have hU:=inverse_volume_left_op
  have hV:=inverse_volume_right
  have hD:=combined_volume_commute.eq
  have hC:((Dc*U)*V-V*(Dc*U))=(-2*Complex.I) • (1:End):=by
    have hh:=congrArg (fun T:End=>T*U) hd
    change (Dc*V-V*Dc)*U=((-2*Complex.I) • V)*U at hh
    simp only [sub_mul,smul_mul_assoc,hV] at hh
    calc
      (Dc*U)*V-V*(Dc*U)=Dc-V*(Dc*U):=by
        calc
          (Dc*U)*V-V*(Dc*U)=Dc*(U*V)-V*(Dc*U):=by noncomm_ring
          _=_:=by rw [hU,mul_one]
      _=(Dc*V-V*Dc)*U:=by
        calc
          Dc-V*(Dc*U)=Dc*(V*U)-V*(Dc*U):=by rw [hV,mul_one]
          _=_:=by noncomm_ring
      _=_:=hh
  change (U*D+(3*Complex.I:ℂ) • (Dc*U)+(3:ℂ) • U)*V-
    V*(U*D+(3*Complex.I:ℂ) • (Dc*U)+(3:ℂ) • U)=(6:ℂ) • (1:End)
  simp only [add_mul,mul_add,mul_smul_comm,smul_mul_assoc]
  have hDU:U*D*V-V*U*D=0:=by
    calc
      U*D*V-V*U*D=U*(D*V)-(V*U)*D:=by noncomm_ring
      _=U*(V*D)-(V*U)*D:=by rw [hD]
      _=(U*V)*D-(V*U)*D:=by noncomm_ring
      _=0:=by rw [hU,hV];module
  have hUU:U*V-V*U=0:=by rw [hU,hV];module
  have hi:(3:ℂ)*Complex.I*(-2*Complex.I)=6:=by
    calc _= -6*(Complex.I*Complex.I):=by ring
         _=6:=by rw [Complex.I_mul_I];ring
  have hC':(3*Complex.I:ℂ) • ((Dc*U)*V-V*(Dc*U))=(6:ℂ) • (1:End):=by
    rw [hC,smul_smul,hi]
  linear_combination (norm:=noncomm_ring) hDU+hC'+3*hUU
  all_goals module

theorem complete_current_volume:
    SourceClockPhiMatchedDiffusionSource.completeCurrent V=(24:ℂ) • (1:End):=by
  have hc:=conjugate_volume_commute.eq
  have hd:=drift_volume
  have hU:=inverse_volume_left_op
  have hV:=inverse_volume_right
  unfold SourceClockPhiMatchedDiffusionSource.completeCurrent
    SourceClockPhiMatchedDiffusionSource.diffusionCurrent
    SourceClockPhiMatchedDiffusionSource.diffusionDrift
    SourceClockPhiMatchedDiffusionSource.diffusionDriftTranspose
  change ((A*A+(3:ℂ) • SourceClockPhiMatchedDiffusionSource.driftClock)*V+
    V*(A*A-(3:ℂ) • SourceClockPhiMatchedDiffusionSource.driftClock)-
    (2:ℂ) • (A*V*A)+(3:ℂ) • (U*V+V*U))=(24:ℂ) • (1:End)
  simp only [add_mul,mul_sub,mul_smul_comm,smul_mul_assoc,smul_add]
  linear_combination (norm:=noncomm_ring) A*hc-hc*A+3*hd+3*hU+3*hV
  all_goals module

private theorem conjugate_root_commute:Commute A inverseRootAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have he(t:ℝ):ClockPhiMatchedNoiseCore.noiseCore t 0 (inverseRootAction f) z word=
      (inverseRootVolume z:ℂ)*ClockPhiMatchedNoiseCore.noiseCore t 0 f z word:=by
    have h:=LinearMap.congr_fun (ClockPhiMatchedNoiseCore.noiseCore_root t 0).eq f
    exact congrArg (fun q:QuantumTest=>q z word) h
  have hl:=ClockPhiMatchedNoiseCore.noise_linear_zero_jet 1 0
    (inverseRootAction f) z word
  have hr:=(ClockPhiMatchedNoiseCore.noise_linear_zero_jet 1 0 f z word).const_mul
    (inverseRootVolume z:ℂ)
  simp only [mul_one,mul_zero] at hl hr
  have hfun:(fun t:ℝ=>ClockPhiMatchedNoiseCore.noiseCore t 0 (inverseRootAction f) z word)=
      fun t:ℝ=>(inverseRootVolume z:ℂ)*ClockPhiMatchedNoiseCore.noiseCore t 0 f z word:=
    funext he
  rw [hfun] at hl
  have hh:=hl.unique hr
  change A (inverseRootAction f) z word=(inverseRootVolume z:ℂ)*A f z word
  simpa only [A,combinedConjugate,ClockPhiMatchedNoiseCore.noiseGenerator,
    Complex.ofReal_one,Complex.ofReal_zero,one_smul,zero_smul,
    ClockPhiMatchedNoiseCore.parameter,one_mul,zero_mul,add_zero]
    using hh

private abbrev a:End:=inverseRootAction
private abbrev LV:End:=SourceClockPhiCoframeForwardCore.forwardGenerator
private theorem root_square:a*a=U:=by
  apply LinearMap.ext
  exact inverse_root_square
private theorem drift_forward:
    SourceClockPhiMatchedDiffusionSource.driftClock=U*D-(1/3:ℂ) • LV:=by
  change SourceClockPhiMatchedDiffusionSource.driftClock=
    U*D-(1/3:ℂ) • SourceClockPhiCoframeForwardCore.forwardGenerator
  rw [SourceClockPhiCoframeForwardCore.forwardGenerator_original]
  unfold SourceClockPhiMatchedDiffusionSource.driftClock
    SourceClockPhiNativeMatchedSource.matchedColumn
  module

private theorem bracket_left_mul (X Y Z:End):
    bracket (X*Y) Z=X*bracket Y Z+bracket X Z*Y:=by
  unfold bracket
  noncomm_ring
private theorem bracket_right_mul (X Y Z:End):
    bracket X (Y*Z)=bracket X Y*Z+Y*bracket X Z:=by
  unfold bracket
  noncomm_ring
private theorem bracket_sub_right (X Y Z:End):
    bracket X (Y-Z)=bracket X Y-bracket X Z:=by
  unfold bracket
  noncomm_ring
private theorem bracket_smul_right (X Y:End)(c:ℂ):
    bracket X (c • Y)=c • bracket X Y:=by
  unfold bracket
  simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bracket_sub_left (X Y Z:End):
    bracket (X-Y) Z=bracket X Z-bracket Y Z:=by
  unfold bracket
  noncomm_ring
private theorem bracket_smul_left (X Y:End)(c:ℂ):
    bracket (c • X) Y=c • bracket X Y:=by
  unfold bracket
  simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem complete_current_bracket(X:End):
    completeCurrent X=bracket A (bracket A X)+
      (3:ℂ) • bracket SourceClockPhiMatchedDiffusionSource.driftClock X+
      (3:ℂ) • (U*X+X*U):=by
  unfold completeCurrent diffusionCurrent diffusionDriftTranspose diffusionDrift bracket
  noncomm_ring
  module

theorem complete_current_homogeneous(T:End)(p q:ℂ)
    (hUT:Commute U T)(haT:Commute a T)
    (hDT:bracket D T=(-q) • T)
    (hLT:bracket LV T=(-18*(p-1/3)) • (U*T)):
    completeCurrent T=(q*q-3*q+18*p) • (U*T):=by
  have hAT:bracket A T=(-q) • (a*T):=by
    change bracket (a*D) T=_
    rw [bracket_left_mul,hDT,show bracket a T=0 from sub_eq_zero.mpr haT.eq]
    simp only [zero_mul,add_zero,mul_smul_comm]
  have hAat:bracket A (a*T)=(-q) • (U*T):=by
    rw [bracket_right_mul,show bracket A a=0 from
      sub_eq_zero.mpr conjugate_root_commute.eq,hAT]
    simp only [zero_mul,zero_add,mul_smul_comm,←mul_assoc,root_square]
  have hAA:bracket A (bracket A T)=(q*q) • (U*T):=by
    rw [hAT,bracket_smul_right,hAat,smul_smul]
    congr 1
    ring
  have hBT:bracket SourceClockPhiMatchedDiffusionSource.driftClock T=
      (-q+6*(p-1/3)) • (U*T):=by
    rw [drift_forward]
    change (U*D-(1/3:ℂ) • LV)*T-T*(U*D-(1/3:ℂ) • LV)=_
    have hzU:U*T-T*U=0:=sub_eq_zero.mpr hUT.eq
    have hzD:D*T-T*D=(-q) • T:=hDT
    change LV*T-T*LV=(-18*(p-1/3)) • (U*T) at hLT
    calc
      _=U*(D*T-T*D)+(U*T-T*U)*D-(1/3:ℂ) • (LV*T-T*LV):=by
        simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
        noncomm_ring
        module
      _=_:=by
        rw [hzD,hzU,hLT]
        simp only [zero_mul,add_zero,mul_smul_comm,smul_smul]
        module
  rw [complete_current_bracket,hAA,hBT]
  have hTU:T*U=U*T:=hUT.eq.symm
  rw [hTU]
  simp only [smul_add,smul_smul]
  module

theorem forward_bracket_of_scale(T:End)(r:ℂ)(hUT:Commute U T)
    (hScale:SourceHamiltonianScaleJet.scaleDerivative T=r • T):
    bracket LV T=(-6*r) • (U*T):=by
  have hDc:bracket (Dc*U) T=bracket Dc T*U:=by
    unfold bracket
    change Dc*(U*T)-T*(Dc*U)=(Dc*T-T*Dc)*U
    rw [hUT.eq]
    noncomm_ring
  have hs:((3*Complex.I/2:ℂ) • (Dc*T-T*Dc))*U=(r • T)*U:=by
    exact congrArg (fun X:End=>X*U) hScale
  have hh:=congrArg (fun X:End=>(-6:ℂ) • X) hs
  simp only [smul_mul_assoc,smul_smul] at hh
  have he:(-9*Complex.I:ℂ) • ((Dc*T-T*Dc)*U)=(-6*r) • (U*T):=by
    convert hh using 1
    · congr 1
      ring
    · rw [←hUT.eq]
  change bracket SourceClockPhiCoframeForwardCore.forwardGenerator T=_
  rw [SourceClockPhiCoframeForwardCore.forwardGenerator_original]
  rw [bracket_sub_left,bracket_smul_left,bracket_smul_left,hDc,
    show bracket U T=0 from sub_eq_zero.mpr hUT.eq]
  simp only [smul_zero,sub_zero]
  exact he

theorem complete_current_real_multiplier(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(p q:ℂ)
    (hD:deltaPhi (GaussNativeForm.multiply b hb)-
      deltaGauge (GaussNativeForm.multiply b hb)=(-q) • (GaussNativeForm.multiply b hb))
    (hScale:SourceHamiltonianScaleJet.scaleDerivative (GaussNativeForm.multiply b hb)=
      (3*p-1) • (GaussNativeForm.multiply b hb)):
    completeCurrent (GaussNativeForm.multiply b hb)=
      (q*q-3*q+18*p) • (U*(GaussNativeForm.multiply b hb)):=by
  let T:End:=GaussNativeForm.multiply b hb
  have hUT:Commute U T:=by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (reciprocalVolume z:ℂ) (b z:ℂ) (f z)
  have haT:Commute a T:=by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (inverseRootVolume z:ℂ) (b z:ℂ) (f z)
  have hDsrc:bracket D T=deltaPhi T-deltaGauge T:=by
    have hp:=SourceScalarAffineScaleTransport.generator_commutator T
    have hg:=SourceGaugeScaleTransport.generator_commutator T
    calc
      bracket D T=(SourceScalarAffineScaleTransport.generator*T-
        T*SourceScalarAffineScaleTransport.generator)-
        (SourceGaugeScaleTransport.generator*T-
          T*SourceGaugeScaleTransport.generator):=by
          unfold bracket D combinedGenerator
          noncomm_ring
      _=_:=by rw [hp,hg]
  have hDT:bracket D T=(-q) • T:=by rw [hDsrc];exact hD
  have hLT:bracket LV T=(-18*(p-1/3)) • (U*T):=by
    have h:=forward_bracket_of_scale T (3*p-1) hUT hScale
    convert h using 1
    congr 1
    ring
  exact complete_current_homogeneous T p q hUT haT hDT hLT

end LowEnergy.SourceClockPhiOriginalGaussianH0Recognition
