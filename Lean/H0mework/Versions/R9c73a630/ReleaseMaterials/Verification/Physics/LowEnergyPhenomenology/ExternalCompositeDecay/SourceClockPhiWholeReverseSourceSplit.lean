import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseInputCommonPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseWholeClockFubini
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNoetherCausalPrice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeOuterSource
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussLiveMomentum
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceClockYukawaCubicCurrent SourceClockPhiNormalizedScalarBudget
open SourceClockPhiCombinedScalePressure SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiNativeJointPayment SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentElectricSuccessor
open FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentAdmissibleElectric FirstCurrentGeometricPayer
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarPositiveBulkWard
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceDilationKinetic
open SourceGaugeRadius SourceGaugeRadiusMetric SourceGaugeRadialCurrent SourcePhysicalKineticSquare
open SourceGaugeRadialPair SourceCornerWeight SourceDilationAlgebra GaussCoframeForm
open SourceClockPhiMatchedElectricSource SourceClockPhiNativeMatchedSource
open scoped ContDiff InnerProductSpace
open ClockPhiHeatCorrectedCovarianceSource ReverseNativeClock ReverseNativeFrequencyWard
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev Z:End:=reverseNativeClock
private abbrev X:End:=weightedElectricCurrent
private abbrev D:End:=combinedGenerator
private abbrev Dc:End:=dilation
private abbrev Phi:End:=SourceScalarAffineScaleTransport.generator
private abbrev Ggen:End:=SourceGaugeScaleTransport.generator
private abbrev E:End:=electricAction
private abbrev V:End:=volumeAction
private abbrev W:End:=magneticVolumeWeight
private abbrev H0:End:=diagonalAction
private abbrev CE:End:=fullElectricCurrent
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed reverseNativeClock correctedCompleteCore weightedElectricCurrent
  coreEquiv normalizedState normalizedForcing wholeClockState wholeSourceNext phiThetaAction phiInverseAction
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hg:=actual_source_noether_gap half
  linarith
private abbrev Hz(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced (sourceNoetherFrequency half) (frequency_positive half) q
private theorem normalized_two_seed(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    normalizedState m ell F z hz g=
      ∑i:Fin 2,phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (inputSeed g i))):=by
  simp only [Fin.sum_univ_two]
  have hr:coreEquiv.symm (phiRadiusSource g)=phiRadiusAction (coreEquiv.symm g):=by
    unfold phiRadiusSource
    exact coreEquiv.symm_apply_apply _
  unfold normalizedState
  change phiThetaAction m ell (resolventCore F z hz (coreEquiv.symm g))-
    phiInverseAction (phiThetaAction m ell (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g))))=
    phiThetaAction m ell (resolventCore F z hz (coreEquiv.symm g))+
    (-(phiInverseAction*phiThetaAction m ell)) (resolventCore F z hz (coreEquiv.symm (phiRadiusSource g)))
  simp only [hr,LinearMap.neg_apply,Module.End.mul_apply,sub_eq_add_neg]
private theorem bracket_product(A B C:End):bracket A (B*C)=bracket A B*C+B*bracket A C:=by
  unfold bracket
  noncomm_ring
private theorem electric_smooth_local(z:physicalChart):ContDiffAt ℝ ∞ electricWeight z.val:=
  (reciprocal_volume_smooth z).mul (SourceGaugeRadialCurrent.electric_square_smooth z)
private theorem electric_formula(z:SourceCoordinateSlice):electricWeight z=
    n/(sourceSigma*(volume z)^2)*gaugeSquare z:=by
  unfold electricWeight SourceGaugeRadiusMetric.electricSquare reciprocalVolume
  ring
private theorem real_multiply(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest):
    (multiply c hc f:SourceCoordinateSlice→FockFiber)=(fun z=>c z • f z):=by
  funext z;apply PiLp.ext;intro word
  exact Complex.real_smul.symm
private theorem real_commute(c d:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)
private theorem connection_coframe_scale(r:ℝ)(z:SourceCoordinateSlice)(i:Fin 3):
    connectionField (SourceCoframeVolume.scale r z) i=connectionField z i:=by
  unfold connectionField SourceCoframeVolume.scale
  rfl
private theorem electric_coframe_scale(r:ℝ)(hr:r≠0)(z:physicalChart):
    electricWeight (SourceCoframeVolume.scale r z.val)=r^(-4:ℤ)*electricWeight z.val := by
  have hrow(i:Fin 3):gaugeRow (SourceCoframeVolume.scale r z.val) i=r • gaugeRow z.val i:=by
    simp only [gaugeRow,connection_coframe_scale]
    fin_cases i <;> simp [SourceCoframeVolume.scale,smul_smul,smul_add]
  have hT:gaugeSquare (SourceCoframeVolume.scale r z.val)=r^2*gaugeSquare z.val:=by
    simp only [gaugeSquare,hrow,real_inner_smul_left,real_inner_smul_right,pow_two,
      Finset.mul_sum,mul_assoc]
  rw [electric_formula,volume_scale,hT,electric_formula]
  simp only [zpow_neg]
  field_simp [hr,(volume_pos z).ne',source_sigma_nonzero]
private theorem electric_dilation:bracket Dc electricAction=(8*Complex.I/3) • electricAction := by
  have hd(z:physicalChart):fderiv ℝ electricWeight z.val (euler z.val)=(-4:ℝ)*electricWeight z.val:=by
    simpa only [Int.cast_neg,Int.cast_ofNat] using SourceKineticScale.euler_of_scale electricWeight (-4) z (electric_smooth_local z) (fun r hr=>electric_coframe_scale r hr z)
  have h:=SourceDilationMultiplier.homogeneous_multiplier electricWeight electric_smooth_local (-4) hd
  change bracket Dc electricAction=((-2*Complex.I/3)*((-4:ℝ):ℂ)) • electricAction at h
  convert h using 1
  congr 1
  norm_num
  ring
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
private theorem electric_scalar_flow (t : ℝ) (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    SourceScalarAffineScaleTransport.coreFlow t (E f) z word =
      (electricWeight z : ℂ) * SourceScalarAffineScaleTransport.coreFlow t f z word := by
  rw [SourceScalarAffineScaleTransport.coreFlow_apply, SourceScalarAffineScaleTransport.coreFlow_apply]
  change _ * ((electricWeight (SourceScalarAffineScaleTransport.scaleEquiv t z) : ℂ) *
    f (SourceScalarAffineScaleTransport.scaleEquiv t z) word) = _
  rw [electric_scalar_weight]
  ring
private theorem electric_phi_generator : Commute E SourceScalarAffineScaleTransport.generator := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have h1 := SourceScalarAffineScaleTransport.component_flow_derivative (E f) z word 0
  have h2 := (SourceScalarAffineScaleTransport.component_flow_derivative f z word 0).const_mul
    (electricWeight z : ℂ)
  have he : (fun t : ℝ => SourceScalarAffineScaleTransport.coreFlow t (E f) z word) =
      (fun t : ℝ => (electricWeight z : ℂ) * SourceScalarAffineScaleTransport.coreFlow t f z word) :=
    funext (fun t => electric_scalar_flow t f z word)
  rw [he] at h1
  have h := h1.unique h2
  simp only [SourceScalarAffineScaleTransport.coreFlow_zero] at h
  exact h.symm

private theorem bracket_smul_left(c:ℂ)(A B:End):bracket (c • A) B=c • bracket A B:=by
  unfold bracket
  simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_smul_right(c:ℂ)(A B:End):bracket A (c • B)=c • bracket A B:=by
  unfold bracket
  simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_jacobi(A B C:End):
    bracket A (bracket B C)=bracket (bracket A B) C+bracket B (bracket A C):=by
  unfold bracket
  noncomm_ring
/-- The original electric multiplier has weight eighteen under the balanced source scale. -/
theorem actual_reverse_electric_action:bracket Z E=(18:ℂ) • E:=by
  have hp:bracket Phi E=0:=sub_eq_zero.mpr electric_phi_generator.eq.symm
  have hg:=electric_gauge
  have hd:=electric_dilation
  unfold Z reverseNativeClock
  change bracket ((3:ℂ) • (Phi-Ggen)-(9*Complex.I:ℂ) • Dc) E=_
  have hc:=congrArg (fun T:End=>(9*Complex.I:ℂ) • T) hd
  simp only [smul_smul] at hc
  have hi:(9*Complex.I:ℂ)*(8*Complex.I/3)= -24:=by
    calc _=24*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi] at hc
  simp only [bracket] at hp hg hc ⊢
  linear_combination (norm:=(noncomm_ring;module)) (3:ℂ) • hp-(3:ℂ) • hg-hc
private theorem reverse_volume:bracket Z V=(-18:ℂ) • V:=by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator V
  have hg:=SourceGaugeScaleTransport.generator_commutator V
  rw [original_volume_phi] at hp
  rw [original_volume_gauge] at hg
  have hd:=volume_scale_current
  change bracket Dc V=(-2*Complex.I) • V at hd
  unfold Z reverseNativeClock
  change bracket ((3:ℂ) • (Phi-Ggen)-(9*Complex.I:ℂ) • Dc) V=_
  have hc:=congrArg (fun T:End=>(9*Complex.I:ℂ) • T) hd
  simp only [smul_smul] at hc
  have hi:(9*Complex.I:ℂ)*(-2*Complex.I)=18:=by
    calc _= -18*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi] at hc
  simp only [bracket] at hp hg hc ⊢
  linear_combination (norm:=(noncomm_ring;module)) (3:ℂ) • hp-(3:ℂ) • hg-hc
private theorem weight_cube:W=V^3:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change ((volume z^3:ℝ):ℂ)*f z word=(volume z:ℂ)*((volume z:ℂ)*((volume z:ℂ)*f z word))
  push_cast
  ring
private theorem reverse_weight:bracket Z W=(-54:ℂ) • W:=by
  rw [weight_cube]
  change bracket Z ((V*V)*V)=(-54:ℂ) • ((V*V)*V)
  rw [bracket_product,bracket_product,reverse_volume]
  simp only [smul_mul_assoc,mul_smul_comm,add_mul]
  module
private theorem reverse_electric_current:
    bracket Z CE=(36:ℂ) • CE+(1/2:ℂ) • bracket reverseScaleForce E:=by
  unfold CE fullElectricCurrent
  rw [bracket_smul_right,bracket_jacobi,actual_reverse_full_hamiltonian_scale,actual_reverse_electric_action]
  have hadd(A B C:End):bracket (A+B) C=bracket A C+bracket B C:=by unfold bracket;noncomm_ring
  rw [hadd,bracket_smul_left,bracket_smul_right]
  simp only [smul_add,smul_smul]
  module
/-- The full-H0 electric outer word has its generated scale term and the original force-electric current; no auxiliary Hamiltonian is substituted. -/
theorem actual_reverse_weighted_electric_source:
    bracket Z X=(-18:ℂ) • X+(1/4:ℂ) •
      (W*bracket reverseScaleForce E+bracket reverseScaleForce E*W):=by
  unfold X weightedElectricCurrent
  have hadd(A B C:End):bracket A (B+C)=bracket A B+bracket A C:=by unfold bracket;noncomm_ring
  rw [bracket_smul_right,hadd,bracket_product,bracket_product,reverse_weight,reverse_electric_current]
  simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add,smul_add,smul_smul]
  module
private abbrev U:End:=inverseVolumeAction
private abbrev VP:End:=multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
private abbrev Hc:End:=GaussCoframeForm.coframeAction-VP
private theorem combined_delta(T:End):bracket D T=deltaPhi T-deltaGauge T:=by
  unfold D combinedGenerator bracket
  have hp:=SourceScalarAffineScaleTransport.generator_commutator T
  have hg:=SourceGaugeScaleTransport.generator_commutator T
  linear_combination (norm:=noncomm_ring) hp-hg
private theorem reverse_coframe:bracket Z Hc=(18:ℂ) • Hc:=by
  have hc:bracket D GaussCoframeForm.coframeAction=0:=by
    rw [combined_delta,original_coframe_phi,original_coframe_gauge,sub_self]
  have hv:bracket D VP=0:=by
    rw [combined_delta]
    have h:=original_coframe_local_phi_gauge VP
      (fun q=>(GaussCoframeForm.volumePotential (q,(0:Slice)):ℂ) • ContinuousLinearMap.id ℂ FockFiber)
      (fun _ _=>rfl)
    rw [h.1,h.2,sub_self]
  have hb:bracket D Hc=0:=by
    unfold Hc bracket at *
    linear_combination (norm:=noncomm_ring) hc-hv
  have hd:bracket Dc Hc=(2*Complex.I:ℂ) • Hc:=by
    have hH:Hc=GaussCoframeKinetic.kinetic+currentAction+(∑a:Fin 7,spinSquare a)+numberShift:=by
      unfold Hc GaussCoframeForm.coframeAction VP
      abel
    rw [hH]
    exact homogeneous_add _ _ _ _ (homogeneous_add _ _ _ _
      (homogeneous_add _ _ _ _ coframe_kinetic_current coframe_current_current)
      (homogeneous_sum _ _ _ spin_square_current)) number_shift_current
  have hsd:=congrArg (fun T:End=>(9*Complex.I:ℂ) • T) hd
  simp only [smul_smul] at hsd
  have hi:(9*Complex.I:ℂ)*(2*Complex.I)= -18:=by
    calc _=18*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi] at hsd
  unfold Z reverseNativeClock
  change bracket ((3:ℂ) • D-(9*Complex.I:ℂ) • Dc) Hc=_
  unfold bracket at hb hsd ⊢
  linear_combination (norm:=(noncomm_ring;module)) (3:ℂ) • hb-hsd
private theorem reverse_coframe_current:
    bracket Z coframeElectricCurrent=(36:ℂ) • coframeElectricCurrent:=by
  have hE:bracket VP E=0:=sub_eq_zero.mpr (real_commute _ _ _ _).eq
  have he:coframeElectricCurrent=(1/2:ℂ) • bracket Hc E:=by
    unfold coframeElectricCurrent Hc bracket at *
    linear_combination (norm:=(noncomm_ring;module)) (1/2:ℂ) • hE
  rw [he,bracket_smul_right,bracket_jacobi,reverse_coframe,actual_reverse_electric_action,
    bracket_smul_left,bracket_smul_right]
  module
private theorem reverse_gauge:bracket Z Ggen=0:=by
  have hp:=SourceScalarAffineMixedJets.generators_affine_gauge.eq
  have hd:=SourceGaugeScaleTransport.generator_commutator Dc
  rw [original_dilation_gauge] at hd
  unfold Z reverseNativeClock
  change bracket ((3:ℂ) • (Phi-Ggen)-(9*Complex.I:ℂ) • Dc) Ggen=_
  unfold bracket
  linear_combination (norm:=(noncomm_ring;module)) (3:ℂ) • hp+(9*Complex.I:ℂ) • hd
private theorem UV:U*V=(1:End):=(real_commute _ _ _ _).eq.trans (LinearMap.ext volume_inverse)
private theorem VU:V*U=(1:End):=LinearMap.ext volume_inverse
private theorem reverse_inverse:bracket Z U=(18:ℂ) • U:=by
  have hv:=reverse_volume
  unfold bracket at hv ⊢
  have h:U*(Z*V-V*Z)*U=(-18:ℂ) • U:=by
    rw [hv]
    simp only [mul_smul_comm,smul_mul_assoc,mul_assoc,VU,mul_one]
  have hh:U*(Z*V-V*Z)*U=U*Z-Z*U:=by
    noncomm_ring
    simp only [VU,mul_one,←mul_assoc,UV,one_mul]
  rw [hh] at h
  linear_combination (norm:=(noncomm_ring;module)) -h
/-- All non-gauge departments of the literal scale-force cancel against the original electric multiplier. -/
theorem actual_reverse_force_electric(F:Index)(g:diagonal.domain):
    bracket reverseScaleForce E=(36:ℂ) • (U*Ggen):=by
  have he:CE=coframeElectricCurrent-U*Ggen:=(actual_matched_electric_source 0 0 F Complex.I (by simp) g).1
  have hu:bracket Z (U*Ggen)=(18:ℂ) • (U*Ggen):=by
    rw [bracket_product,reverse_inverse,reverse_gauge]
    simp only [smul_mul_assoc,mul_zero,add_zero]
  have hc:=reverse_coframe_current
  have hr:bracket Z CE=(36:ℂ) • CE+(18:ℂ) • (U*Ggen):=by
    rw [he]
    unfold bracket at hu hc ⊢
    linear_combination (norm:=(noncomm_ring;module)) hc-hu
  linear_combination (norm:=module) (2:ℂ) • hr-(2:ℂ) • reverse_electric_current
private theorem gauge_weight:Commute Ggen W:=by
  have h:=original_coframe_local_phi_gauge W
    (fun q=>((volume (q,(0:Slice))^3:ℝ):ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun _ _=>rfl)
  have hg:=SourceGaugeScaleTransport.generator_commutator W
  rw [h.2] at hg
  exact sub_eq_zero.mp hg
private theorem end_assoc(A B C:End):(A*B)*C=A*(B*C):=rfl
private theorem weight_inverse:W*U=V^2:=by
  rw [weight_cube,pow_succ]
  rw [end_assoc,VU,mul_one]
private theorem inverse_weight:U*W=V^2:=by
  rw [weight_cube,pow_succ']
  rw [←end_assoc,UV,one_mul]
/-- The actual weighted electric outer update reduces to its own step and the original volume-squared gauge generator. -/
theorem actual_reverse_electric_outer_return(F:Index)(g:diagonal.domain):
    bracket Z X=(-18:ℂ) • X+(18:ℂ) • (V^2*Ggen):=by
  rw [actual_reverse_weighted_electric_source,actual_reverse_force_electric F g]
  have h1:W*(U*Ggen)=V^2*Ggen:=by rw [←end_assoc,weight_inverse]
  have h2:(U*Ggen)*W=V^2*Ggen:=by rw [end_assoc,gauge_weight.eq,←end_assoc,inverse_weight]
  simp only [mul_smul_comm,smul_mul_assoc,h1,h2,smul_add,smul_smul]
  module
private theorem whole_map_bracket(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    bracket Z (wholeSourceMap s hs half advanced m ell F g)=
      (wholeStep s hs half advanced m ell F g:ℂ) • bracket Z X:=by
  unfold wholeSourceMap bracket
  simp only [mul_add,add_mul,mul_one,one_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
  module

/-- The scale-force and both compression commutators stay on their original two resolvent legs. -/
def reverseForceInput(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  ∑i:Fin 2,phaseRow m ell i (resolventCore F z hz
    (reverseCompressionForce F (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))))

/-- Removing the separately paid clock part leaves the actual selected electric word and full original compression force. -/
def wholeOuterSource(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):QuantumTest:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  (wholeStep s hs half advanced m ell F g:ℂ) • bracket Z X (frequencyState half advanced m ell F g q)+
    wholeSourceMap s hs half advanced m ell F g
      (reverseInputVector m ell F z (Hz half advanced q) g-reverseForceInput m ell F z (Hz half advanced q) g)

attribute [local irreducible] reverseInputVector reverseForceInput wholeSourceMap wholeClockWord resolventCore phaseRow inputSeed wholeStep reverseCompressionForce reverseScaleForce diagonalAction

private theorem two_seed_outer_split(K L R T:End)(A:Fin 2→End)(f:Fin 2→QuantumTest):
    (∑i:Fin 2,(bracket Z (K*L*A i) (R (f i))+(K*L*A i) (R (Z (f i)))-
      (K*L*A i) (R (T (R (f i))))))=
    bracket Z K (L (∑i:Fin 2,A i (R (f i))))+
      K (bracket Z L (∑i:Fin 2,A i (R (f i)))+
        L ((∑i:Fin 2,(bracket Z (A i) (R (f i))+A i (R (Z (f i)))))-
          ∑i:Fin 2,A i (R (T (R (f i)))))):=by
  simp only [bracket_product,Module.End.mul_apply,LinearMap.add_apply,map_sum,map_add,map_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  module

private theorem balanced_response_split(K L:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    (∑i:Fin 2,(bracket Z (K*L*phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
      (K*L*phaseRow m ell i) (resolventCore F z hz (Z (coreEquiv.symm (inputSeed g i))))-
      (K*L*phaseRow m ell i) (resolventCore F z hz
        (reverseCompressionForce F (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))))))=
    bracket Z K (L (normalizedState m ell F z hz g))+
      K (bracket Z L (normalizedState m ell F z hz g)+L
        (reverseInputVector m ell F z hz g-reverseForceInput m ell F z hz g)):=by
  have hp:=two_seed_outer_split K L (resolventCore F z hz) (reverseCompressionForce F)
    (phaseRow m ell) (fun i=>coreEquiv.symm (inputSeed g i))
  have ha:=actual_reverse_input_vector m ell F z hz g
  have hw:=normalized_two_seed m ell F z hz g
  simp only [ha,←hw] at hp
  unfold reverseForceInput
  exact hp

private theorem whole_source_sum(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeReverseSource s hs half advanced m ell F g x q=
      ∑i:Fin 2,(bracket Z (wholeClockWord s hs half advanced m ell F g x i)
        (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q)
          (coreEquiv.symm (inputSeed g i)))+
        wholeClockWord s hs half advanced m ell F g x i
          (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q)
            (Z (coreEquiv.symm (inputSeed g i))))-
        wholeClockWord s hs half advanced m ell F g x i
          (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q)
            (reverseCompressionForce F (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q)
              (Hz half advanced q) (coreEquiv.symm (inputSeed g i)))))):=rfl
private theorem whole_outer_apply(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    wholeOuterSource s hs half advanced m ell F g q=
      (wholeStep s hs half advanced m ell F g:ℂ) • bracket Z X
        (normalizedState m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q) g)+
      wholeSourceMap s hs half advanced m ell F g
        (reverseInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q) g-
          reverseForceInput m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q) g):=rfl

/-- Exact full source split: no step is differentiated, and the input correction and delta_Z remain inside the same whole-source map. -/
theorem actual_whole_reverse_source_split(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeReverseSource s hs half advanced m ell F g x q=
      bracket Z (correctedCompleteCore s hs x.1 x.2) ((wholeSourceNext s hs half advanced m ell F g q).1)+
      correctedCompleteCore s hs x.1 x.2 (wholeOuterSource s hs half advanced m ell F g q):=by
  have hm:(wholeSourceNext s hs half advanced m ell F g q).1=
      wholeSourceMap s hs half advanced m ell F g (frequencyState half advanced m ell F g q):=by
    unfold wholeSourceNext wholeSourceMap
    simp only [electricSourceDirection,Prod.fst_add,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply]
    rfl
  have hp:=balanced_response_split (correctedCompleteCore s hs x.1 x.2)
    (wholeSourceMap s hs half advanced m ell F g) m ell F
    (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q) g
  have hb:=whole_map_bracket s hs half advanced m ell F g
  simp only [hb,LinearMap.smul_apply] at hp
  rw [hm,whole_outer_apply s hs half advanced m ell F g q,whole_source_sum s hs half advanced m ell F g x q]
  simp only [wholeClockWord,frequencyState]
  exact hp

/-- The clock commutator is its genuine three-row return, with the original volume shift and both source noises. -/
theorem actual_whole_reverse_three_row_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeReverseSource s hs half advanced m ell F g x q=
      correctedCompleteCore s hs x.1 x.2
        (reverseClockReturn s hs x.1 x.2 ((wholeSourceNext s hs half advanced m ell F g q).1)+
          wholeOuterSource s hs half advanced m ell F g q):=by
  rw [actual_whole_reverse_source_split,actual_complete_reverse_clock_return]
  rw [map_add]
  rfl

open ScalarCausalFrequencyMoment SourceScalarShiftedBulk SourceScalarEssentialBudget MeasureTheory Filter
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1

theorem actual_whole_outer_source_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    wholeOuterSource s hs half advanced m ell F g q=
      (-18*(wholeStep s hs half advanced m ell F g:ℂ)) • X (frequencyState half advanced m ell F g q)+
      (18*(wholeStep s hs half advanced m ell F g:ℂ)) • (V^2*Ggen) (frequencyState half advanced m ell F g q)+
      wholeSourceMap s hs half advanced m ell F g
        (reverseInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q) g-
          reverseForceInput m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q) g):=by
  unfold wholeOuterSource
  rw [actual_reverse_electric_outer_return F g]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_add,smul_smul]
  module

def wholeOuterNoetherPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  18*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)-
    2*(sourcePair (correctedCompleteCore s hs x.1 x.2 (wholeOuterSource s hs half advanced m ell F g q))
      (scalarBulkComplete (wholeClockState s hs half advanced m ell F g x q))).re
private theorem pair_add_left(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by
  simp only [sourcePair,map_add,inner_add_left]
private theorem causal_outer_gap(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeNoetherCausalPrice s hs half advanced m ell F g x q-wholeOuterNoetherPrice s hs half advanced m ell F g x q=
      -2*(wholeClockWardKernel s hs half advanced m ell F g q x).re:=by
  unfold wholeNoetherCausalPrice wholeOuterNoetherPrice
  rw [actual_whole_reverse_source_split]
  simp only [pair_add_left,Complex.add_re]
  have hc:sourcePair (bracket Z (correctedCompleteCore s hs x.1 x.2)
      ((wholeSourceNext s hs half advanced m ell F g q).1))
      (scalarBulkComplete (wholeClockState s hs half advanced m ell F g x q))=
      wholeClockWardKernel s hs half advanced m ell F g q x:=by
    unfold wholeClockWardKernel wholeClockState
    rfl
  rw [hc]
  ring

/-- The actual causal upper price differs from the fully expanded outer-source price by a common vanishing frequency/Gaussian source quantity. The source supplies delta before both causes; no energy or Hamiltonian budget is assumed. -/
theorem actual_whole_outer_noether_common_payment(ε:ℝ)(hε:0<ε)(half:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    ∃δ:ℝ,0<δ ∧ δ ≤ 1 ∧ ∀advanced:Bool,∀s:ℝ,∀hs:0<s,s ≤ δ→
      Integrable (fun p:ℝ×(ℝ×ℝ)=>wholeNoetherCausalPrice s hs half advanced m ell F g p.2 p.1-
        wholeOuterNoetherPrice s hs half advanced m ell F g p.2 p.1) (MeasureTheory.volume.prod (γ.prod γ)) ∧
      ‖∫x:ℝ×ℝ,(∫q:ℝ,wholeNoetherCausalPrice s hs half advanced m ell F g x q-
        wholeOuterNoetherPrice s hs half advanced m ell F g x q) ∂γ.prod γ‖ ≤ ε:=by
  obtain ⟨δ,hδ,hδ1,hpay⟩:=actual_whole_reverse_clock_frequency_payment (ε/2) (by positivity) half m ell F g
  refine ⟨δ,hδ,hδ1,?_⟩
  intro advanced s hs hsδ
  obtain ⟨hi,hb⟩:=hpay advanced s hs hsδ
  have hr:Integrable (fun p:ℝ×(ℝ×ℝ)=>(-2:ℝ)*(wholeClockWardKernel s hs half advanced m ell F g p.1 p.2).re)
      (MeasureTheory.volume.prod (γ.prod γ)):=by
    simpa only [RCLike.re_eq_complex_re] using hi.re.const_mul (-2:ℝ)
  constructor
  · apply hr.congr
    exact Eventually.of_forall (fun p=>(causal_outer_gap s hs half advanced m ell F g p.2 p.1).symm)
  · simp_rw [causal_outer_gap]
    have he:(∫x:ℝ×ℝ,(∫q:ℝ,(-2:ℝ)*(wholeClockWardKernel s hs half advanced m ell F g q x).re) ∂γ.prod γ)=
        (-2:ℝ)*(∫x:ℝ×ℝ,(∫q:ℝ,wholeClockWardKernel s hs half advanced m ell F g q x) ∂γ.prod γ).re:=by
      rw [←integral_prod_symm _ hr,integral_const_mul]
      have hreal:=integral_re hi
      simp only [RCLike.re_eq_complex_re] at hreal
      rw [hreal,integral_prod_symm _ hi]
    rw [he,norm_mul]
    norm_num only [norm_neg,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num:0 ≤ (2:ℝ))).trans (by linarith)

/-- The original finite Noether work consumes the causal sign and the exact outer-source decomposition at every noise point. The separately generated joint small price pays its remaining clock term. -/
theorem actual_whole_outer_noether_work(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(h:ℝ)(hh:0<h):
    let W:=fun q:ℝ=>let z:=actualFrequency advanced (sourceNoetherFrequency half) q
      let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
      reverseScalarNoetherWork h z a.1 a.2
    Integrable W ∧ Integrable (fun q:ℝ=>wholeOuterNoetherPrice s hs half advanced m ell F g x q-
      2*(wholeClockWardKernel s hs half advanced m ell F g q x).re) ∧
      (∫q:ℝ,W q) ≤ ∫q:ℝ,wholeOuterNoetherPrice s hs half advanced m ell F g x q-
        2*(wholeClockWardKernel s hs half advanced m ell F g q x).re:=by
  have he:(fun q:ℝ=>wholeNoetherCausalPrice s hs half advanced m ell F g x q)=
      fun q:ℝ=>wholeOuterNoetherPrice s hs half advanced m ell F g x q-
        2*(wholeClockWardKernel s hs half advanced m ell F g q x).re:=by
    funext q
    linarith [causal_outer_gap s hs half advanced m ell F g x q]
  have hp:=actual_whole_noether_causal_price s hs half advanced m ell F g x h hh
  dsimp only at hp ⊢
  refine ⟨hp.1,hp.2.1.congr (Eventually.of_forall (fun q=>congrFun he q)),?_⟩
  simpa only [he] using hp.2.2
end LowEnergy.ReverseNativeOuterSource
