import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeRSourceReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1600000
noncomputable section
namespace LowEnergy.FirstCurrentPrimitiveNoether
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolumeCurrent SourceCoframeDilation SourceScalarDoubleCurrent SourceClockAcceleration
open SourceClockPhiRadiusAcceleration SourceClockPhiRadiusSourceCurrent SourceClockPhiMatchedElectricSource
open SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource SourceClockPhiCombinedScalePressure
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentJointBudget FirstCurrentJointBudgetNext FirstCurrentGeometricPayer FirstCurrentElectricSuccessor
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier JointElectricSource
open ClockPhiHeatCorrectedCovarianceSource
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev U:End:=inverseVolumeAction
private abbrev P:End:=electricPrimitive
private abbrev E:End:=electricAction
private abbrev CE:End:=fullElectricCurrent
private abbrev Ccf:End:=coframeElectricCurrent
private abbrev X:End:=weightedElectricCurrent
private abbrev W:End:=magneticVolumeWeight
private abbrev M:End:=matchedTester
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] diagonalAction sourcePair embed
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only[sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only[sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem U_pair(f g:QuantumTest):sourcePair f (U g)=sourcePair (U f) g:=multiply_pair _ _ _ _
private theorem E_pair(f g:QuantumTest):sourcePair f (E g)=sourcePair (E f) g:=multiply_pair _ _ _ _
private theorem clock_pair(f g:QuantumTest):sourcePair f (clock g)=sourcePair (clock f) g:=by
  rw [original_clock]
  exact multiply_pair _ _ _ _
private theorem phi_pair(f g:QuantumTest):sourcePair f (phiSquare g)=sourcePair (phiSquare f) g:=by
  change sourcePair f (phiRadiusAction (phiRadiusAction g))=sourcePair (phiRadiusAction (phiRadiusAction f)) g
  have hr(a b:QuantumTest):sourcePair a (phiRadiusAction b)=sourcePair (phiRadiusAction a) b:=multiply_pair _ _ _ _
  rw [hr,hr]

/-- These are literally the same primitive: the Lyapunov form retains its electric term when expanded. -/
theorem actual_primitive_source_identity:
    P=(2/(n:ℂ)) • phiSquare+(5/2:ℂ) • E-(2:ℂ) • electricLyapunov ∧
    P=(2/(n:ℂ)) • phiSquare+(1/2:ℂ) • E-(4/(n:ℂ)) • clock:=by
  refine ⟨actual_electric_primitive_normal_form,?_⟩
  change (2/(n:ℂ)) • phiSquare-(4/(n:ℂ)) • clock+(1/2:ℂ) • E=_
  module
private theorem P_pair(f g:QuantumTest):sourcePair f (P g)=sourcePair (P f) g:=by
  rw [actual_primitive_source_identity.2]
  simp only[LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,pair_add_l,pair_add_r,
    pair_sub_l,pair_sub_r,pair_smul_l,pair_smul_r,phi_pair,E_pair,clock_pair,
    Complex.star_def,map_div₀,map_ofNat,map_one,Complex.conj_ofReal]
private theorem self_im(T:End)(hT:∀f g,sourcePair f (T g)=sourcePair (T f) g)(w:QuantumTest):
    (sourcePair w (T w)).im=0:=by
  have h:=congrArg Complex.im (GaussNativeForm.pair_conjugate w (T w))
  rw [hT w w] at h
  simp only[Complex.conj_im] at h
  rw [hT w w]
  linarith only[h]
private theorem inverse_dilation:dilation*U-U*dilation=(2*Complex.I) • U:=by
  have h:=congrArg (fun A:End=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (dilation*U-U*dilation))=
    (-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only[smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=1:=by
    calc _= -(Complex.I*Complex.I):=by ring
         _= _:=by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1; congr 1; ring

/-- The complete matched current is recovered from the same full-H0 primitive, including its coframe-electric and U remainder. -/
theorem actual_full_primitive_matched_current(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    bracket H0 P=M+Ccf+U:=by
  have he:CE=Ccf-U*SourceGaugeScaleTransport.generator:=(actual_matched_electric_source m ell F z hz g).1
  have hphi:bracket H0 phiSquare=(n/2:ℂ) • (U*SourceScalarAffineScaleTransport.generator):=original_phi_square_current
  have hclock:bracket H0 clock=(-Complex.I) • clockCurrent:=by
    unfold clockCurrent bracket
    simp only[smul_smul]
    rw [show (-Complex.I)*Complex.I=1 by rw [neg_mul,Complex.I_mul_I];ring,one_smul]
  have hp:bracket H0 P=(2/(n:ℂ)) • bracket H0 phiSquare+
      (1/2:ℂ) • bracket H0 E-(4/(n:ℂ)) • bracket H0 clock:=by
    rw [actual_primitive_source_identity.2]
    unfold bracket
    simp only[mul_add,mul_sub,add_mul,sub_mul,mul_smul_comm,smul_mul_assoc]
    module
  rw [hp,hphi,hclock,original_clock_current]
  change (2/(n:ℂ)) • ((n/2:ℂ) • (U*SourceScalarAffineScaleTransport.generator))+CE-
    (4/(n:ℂ)) • ((-Complex.I) • ((3*(n:ℂ)/8) • (U*dilation+dilation*U)))=_
  rw [he]
  have hU:U*dilation=dilation*U-(2*Complex.I) • U:=by linear_combination (norm:=module) -inverse_dilation
  rw [hU]
  simp only[smul_smul,smul_add,smul_sub]
  have hn:(n:ℂ)≠0:=Complex.ofReal_ne_zero.mpr n_pos.ne'
  have h1:(2/(n:ℂ))*(n/2:ℂ)=1:=by field_simp[hn]
  have h2:(4/(n:ℂ))*((-Complex.I)*(3*(n:ℂ)/8))= -3*Complex.I/2:=by field_simp[hn];ring
  rw [h1,h2,one_smul]
  have hM:M=U*(SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)+
      (3*Complex.I) • (dilation*U)+(2:ℂ) • U:=rfl
  rw [hM]
  simp only[mul_sub]
  have hi:(4/(n:ℂ))*((-Complex.I)*(3*(n:ℂ)/8*(2*Complex.I)))=3:=by
    calc _= -3*(Complex.I*Complex.I):=by field_simp[hn];ring
         _= _:=by rw [Complex.I_mul_I];ring
  rw [hi]
  module

def primitiveNoether(w f:QuantumTest):ℝ:=
  (sourcePair f (P w)).im-(sourcePair w (bracket H0 P w)).im/2
private theorem primitive_ward(w f:QuantumTest)(z:ℂ)(he:H0 w=f+z • w):
    primitiveNoether w f=z.im*(sourcePair w (P w)).re:=by
  have hp:sourcePair w (bracket H0 P w)=sourcePair (H0 w) (P w)-sourcePair (P w) (H0 w):=by
    simp only[bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r,diagonalAction_pair,P_pair]
  rw [he,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r] at hp
  have hc:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (P w))
  have hs:sourcePair (P w) w=sourcePair w (P w):=(P_pair w w).symm
  rw [hs] at hp
  have hself:=self_im P P_pair w
  have h:=congrArg Complex.im hp
  simp only[Complex.sub_im,Complex.add_im,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,hself,
    mul_zero,zero_add] at h hc
  unfold primitiveNoether
  linarith only[h,hc]
private theorem source_direction(w f:QuantumTest)(z:ℂ)(he:H0 w=f+z • w):
    H0 (X w)=(X f+bracket H0 X w)+z • X w:=by
  simp only[bracket,LinearMap.sub_apply,Module.End.mul_apply]
  rw [he,map_add,map_smul]
  module

def primitiveNoetherSlope(w f:QuantumTest):ℝ:=
  (sourcePair (X f+bracket H0 X w) (P w)).im+(sourcePair f (P (X w))).im-
    ((sourcePair (X w) (bracket H0 P w)).im+(sourcePair w (bracket H0 P (X w))).im)/2
private theorem slope_return(F:Index)(g:diagonal.domain)(w f:QuantumTest)(z:ℂ)(he:H0 w=f+z • w):
    primitiveNoetherSlope w f=z.im*(5*(sourcePair w ((W*U*E) w)).re+
      (1/4:ℝ)*(sourcePair w ((W*wedgeAction) w)).re):=by
  let fX:=X f+bracket H0 X w
  have hX:=source_direction w f z he
  have hp:H0 (w+X w)=(f+fX)+z • (w+X w):=by rw [map_add,he,hX,smul_add];module
  have hm:H0 (w-X w)=(f-fX)+z • (w-X w):=by rw [map_sub,he,hX,smul_sub];module
  have hplus:=primitive_ward (w+X w) (f+fX) z hp
  have hminus:=primitive_ward (w-X w) (f-fX) z hm
  have hmid:=(actual_weighted_electric_midpoint F g 1 w).2
  norm_num only[weightedElectricEndpoint,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    Bool.false_eq_true,ite_true,ite_false,Complex.ofReal_one,neg_one_smul,one_smul,←sub_eq_add_neg] at hmid
  change (sourcePair (w-X w) (P (w-X w))).re-(sourcePair (w+X w) (P (w+X w))).re=
    -10*(sourcePair w ((W*U*E) w)).re-(1/2:ℝ)*(sourcePair w ((W*wedgeAction) w)).re at hmid
  have hdiff:primitiveNoether (w+X w) (f+fX)-primitiveNoether (w-X w) (f-fX)=
      2*primitiveNoetherSlope w f:=by
    simp only[primitiveNoether,primitiveNoetherSlope,map_add,map_sub,pair_add_l,pair_add_r,pair_sub_l,pair_sub_r,
      Complex.add_im,Complex.sub_im]
    dsimp only[fX]
    simp only[pair_add_l,Complex.add_im]
    ring
  rw [hplus,hminus] at hdiff
  nlinarith only[hdiff,congrArg (fun t:ℝ=>z.im*t) hmid]
private theorem B_pair(f g:QuantumTest):sourcePair (driftClock f) g= -sourcePair f (driftClock g):=by
  have h:=SourceClockPhiComparisonNativeClosedGraph.actual_B3_formal_pair (coreEquiv f) (coreEquiv g)
  change inner ℂ (embed (driftClock (coreEquiv.symm (coreEquiv f)))) (embed g)=
    inner ℂ (embed f) (embed ((-driftClock) (coreEquiv.symm (coreEquiv g)))) at h
  rw [coreEquiv.symm_apply_apply,coreEquiv.symm_apply_apply] at h
  simpa only[sourcePair,LinearMap.neg_apply,map_neg,inner_neg_right] using h
private theorem M_real(w:QuantumTest):(sourcePair (M w) w).re= -(sourcePair w (U w)).re:=by
  have hb:=congrArg Complex.re (B_pair w w)
  have hc:=congrArg Complex.re (GaussNativeForm.pair_conjugate w (driftClock w))
  simp only[Complex.neg_re,Complex.conj_re] at hb hc
  have hz:(sourcePair (driftClock w) w).re=0:=by linarith only[hb,hc]
  have hm:M=driftClock-U:=by unfold M driftClock matchedTester;module
  rw [hm,LinearMap.sub_apply,pair_sub_l,Complex.sub_re,hz,←U_pair]
  ring
private theorem primitive_form(w:QuantumTest):(sourcePair w (P w)).re=
    (2/n)*‖embed (phiRadiusAction w)‖^2+(1/2:ℝ)*(sourcePair w (E w)).re-
      (4/n)*(sourcePair w (clock w)).re:=by
  have hr(a b:QuantumTest):sourcePair a (phiRadiusAction b)=sourcePair (phiRadiusAction a) b:=multiply_pair _ _ _ _
  have hphi:sourcePair w (phiSquare w)=sourcePair (phiRadiusAction w) (phiRadiusAction w):=hr _ _
  have hself:(sourcePair (phiRadiusAction w) (phiRadiusAction w)).re=‖embed (phiRadiusAction w)‖^2:=by
    simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed (phiRadiusAction w))
  rw [actual_primitive_source_identity.2]
  simp only[LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,pair_add_r,pair_sub_r,pair_smul_r,hphi,
    show (2/(n:ℂ))=((2/n:ℝ):ℂ) by push_cast;rfl,show (4/(n:ℂ))=((4/n:ℝ):ℂ) by push_cast;rfl,
    show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,Complex.add_re,Complex.sub_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hself]

def primitivePhasePrice(z:ℂ)(w f:QuantumTest):ℝ:=
  12*z.im*(sourcePair f (P w)).im-6*z.im*(sourcePair w (Ccf w)).im-
    (24*z.im^2/n)*‖embed (phiRadiusAction w)‖^2-6*z.im^2*(sourcePair w (E w)).re+
    (48*z.im^2/n)*(sourcePair w (clock w)).re-6*z.re*(sourcePair w (U w)).re
private theorem phase_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)
    (w f:QuantumTest)(he:H0 w=f+z • w):
    6*(sourcePair (M w) (z • w)).re=primitivePhasePrice z w f:=by
  have hc:=congrArg (fun T:End=>(sourcePair w (T w)).im) (actual_full_primitive_matched_current m ell F z hz g)
  simp only[LinearMap.add_apply,pair_add_r,Complex.add_im,self_im U U_pair w] at hc
  have hN:=primitive_ward w f z he
  unfold primitiveNoether at hN
  have hp:=congrArg Complex.im (GaussNativeForm.pair_conjugate w (M w))
  simp only[Complex.conj_im] at hp
  have hIm:(sourcePair (M w) w).im= -2*(sourcePair f (P w)).im+
      2*z.im*(sourcePair w (P w)).re+(sourcePair w (Ccf w)).im:=by linarith only[hc,hN,hp]
  rw [pair_smul_r,Complex.mul_re,M_real,hIm,primitive_form]
  unfold primitivePhasePrice
  ring

def magneticNoetherPrice(z:ℂ)(w f:QuantumTest):ℝ:=
  (4*magneticPrimitiveFactor/z.im)*primitiveNoetherSlope w f-
    20*magneticPrimitiveFactor*(sourcePair w ((W*U*E) w)).re
private theorem magnetic_payment(F:Index)(g:diagonal.domain)(z:ℂ)(hz:z.im≠0)
    (w f:QuantumTest)(he:H0 w=f+z • w):
    4*(sourcePair w (U (SourceScalarVirialBulk.magneticAction w))).re-(n/48)*‖embed (M w)‖^2≤
      magneticNoetherPrice z w f-(n/48)*‖embed (M w)‖^2:=by
  have hs:=slope_return F g w f z he
  have hp:=actual_magnetic_electric_contact_payment w
  have hr:magneticNoetherPrice z w f=magneticPrimitiveFactor*(sourcePair w ((W*wedgeAction) w)).re:=by
    unfold magneticNoetherPrice
    rw [hs]
    field_simp [hz]
    ring
  rw [hr]
  linarith only[hp]
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  linarith[n_pos,actual_source_noether_gap half]
private theorem frequency_nonreal(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
  have hp:=frequency_positive half
  cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hp.ne'

/-- The actual fixed-pole update and its complete clock restriction generate the primitive Ward,
its negative physical-frequency potentials, and the signed magnetic Noether payment. -/
theorem actual_updated_primitive_noether_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
    primitiveNoether a.1 a.2=z.im*(sourcePair a.1 (P a.1)).re ∧
    6*(sourcePair (M a.1) (z • a.1)).re=primitivePhasePrice z a.1 a.2 ∧
    primitiveNoetherSlope a.1 a.2=z.im*(5*(sourcePair a.1 ((W*U*E) a.1)).re+
      (1/4:ℝ)*(sourcePair a.1 ((W*wedgeAction) a.1)).re) ∧
    4*(sourcePair a.1 (U (SourceScalarVirialBulk.magneticAction a.1))).re-(n/48)*‖embed (M a.1)‖^2≤
      magneticNoetherPrice z a.1 a.2-(n/48)*‖embed (M a.1)‖^2:=by
  dsimp only
  have h:=((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x
  exact ⟨primitive_ward _ _ _ h,phase_return m ell F _ (frequency_nonreal half advanced q) g _ _ h,
    slope_return F g _ _ _ h,magnetic_payment F g _ (frequency_nonreal half advanced q) _ _ h⟩

/-- Any actual complete H0 source can use the same primitive mechanism; the only input is its source equation. -/
theorem actual_full_source_primitive_noether(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)
    (w f:QuantumTest)(he:H0 w=f+z • w):
    primitiveNoether w f=z.im*(sourcePair w (P w)).re ∧
    6*(sourcePair (M w) (z • w)).re=primitivePhasePrice z w f ∧
    primitiveNoetherSlope w f=z.im*(5*(sourcePair w ((W*U*E) w)).re+
      (1/4:ℝ)*(sourcePair w ((W*wedgeAction) w)).re) ∧
    4*(sourcePair w (U (SourceScalarVirialBulk.magneticAction w))).re-(n/48)*‖embed (M w)‖^2≤
      magneticNoetherPrice z w f-(n/48)*‖embed (M w)‖^2:=by
  exact ⟨primitive_ward w f z he,phase_return m ell F z hz g w f he,
    slope_return F g w f z he,magnetic_payment F g z hz w f he⟩
end LowEnergy.FirstCurrentPrimitiveNoether
