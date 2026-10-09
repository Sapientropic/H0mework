import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseFrequencyDerivative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeFrequencyWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceClockYukawaCubicCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceInverseNoetherChannelGap SourceJointResidualEnergy
open SourceClockPhiNormalizedScalarBudget SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeJointPayment
open SourceScalarDoubleCurrent ReverseNativeClock FirstCurrentWholeCarrier FirstCurrentAdmissibleElectric
open FirstCurrentJointBudget FirstCurrentElectricSuccessor FirstCurrentGeometricPayer ClockPhiHeatCorrectedCovarianceSource
open scoped Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev Z:End:=reverseNativeClock
attribute [local irreducible] embed sourcePair diagonalAction compressionCore resolventCore reverseNativeClock reverseScaleForce
  normalizedState normalizedForcing wholeSourceNext wholeSourceMap correctedCompleteCore phiThetaAction phiInverseAction
  SourceClockRadiusResponseAffine.affineRadiusAction coreEquiv
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

/-- The coefficient is the original whole-frequency selected step, fixed before this frequency is varied. -/
def wholeClockWord(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(i:Fin 2):End:=
  correctedCompleteCore s hs x.1 x.2*wholeSourceMap s hs half advanced m ell F g*phaseRow m ell i

def wholeClockState(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).1
private theorem whole_two_seed(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeClockState s hs half advanced m ell F g x q=
      ∑i:Fin 2,wholeClockWord s hs half advanced m ell F g x i
        (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q)
          (coreEquiv.symm (inputSeed g i))):=by
  have hm:(wholeSourceNext s hs half advanced m ell F g q).1=
      wholeSourceMap s hs half advanced m ell F g (frequencyState half advanced m ell F g q):=by
    unfold wholeSourceNext wholeSourceMap
    simp only [electricSourceDirection,Prod.fst_add,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply]
    rfl
  unfold wholeClockState
  simp only [clockSourcePair,hm,frequencyState,normalized_two_seed,map_sum]
  rfl

def wholeFrequencyJet(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  let R:=resolventCore F z (Hz half advanced q)
  ∑i:Fin 2,wholeClockWord s hs half advanced m ell F g x i
    (R (coreEquiv.symm (inputSeed g i))+z • R (R (coreEquiv.symm (inputSeed g i))))

def wholeReverseSource(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  let R:=resolventCore F z (Hz half advanced q)
  ∑i:Fin 2,let L:=wholeClockWord s hs half advanced m ell F g x i
    let f:=coreEquiv.symm (inputSeed g i)
    bracket Z L (R f)+L (R (Z f))-L (R (reverseCompressionForce F (R f)))

/-- The actual whole-source state retains the complete commutators with its clock, selected electric step and two phase rows, together with the full original compression force. -/
theorem actual_whole_reverse_frequency_ward(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    Z (wholeClockState s hs half advanced m ell F g x q)+
      (18:ℂ) • wholeFrequencyJet s hs half advanced m ell F g x q=
      wholeReverseSource s hs half advanced m ell F g x q:=by
  rw [whole_two_seed]
  unfold wholeFrequencyJet wholeReverseSource
  simp only [map_sum,Finset.smul_sum,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _=>actual_reverse_source_word_ward F _ (Hz half advanced q)
    (wholeClockWord s hs half advanced m ell F g x i) (coreEquiv.symm (inputSeed g i)))

theorem actual_whole_physical_frequency_derivative(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    HasDerivAt (fun r:ℝ=>embed (actualFrequency advanced (sourceNoetherFrequency half) r •
      wholeClockState s hs half advanced m ell F g x r))
      (embed (wholeFrequencyJet s hs half advanced m ell F g x q)) q:=by
  have h:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset (Fin 2))) (fun i _=>
    actual_shifted_resolvent_derivative F advanced (sourceNoetherFrequency half) (frequency_positive half)
      (wholeClockWord s hs half advanced m ell F g x i) (coreEquiv.symm (inputSeed g i)) q)
  simpa only [whole_two_seed,wholeFrequencyJet,map_sum,map_smul,Finset.smul_sum] using! h

private abbrev B:End:=SourceScalarShiftedBulk.scalarBulkComplete
open SourceScalarEssentialBudget SourceCoframeDilation SourceCoframeVolumeCurrent SourceClockPhiCombinedScalePressure
attribute [local irreducible] SourceScalarShiftedBulk.scalarBulkComplete scalarEnergy

def wholeResponseDerivative(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  let R:=resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q)
  ∑i:Fin 2,wholeClockWord s hs half advanced m ell F g x i (R (R (coreEquiv.symm (inputSeed g i))))
attribute [local irreducible] wholeClockState wholeClockWord wholeResponseDerivative wholeFrequencyJet wholeReverseSource
private theorem whole_word_derivative(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ)(T:End):
    HasDerivAt (fun r:ℝ=>embed (T (wholeClockState s hs half advanced m ell F g x r)))
      (embed (T (wholeResponseDerivative s hs half advanced m ell F g x q))) q:=by
  have h:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset (Fin 2))) (fun i _=>
    actual_physical_resolvent_derivative F advanced (sourceNoetherFrequency half) (frequency_positive half)
      (T*wholeClockWord s hs half advanced m ell F g x i) (coreEquiv.symm (inputSeed g i)) q)
  simpa only [whole_two_seed,wholeResponseDerivative,map_sum,Module.End.mul_apply] using! h
private theorem whole_jet_split(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeFrequencyJet s hs half advanced m ell F g x q=wholeClockState s hs half advanced m ell F g x q+
      actualFrequency advanced (sourceNoetherFrequency half) q • wholeResponseDerivative s hs half advanced m ell F g x q:=by
  rw [whole_two_seed]
  simp only [wholeFrequencyJet,wholeResponseDerivative,map_add,map_smul,Finset.sum_add_distrib,Finset.smul_sum]

private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
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
private theorem combined_pair(f g:QuantumTest):sourcePair f (combinedGenerator g)= -sourcePair (combinedGenerator f) g:=by
  have hp:=flow_pair_generator SourceScalarAffineScaleTransport.coreFlow SourceScalarAffineScaleTransport.generator
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
  have hg:=flow_pair_generator SourceGaugeScaleTransport.coreFlow SourceGaugeScaleTransport.generator
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
  unfold combinedGenerator
  simp only [LinearMap.sub_apply,sourcePair,map_sub,inner_sub_left,inner_sub_right] at hp hg ⊢
  linear_combination hp-hg
private theorem Z_pair(f g:QuantumTest):sourcePair f (Z g)= -sourcePair (Z f) g:=by
  unfold Z reverseNativeClock
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,starRingEnd_apply]
  have hD:=combined_pair f g
  have hC:=dilation_pair f g
  simp only [sourcePair] at hD hC
  rw [hD,hC]
  simp only [Complex.star_def,map_mul,map_ofNat,Complex.conj_I]
  ring
private theorem scalar_cross_real(w d:QuantumTest):
    (sourcePair w (B d)).re=(sourcePair d (B w)).re:=by
  rw [original_scalar_pair]
  have h:=congrArg Complex.re (GaussNativeForm.pair_conjugate d (B w))
  simpa only [Complex.conj_re] using h.symm
private theorem scalar_current_pair(w:QuantumTest):
    reverseScalarCurrent w= -2*(sourcePair (Z w) (B w)).re:=by
  change (sourcePair w (Z (B w)-B (Z w))).re= _
  rw [pair_sub_r,Z_pair,Complex.sub_re,Complex.neg_re,scalar_cross_real]
  ring
private theorem scalar_energy_derivative(w d:ℝ→QuantumTest)(q:ℝ)
    (hw:HasDerivAt (fun r=>embed (w r)) (embed (d q)) q)
    (hb:HasDerivAt (fun r=>embed (B (w r))) (embed (B (d q))) q):
    HasDerivAt (fun r=>scalarEnergy (w r)) (2*(sourcePair (d q) (B (w q))).re) q:=by
  have h:=hw.inner ℂ hb
  have hp:HasDerivAt (fun r:ℝ=>sourcePair (w r) (B (w r)))
      (sourcePair (w q) (B (d q))+sourcePair (d q) (B (w q))) q:=by
    simpa only [sourcePair] using! h
  have hr:HasDerivAt (fun r:ℝ=>(sourcePair (w r) (B (w r))).re)
      ((sourcePair (w q) (B (d q))+sourcePair (d q) (B (w q))).re) q:=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt q hp
  have hf:(fun r:ℝ=>(sourcePair (w r) (B (w r))).re)=(fun r=>scalarEnergy (w r)):=
    funext (fun r=>original_scalar_energy (w r))
  rw [hf] at hr
  rw [Complex.add_re,scalar_cross_real] at hr
  simpa only [two_mul] using! hr
private theorem scalar_frequency_derivative(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    HasDerivAt (fun r:ℝ=>scalarEnergy (wholeClockState s hs half advanced m ell F g x r))
      (2*(sourcePair (wholeResponseDerivative s hs half advanced m ell F g x q)
        (B (wholeClockState s hs half advanced m ell F g x q))).re) q:=by
  have h1:=whole_word_derivative s hs half advanced m ell F g x q 1
  simp only [Module.End.one_apply] at h1
  exact scalar_energy_derivative _ _ q h1 (whole_word_derivative s hs half advanced m ell F g x q B)

def wholeScalarFrequencyRemainder(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let w:=wholeClockState s hs half advanced m ell F g x q
  let d:=wholeResponseDerivative s hs half advanced m ell F g x q
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  18*scalarEnergy w+36*z.im*(sourcePair d (B w)).im-
    2*(sourcePair (wholeReverseSource s hs half advanced m ell F g x q) (B w)).re

/-- The actual finite scalar Noether work becomes a physical-frequency derivative plus its literal imaginary-pole and complete compression-force remainder. No damping threshold or physical-time growth premise is introduced. -/
theorem actual_whole_reverse_scalar_frequency_work(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)
    (x:ℝ×ℝ)(q h:ℝ)(hh:0<h):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
    HasDerivAt (fun r:ℝ=>18*r*scalarEnergy (wholeClockState s hs half advanced m ell F g x r))
      (reverseScalarNoetherWork h z a.1 a.2-wholeScalarFrequencyRemainder s hs half advanced m ell F g x q) q:=by
  dsimp only
  let w:=wholeClockState s hs half advanced m ell F g x q
  let d:=wholeResponseDerivative s hs half advanced m ell F g x q
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  have hp:=congrArg (fun v:QuantumTest=>(sourcePair v (B w)).re)
    (actual_whole_reverse_frequency_ward s hs half advanced m ell F g x q)
  rw [whole_jet_split] at hp
  simp only [pair_add_l,pair_smul_l,Complex.add_re,Complex.mul_re,
    Complex.star_def,Complex.conj_re,Complex.conj_im,map_ofNat,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,sub_zero,neg_mul] at hp
  have hzr:z.re=q:=by
    cases advanced <;> simp [z,actualFrequency,line]
  have he:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  have hw:=(actual_reverse_scalar_noether_work h hh z (Hz half advanced q) _ _ he).2
  have hstate(r:ℝ):(clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g r)).1=
      wholeClockState s hs half advanced m ell F g x r:=by unfold wholeClockState;rfl
  simp only [hstate] at hw ⊢
  have hder:=((hasDerivAt_id q).mul (scalar_frequency_derivative s hs half advanced m ell F g x q)).const_mul 18
  convert! hder using 1
  · funext r;simp only [Pi.mul_apply,id_eq];ring
  · change reverseScalarNoetherWork h z w (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2-
      wholeScalarFrequencyRemainder s hs half advanced m ell F g x q=
      18*(1*scalarEnergy w+q*(2*(sourcePair d (B w)).re))
    rw [hw,scalar_current_pair]
    unfold wholeScalarFrequencyRemainder
    change (sourcePair (Z w) (B w)).re+18*((sourcePair w (B w)).re+
      (z.re*(sourcePair d (B w)).re- -(z.im*(sourcePair d (B w)).im)))=_ at hp
    rw [hzr] at hp
    have hE:=original_scalar_energy w
    linarith only [hp,hE]

/-- These are the actual whole-source columns, including the original escape column and the selected electric step. -/
def wholeClockColumn(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(j:SourceJointResidualEnergy.Channel F):QuantumTest:=
  correctedCompleteCore s hs x.1 x.2
    (FinitePhysicalSource.sourceColumn (wholeSourceMap s hs half advanced m ell F g) m ell F g j)

theorem actual_whole_clock_channels(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeClockState s hs half advanced m ell F g x q=
      ∑j:SourceJointResidualEnergy.Channel F,
        ((SourceJointResidualEnergy.channelValue F j:ℂ)-actualFrequency advanced (sourceNoetherFrequency half) q)⁻¹ •
          wholeClockColumn s hs half advanced m ell F g x j:=by
  have h:=congrArg (correctedCompleteCore s hs x.1 x.2)
    (((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).1)
  simpa only [wholeClockState,clockSourcePair,wholeClockColumn,map_sum,map_smul] using h

theorem actual_whole_clock_derivative_channels(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeResponseDerivative s hs half advanced m ell F g x q=
      ∑j:SourceJointResidualEnergy.Channel F,
        (((SourceJointResidualEnergy.channelValue F j:ℂ)-actualFrequency advanced (sourceNoetherFrequency half) q)⁻¹)^2 •
          wholeClockColumn s hs half advanced m ell F g x j:=by
  have hj:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset (SourceJointResidualEnergy.Channel F))) (fun j _=>
    (actual_physical_pole_derivative advanced (sourceNoetherFrequency half) (frequency_positive half)
      (SourceJointResidualEnergy.channelValue F j) q).smul_const
        (embed (wholeClockColumn s hs half advanced m ell F g x j)))
  have hd:=whole_word_derivative s hs half advanced m ell F g x q 1
  simp only [Module.End.one_apply,actual_whole_clock_channels,map_sum,map_smul] at hd
  apply embed_injective
  simpa only [map_sum,map_smul] using hd.unique hj

open MeasureTheory Filter SourceFourPoleEnergyClosed SourceJointResidualEnergy
private abbrev P(advanced:Bool)(μ a q:ℝ):ℂ:=((a:ℂ)-actualFrequency advanced μ q)⁻¹
private abbrev signedMu(advanced:Bool)(μ:ℝ):ℝ:=if advanced then -μ else μ
private theorem physical_line(advanced:Bool)(μ q:ℝ):
    actualFrequency advanced μ q=(q:ℂ)+(signedMu advanced μ:ℂ)*Complex.I:=by
  cases advanced <;> simp [actualFrequency,line,signedMu]
private theorem pole_ne(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):
    (a:ℂ)-actualFrequency advanced μ q≠0:=by
  intro h
  apply reverse_frequency_nonreal advanced μ hμ q
  rw [←sub_eq_zero.mp h]
  rfl
private theorem pole_bound(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):‖P advanced μ a q‖ ≤ μ⁻¹:=by
  have hb:μ ≤ ‖(a:ℂ)-actualFrequency advanced μ q‖:=by
    have h:=Complex.abs_im_le_norm ((a:ℂ)-actualFrequency advanced μ q)
    cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,Complex.star_def,
      Complex.sub_im,Complex.ofReal_im,Complex.conj_im,line_im,zero_sub,abs_neg,abs_of_pos hμ] using h
  exact (norm_inv _).trans_le ((inv_le_inv₀ (norm_pos_iff.mpr (pole_ne advanced μ hμ a q)) hμ).mpr hb)
private theorem pole_measurable(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a:ℝ):
    AEStronglyMeasurable (P advanced μ a):=
  (continuous_iff_continuousAt.mpr (fun q=>(actual_physical_pole_derivative advanced μ hμ a q).continuousAt)).aestronglyMeasurable
private theorem pole_pair_integrable(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Integrable (fun q:ℝ=>star (P advanced μ a q)*P advanced μ b q):=by
  cases advanced
  · simpa only [P,actualFrequency,Bool.false_eq_true,ite_false,pole] using! two_pole_integrable μ a b hμ
  · have h:=(RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (two_pole_integrable μ a b hμ)
    have he(q:ℝ):star (P true μ a q)*P true μ b q=star (star (pole μ a q)*pole μ b q):=by
      simp only [P,actualFrequency,ite_true,pole,star_mul,star_inv₀,star_sub,
        Complex.star_def,Complex.conj_ofReal]
      ring
    simpa only [he] using! h
private theorem pole_weight(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):
    (q:ℂ)*P advanced μ a q=((a:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)*P advanced μ a q-1:=by
  have h:=mul_inv_cancel₀ (pole_ne advanced μ hμ a q)
  change ((a:ℂ)-actualFrequency advanced μ q)*P advanced μ a q=1 at h
  rw [physical_line] at h
  linear_combination (norm:=ring) -h
private theorem pole_star_weight(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):
    (q:ℂ)*star (P advanced μ a q)=((a:ℂ)+(signedMu advanced μ:ℂ)*Complex.I)*star (P advanced μ a q)-1:=by
  have h:=congrArg star (pole_weight advanced μ hμ a q)
  simp only [star_mul,star_sub,star_one,Complex.star_def,Complex.conj_ofReal,Complex.conj_I] at h
  simp only [Complex.star_def]
  linear_combination (norm:=ring) h
private def momentPair(advanced:Bool)(μ a b q:ℝ):ℂ:=(q:ℂ)*(star (P advanced μ a q)*P advanced μ b q)
private def momentJet(advanced:Bool)(μ a b q:ℝ):ℂ:=
  star (P advanced μ a q)*P advanced μ b q+
    (q:ℂ)*(star ((P advanced μ a q)^2)*P advanced μ b q+star (P advanced μ a q)*(P advanced μ b q)^2)
private theorem moment_derivative(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b q:ℝ):
    HasDerivAt (momentPair advanced μ a b) (momentJet advanced μ a b q) q:=by
  have h:=(hasDerivAt_id q).ofReal_comp.mul
    (((actual_physical_pole_derivative advanced μ hμ a q).star).mul
      (actual_physical_pole_derivative advanced μ hμ b q))
  simpa only [momentPair,momentJet,one_mul,Complex.ofReal_one,id_eq] using! h
private theorem moment_jet_integrable(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Integrable (momentJet advanced μ a b):=by
  have h0:=pole_pair_integrable advanced μ hμ a b
  have ha:=h0.mul_bdd (c:=μ⁻¹) (pole_measurable advanced μ hμ a).star
    (Eventually.of_forall (fun q=>by
      change ‖star (P advanced μ a q)‖ ≤ μ⁻¹
      simpa only [norm_star] using pole_bound advanced μ hμ a q))
  have hb:=h0.mul_bdd (pole_measurable advanced μ hμ b)
    (Eventually.of_forall (fun q=>pole_bound advanced μ hμ b q))
  have he(q:ℝ):momentJet advanced μ a b q=
      -(star (P advanced μ a q)*P advanced μ b q)+
      ((a:ℂ)+(signedMu advanced μ:ℂ)*Complex.I)*(star (P advanced μ a q)*P advanced μ b q*star (P advanced μ a q))+
      ((b:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)*(star (P advanced μ a q)*P advanced μ b q*P advanced μ b q):=by
    have hA:=pole_star_weight advanced μ hμ a q
    have hB:=pole_weight advanced μ hμ b q
    unfold momentJet
    simp only [star_pow]
    linear_combination (norm:=ring) star (P advanced μ a q)*P advanced μ b q*hA+
      star (P advanced μ a q)*P advanced μ b q*hB
  exact (((h0.neg).add (ha.const_mul _)).add (hb.const_mul _)).congr (Eventually.of_forall (fun q=>(he q).symm))
private theorem pole_top(advanced:Bool)(μ a:ℝ):Tendsto (P advanced μ a) atTop (𝓝 0):=by
  have h:=tendsto_inv₀_cobounded.comp
    ((tendsto_const_sub_cobounded ((a:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)).comp
      (RCLike.tendsto_ofReal_atTop_cobounded ℂ))
  convert! h using 1
  funext q
  unfold P
  rw [physical_line]
  change ((a:ℂ)-((q:ℂ)+(signedMu advanced μ:ℂ)*Complex.I))⁻¹=
    (((a:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)-(q:ℂ))⁻¹
  congr 1
  ring
private theorem pole_bot(advanced:Bool)(μ a:ℝ):Tendsto (P advanced μ a) atBot (𝓝 0):=by
  have h:=tendsto_inv₀_cobounded.comp
    ((tendsto_const_sub_cobounded ((a:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)).comp
      (RCLike.tendsto_ofReal_atBot_cobounded ℂ))
  convert! h using 1
  funext q
  unfold P
  rw [physical_line]
  change ((a:ℂ)-((q:ℂ)+(signedMu advanced μ:ℂ)*Complex.I))⁻¹=
    (((a:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)-(q:ℂ))⁻¹
  congr 1
  ring
private theorem moment_zero(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Tendsto (momentPair advanced μ a b) atTop (𝓝 0) ∧ Tendsto (momentPair advanced μ a b) atBot (𝓝 0):=by
  have he(q:ℝ):momentPair advanced μ a b q=
      (((a:ℂ)+(signedMu advanced μ:ℂ)*Complex.I)*star (P advanced μ a q)-1)*P advanced μ b q:=by
    unfold momentPair
    rw [←mul_assoc,pole_star_weight advanced μ hμ a q]
  constructor
  · simpa only [mul_zero,sub_zero,zero_mul] using
      ((((pole_top advanced μ a).star.const_mul ((a:ℂ)+(signedMu advanced μ:ℂ)*Complex.I)).sub_const 1).mul
        (pole_top advanced μ b)).congr' (Eventually.of_forall (fun q=>(he q).symm))
  · simpa only [mul_zero,sub_zero,zero_mul] using
      ((((pole_bot advanced μ a).star.const_mul ((a:ℂ)+(signedMu advanced μ:ℂ)*Complex.I)).sub_const 1).mul
        (pole_bot advanced μ b)).congr' (Eventually.of_forall (fun q=>(he q).symm))
private theorem finite_source_pair {ι:Type*}[Fintype ι](c:ι→QuantumTest)(a:ι→ℂ)(T:End):
    sourcePair (∑i,a i • c i) (T (∑i,a i • c i))=
      ∑i,∑j,(star (a i)*a j)*sourcePair (c i) (T (c j)):=by
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
private theorem whole_pair_channels(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ)(T:End):
    sourcePair (wholeClockState s hs half advanced m ell F g x q) (T (wholeClockState s hs half advanced m ell F g x q))=
      ∑i:Channel F,∑j:Channel F,(star (P advanced (sourceNoetherFrequency half) (channelValue F i) q)*
        P advanced (sourceNoetherFrequency half) (channelValue F j) q)*
        sourcePair (wholeClockColumn s hs half advanced m ell F g x i)
          (T (wholeClockColumn s hs half advanced m ell F g x j)):=by
  have h:=actual_whole_clock_channels s hs half advanced m ell F g x q
  exact (congrArg₂ (fun a b:QuantumTest=>sourcePair a (T b)) h h).trans (finite_source_pair _ _ T)
private theorem whole_pair_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(T:End):
    Integrable (fun q:ℝ=>sourcePair (wholeClockState s hs half advanced m ell F g x q)
      (T (wholeClockState s hs half advanced m ell F g x q))):=by
  have h(i j:Channel F):=(pole_pair_integrable advanced (sourceNoetherFrequency half) (frequency_positive half)
    (channelValue F i) (channelValue F j)).mul_const
      (sourcePair (wholeClockColumn s hs half advanced m ell F g x i) (T (wholeClockColumn s hs half advanced m ell F g x j)))
  exact (integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>h i j))).congr
    (Eventually.of_forall (fun q=>(whole_pair_channels s hs half advanced m ell F g x q T).symm))
private def scalarEntry(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(i j:Channel F):ℂ:=
  sourcePair (wholeClockColumn s hs half advanced m ell F g x i) (B (wholeClockColumn s hs half advanced m ell F g x j))
private def scalarMoment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℂ:=
  ∑i:Channel F,∑j:Channel F,momentPair advanced (sourceNoetherFrequency half) (channelValue F i) (channelValue F j) q*
    scalarEntry s hs half advanced m ell F g x i j
private def scalarMomentJet(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℂ:=
  ∑i:Channel F,∑j:Channel F,momentJet advanced (sourceNoetherFrequency half) (channelValue F i) (channelValue F j) q*
    scalarEntry s hs half advanced m ell F g x i j
private theorem scalar_moment_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    18*q*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)=
      18*(scalarMoment s hs half advanced m ell F g x q).re:=by
  have hp:(q:ℂ)*sourcePair (wholeClockState s hs half advanced m ell F g x q)
      (B (wholeClockState s hs half advanced m ell F g x q))=scalarMoment s hs half advanced m ell F g x q:=by
    rw [whole_pair_channels]
    simp only [scalarMoment,scalarEntry,momentPair,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h:=congrArg Complex.re hp
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,original_scalar_energy] at h
  linear_combination (norm:=ring) 18*h
private theorem scalar_moment_derivative(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    HasDerivAt (fun r:ℝ=>18*r*scalarEnergy (wholeClockState s hs half advanced m ell F g x r))
      (18*(scalarMomentJet s hs half advanced m ell F g x q).re) q:=by
  have hc:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset (Channel F))) (fun i _=>
    HasDerivAt.fun_sum (u:=(Finset.univ:Finset (Channel F))) (fun j _=>
      (moment_derivative advanced (sourceNoetherFrequency half) (frequency_positive half)
        (channelValue F i) (channelValue F j) q).mul_const (scalarEntry s hs half advanced m ell F g x i j)))
  have ht:HasDerivAt (scalarMoment s hs half advanced m ell F g x)
      (scalarMomentJet s hs half advanced m ell F g x q) q:=hc
  have hr:HasDerivAt (fun r:ℝ=>(scalarMoment s hs half advanced m ell F g x r).re)
      (scalarMomentJet s hs half advanced m ell F g x q).re q:=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt q ht
  simpa only [scalar_moment_return] using! hr.const_mul 18
private theorem scalar_moment_jet_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>18*(scalarMomentJet s hs half advanced m ell F g x q).re):=by
  have h(i j:Channel F):=(moment_jet_integrable advanced (sourceNoetherFrequency half) (frequency_positive half)
    (channelValue F i) (channelValue F j)).mul_const (scalarEntry s hs half advanced m ell F g x i j)
  exact ((integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>h i j))).re).const_mul 18
private theorem scalar_frequency_boundary(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Tendsto (fun q:ℝ=>18*q*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)) atTop (𝓝 0) ∧
    Tendsto (fun q:ℝ=>18*q*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)) atBot (𝓝 0):=by
  have h(𝓕:Filter ℝ)(hp:∀i j:Channel F,Tendsto (momentPair advanced (sourceNoetherFrequency half)
      (channelValue F i) (channelValue F j)) 𝓕 (𝓝 0)):
      Tendsto (fun q:ℝ=>18*q*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)) 𝓕 (𝓝 0):=by
    have hc:=tendsto_finsetSum Finset.univ (fun i _=>tendsto_finsetSum Finset.univ (fun j _=>
      (hp i j).mul_const (scalarEntry s hs half advanced m ell F g x i j)))
    have hc':Tendsto (scalarMoment s hs half advanced m ell F g x) 𝓕 (𝓝 0):=by
      unfold scalarMoment
      simpa only [zero_mul,Finset.sum_const_zero] using! hc
    have hr:=(Complex.continuous_re.tendsto 0).comp hc'
    have hr':Tendsto (fun q:ℝ=>(scalarMoment s hs half advanced m ell F g x q).re) 𝓕 (𝓝 0):=by
      simpa only [Function.comp_apply,Complex.zero_re] using! hr
    simpa only [scalar_moment_return,mul_zero] using hr'.const_mul 18
  exact ⟨h atTop (fun i j=>(moment_zero advanced (sourceNoetherFrequency half) (frequency_positive half)
    (channelValue F i) (channelValue F j)).1),
    h atBot (fun i j=>(moment_zero advanced (sourceNoetherFrequency half) (frequency_positive half)
    (channelValue F i) (channelValue F j)).2)⟩

/-- Both frequency boundaries are paid from the actual finite/escape source columns. The complete finite scalar Noether work therefore returns its full signed frequency remainder after integration; the imaginary-pole cross is retained. -/
theorem actual_whole_reverse_scalar_frequency_integral(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)
    (x:ℝ×ℝ)(h:ℝ)(hh:0<h):
    let W:=fun q:ℝ=>let z:=actualFrequency advanced (sourceNoetherFrequency half) q
      let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
      reverseScalarNoetherWork h z a.1 a.2
    let J:=wholeScalarFrequencyRemainder s hs half advanced m ell F g x
    Integrable W ∧ Integrable J ∧ (∫q:ℝ,W q)=(∫q:ℝ,J q):=by
  dsimp only
  let W:=fun q:ℝ=>reverseScalarNoetherWork h (actualFrequency advanced (sourceNoetherFrequency half) q)
    (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).1
    (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2
  let J:=wholeScalarFrequencyRemainder s hs half advanced m ell F g x
  have he(q:ℝ):W q-J q=18*(scalarMomentJet s hs half advanced m ell F g x q).re:=
    (actual_whole_reverse_scalar_frequency_work s hs half advanced m ell F g x q h hh).unique
      (scalar_moment_derivative s hs half advanced m ell F g x q)
  have hi:Integrable (fun q:ℝ=>W q-J q):=
    (scalar_moment_jet_integrable s hs half advanced m ell F g x).congr (Eventually.of_forall (fun q=>(he q).symm))
  have hiW:Integrable W:=by
    have hiC:Integrable (fun q:ℝ=>reverseScalarCurrent (wholeClockState s hs half advanced m ell F g x q)):=by
      simpa only [reverseScalarCurrent] using! (whole_pair_integrable s hs half advanced m ell F g x (bracket Z B)).re
    apply hiC.congr
    apply Eventually.of_forall
    intro q
    unfold wholeClockState
    exact ((actual_reverse_scalar_noether_work h hh _ (Hz half advanced q) _ _
      (((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)).2).symm
  have hiJ:Integrable J:=by
    apply (hiW.sub hi).congr
    exact Eventually.of_forall (fun q=>by dsimp only [Pi.sub_apply];ring)
  have hend:=scalar_frequency_boundary s hs half advanced m ell F g x
  have hint:(∫q:ℝ,W q-J q)=0:=by
    simpa only [sub_self] using integral_of_hasDerivAt_of_tendsto
      (fun q=>actual_whole_reverse_scalar_frequency_work s hs half advanced m ell F g x q h hh) hi hend.2 hend.1
  rw [integral_sub hiW hiJ] at hint
  exact ⟨hiW,hiJ,sub_eq_zero.mp hint⟩

end LowEnergy.ReverseNativeFrequencyWard
