import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiForceNoetherCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeReverseSourceSplit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseForceNoetherPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockYukawaCubicCurrent SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget SourceScalarSpatialCurrent
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceScalarPairedTransport
open SourceClockPhiNativeJointPayment SourceInverseNoetherChannelGap SourceJointResidualEnergy SourceBulkTwoTime
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource FullYSourceResolventGraphSplice FinitePhysicalSource
open ClockPhiHeatCorrectedCovarianceSource
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev B:End:=scalarBulkComplete
private abbrev U:End:=inverseVolumeAction
attribute [local irreducible] sourcePair embed diagonalAction compressionCore resolventCore
  reverseNativeClock reverseScaleForce reverseCompressionForce scalarBulkComplete
  normalizedState normalizedForcing wholeClockState wholeSourceNext wholeSourceMap correctedCompleteCore weightedElectricCurrent
  forceResponse phaseRow inputSeed wholeClockWord
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private abbrev hz(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q
private theorem normalized_two_seed(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    normalizedState m ell F z hz g=
      ∑i:Fin 2,phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (inputSeed g i))):=by
  simp only [Fin.sum_univ_two]
  have hr:coreEquiv.symm (phiRadiusSource g)=phiRadiusAction (coreEquiv.symm g):=by
    unfold phiRadiusSource
    exact coreEquiv.symm_apply_apply _
  unfold normalizedState phaseRow inputSeed
  change phiThetaAction m ell (resolventCore F z hz (coreEquiv.symm g))-
    phiInverseAction (phiThetaAction m ell (resolventCore F z hz (phiRadiusAction (coreEquiv.symm g))))=
    phiThetaAction m ell (resolventCore F z hz (coreEquiv.symm g))+
    (-(phiInverseAction*phiThetaAction m ell)) (resolventCore F z hz (coreEquiv.symm (phiRadiusSource g)))
  simp only [hr,LinearMap.neg_apply,Module.End.mul_apply,sub_eq_add_neg]
private theorem whole_two_seed(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeClockState s hs half advanced m ell F g x q=
      ∑i:Fin 2,wholeClockWord s hs half advanced m ell F g x i
        (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
          (coreEquiv.symm (inputSeed g i))):=by
  have hm:(wholeSourceNext s hs half advanced m ell F g q).1=
      wholeSourceMap s hs half advanced m ell F g (frequencyState half advanced m ell F g q):=by
    simp only [wholeSourceNext,wholeSourceMap,electricSourceDirection,Prod.fst_add,Prod.smul_fst,
      LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply]
  unfold wholeClockState
  simp only [clockSourcePair,hm,frequencyState,normalized_two_seed,map_sum]
  simp only [wholeClockWord,Module.End.mul_apply]
private theorem channel_resolution(F:Index)(g:diagonal.domain):
    (∑i:Channel F,channelTest F g i)=coreEquiv.symm g:=by
  apply embed_injective
  have h:=actual_core_time F g 0
  simp only [coreTime,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_smul,
    SourceFiniteUnitary.time_zero,one_apply_eq_self] at h
  exact h.trans (congrArg Subtype.val (coreEquiv.apply_symm_apply g)).symm
private theorem whole_seed_zero(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    (∑i:Fin 2,wholeClockWord s hs half advanced m ell F g x i (coreEquiv.symm (inputSeed g i)))=0:=by
  have h:=actual_source_column_zero (correctedCompleteCore s hs x.1 x.2*wholeSourceMap s hs half advanced m ell F g) m ell F g
  unfold sourceColumn at h
  rw [Finset.sum_comm] at h
  simp_rw [←map_sum,channel_resolution] at h
  simpa only [wholeClockWord,map_sum,Module.End.mul_apply] using h

def wordPhysicalEscape(F:Index)(A:End):End:=bracket H0 A+A*defectAction F
private theorem word_source(F:Index)(z:ℂ)(hz:z.im≠0)(A:End)(f:QuantumTest):
    H0 (A (resolventCore F z hz f))=
      A f+wordPhysicalEscape F A (resolventCore F z hz f)+z • A (resolventCore F z hz f):=by
  have h:=(actual_force_response_full_noether F z hz f).1
  simp only [wordPhysicalEscape,bracket,LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,h,map_add,map_smul]
  module
private theorem word_force_source(F:Index)(z:ℂ)(hz:z.im≠0)(A:End)(f:QuantumTest):
    H0 (A (forceResponse F z hz f))=
      A (reverseCompressionForce F (resolventCore F z hz f))+
        wordPhysicalEscape F A (forceResponse F z hz f)+z • A (forceResponse F z hz f):=by
  simpa only [forceResponse] using word_source F z hz A (reverseCompressionForce F (resolventCore F z hz f))

def wholeForceState(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  ∑i:Fin 2,wholeClockWord s hs half advanced m ell F g x i
    (forceResponse F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (coreEquiv.symm (inputSeed g i)))
def wholeForceEscape(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  ∑i:Fin 2,wordPhysicalEscape F (wholeClockWord s hs half advanced m ell F g x i)
    (forceResponse F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (coreEquiv.symm (inputSeed g i)))
def wholeForceOuter(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  ∑i:Fin 2,bracket (reverseCompressionForce F) (wholeClockWord s hs half advanced m ell F g x i)
    (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (coreEquiv.symm (inputSeed g i)))
def wholeForceSource(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  reverseCompressionForce F (wholeClockState s hs half advanced m ell F g x q)-
    wholeForceOuter s hs half advanced m ell F g x q+wholeForceEscape s hs half advanced m ell F g x q

/-- The original zero column removes the fixed forcing before frequency integration. The remaining forcing is the whole original bracket plus full deltaF. -/
theorem actual_whole_forcing_escape(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2=
      ∑i:Fin 2,wordPhysicalEscape F (wholeClockWord s hs half advanced m ell F g x i)
        (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
          (coreEquiv.symm (inputSeed g i))):=by
  have h:=congrArg (fun v:Fin 2→QuantumTest=>∑i,v i) (funext (fun i=>
    word_source F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (wholeClockWord s hs half advanced m ell F g x i) (coreEquiv.symm (inputSeed g i))))
  simp only [←map_sum,Finset.sum_add_distrib,←Finset.smul_sum,←whole_two_seed,whole_seed_zero,zero_add] at h
  have hs0:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  simp only [wholeClockState,H0] at h
  exact add_right_cancel (hs0.symm.trans h)

/-- The complete force response generates its own H0 forcing on the unchanged whole source. -/
theorem actual_whole_force_full_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    H0 (wholeForceState s hs half advanced m ell F g x q)=
      wholeForceSource s hs half advanced m ell F g x q+
        actualFrequency advanced (sourceNoetherFrequency half) q • wholeForceState s hs half advanced m ell F g x q:=by
  have h:=congrArg (fun v:Fin 2→QuantumTest=>∑i,v i) (funext (fun i=>
    word_force_source F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (wholeClockWord s hs half advanced m ell F g x i) (coreEquiv.symm (inputSeed g i))))
  simp only [←map_sum,Finset.sum_add_distrib,←Finset.smul_sum] at h
  have he:reverseCompressionForce F (wholeClockState s hs half advanced m ell F g x q)-
      wholeForceOuter s hs half advanced m ell F g x q=
        ∑i:Fin 2,wholeClockWord s hs half advanced m ell F g x i
          (reverseCompressionForce F (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q)
            (hz half advanced q) (coreEquiv.symm (inputSeed g i)))):=by
    rw [whole_two_seed s hs half advanced m ell F g x q]
    simp only [wholeForceOuter,map_sum,bracket,LinearMap.sub_apply,Module.End.mul_apply,Finset.sum_sub_distrib]
    module
  change H0 (wholeForceState s hs half advanced m ell F g x q)=
    (reverseCompressionForce F (wholeClockState s hs half advanced m ell F g x q)-
      wholeForceOuter s hs half advanced m ell F g x q)+wholeForceEscape s hs half advanced m ell F g x q+
      actualFrequency advanced (sourceNoetherFrequency half) q • wholeForceState s hs half advanced m ell F g x q
  rw [he]
  exact h

def wholeForceNativeDebit(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let w:=wholeClockState s hs half advanced m ell F g x q
  let v:=wholeForceState s hs half advanced m ell F g x q
  let f:=(clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2;
  -9*(sourcePair w (SourceScalarOscillatorAbsorption.scalarCurrent w)).im-
    96*(sourcePair w (U (scalarSpatialDivergence w))).im+
      (sourcePair w (forceScalarProjectionCurrent F w)).im/2-
      (sourcePair (wholeForceOuter s hs half advanced m ell F g x q) (B w)).im+
      (sourcePair (wholeForceEscape s hs half advanced m ell F g x q) (B w)).im-
      (sourcePair (B v) f).im-(sourcePair v (bracket H0 B w)).im

/-- The original whole force-B price is a signed native/scalar projection-current debit with its complete physical forcing. No force norm or fiber energy is assumed. -/
theorem actual_whole_force_native_noether(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    2*(actualFrequency advanced (sourceNoetherFrequency half) q).im*
      (sourcePair (wholeForceState s hs half advanced m ell F g x q)
        (B (wholeClockState s hs half advanced m ell F g x q))).re=
      wholeForceNativeDebit s hs half advanced m ell F g x q:=by
  have hw:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  have hv:=actual_whole_force_full_source s hs half advanced m ell F g x q
  have hw':H0 (wholeClockState s hs half advanced m ell F g x q)=
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2+
        actualFrequency advanced (sourceNoetherFrequency half) q • wholeClockState s hs half advanced m ell F g x q:=by
    simpa only [wholeClockState] using hw
  have h:=actual_full_source_mixed_scalar_noether _ _ _ _ _ hw' hv
  rw [wholeForceSource] at h
  have hpair(a b c:QuantumTest):sourcePair (a-b+c) (B (wholeClockState s hs half advanced m ell F g x q))=
    sourcePair a (B (wholeClockState s hs half advanced m ell F g x q))-
      sourcePair b (B (wholeClockState s hs half advanced m ell F g x q))+
      sourcePair c (B (wholeClockState s hs half advanced m ell F g x q)):=by
    simp only [sourcePair,map_add,map_sub,inner_add_left,inner_sub_left]
  rw [hpair,Complex.add_im,Complex.sub_im,actual_compression_force_scalar_price] at h
  exact h

/-- The virtual source is exactly the force component already present in the original frequency Ward. -/
theorem actual_whole_force_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeForceState s hs half advanced m ell F g x q=
      correctedCompleteCore s hs x.1 x.2 (wholeSourceMap s hs half advanced m ell F g
        (reverseForceInput m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)):=by
  simp only [wholeForceState,reverseForceInput,forceResponse,wholeClockWord,map_sum,Module.End.mul_apply]
end LowEnergy.ReverseForceNoetherPayer
