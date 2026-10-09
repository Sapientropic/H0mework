import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedNativeForceCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeForceNoetherDebit
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeGaugeScalarReductionSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseBalancedForcePayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockYukawaCubicCurrent SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget SourceScalarSpatialCurrent
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceScalarPairedTransport
open SourceClockPhiNativeJointPayment SourceInverseNoetherChannelGap SourceJointResidualEnergy SourceBulkTwoTime
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource FullYSourceResolventGraphSplice FinitePhysicalSource
open ReverseForceNoetherPayer ReverseScalarGaugeWard ReverseGaugeOuterPayment
open ClockPhiHeatCorrectedCovarianceSource
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev B:End:=scalarBulkComplete
private abbrev U:End:=inverseVolumeAction
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev Zbar:End:=reverseNativeClock-(9:ℂ) • G

def balancedProjectionCurrent(F:Index):End:=
  (18:ℂ) • bracket (defectAction F) B-bracket (bracket Zbar (defectAction F)) B

def balancedResponse(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):QuantumTest:=
  resolventCore F z hz (balancedCompressionForce F (resolventCore F z hz f))
attribute [local irreducible] sourcePair embed diagonalAction compressionCore resolventCore
  reverseNativeClock reverseScaleForce balancedCompressionForce scalarBulkComplete
  normalizedState normalizedForcing wholeClockState wholeSourceNext wholeSourceMap correctedCompleteCore weightedElectricCurrent
  balancedResponse phaseRow inputSeed wholeClockWord
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
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem compression_pair(F:Index)(f g:QuantumTest):sourcePair f (compressionCore F g)=sourcePair (compressionCore F f) g:=by
  have he(q:QuantumTest):embed (compressionCore F q)=GaussGradedCompression.compression F (embed q):=by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp only [sourcePair,he]
  exact (GaussGradedCompression.compression_pair F (embed f) (embed g)).symm
private theorem gauge_force_pair(F:Index)(f g:QuantumTest):
    sourcePair (gaugeCompressionForce F f) g=sourcePair f (gaugeCompressionForce F g):=by
  simp only [gaugeCompressionForce,bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_l,pair_sub_r]
  rw [actual_gauge_pair,←compression_pair,←compression_pair,actual_gauge_pair]
  ring

theorem actual_balanced_compression_pair(F:Index)(f g:QuantumTest):
    sourcePair (balancedCompressionForce F f) g=sourcePair f (balancedCompressionForce F g):=by
  simp only [balancedCompressionForce,LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_l,pair_sub_r,
    pair_smul_l,pair_smul_r,Complex.star_def,Complex.conj_ofNat,actual_compression_force_pair,gauge_force_pair]

theorem actual_balanced_compression_scalar_current(F:Index):
    bracket (balancedCompressionForce F) B=(-18:ℂ) • SourceScalarOscillatorAbsorption.scalarCurrent-
      (336:ℂ) • (U*scalarSpatialDivergence)+balancedProjectionCurrent F:=by
  have he:=actual_balanced_compression_departments F
  change balancedCompressionForce F=gaugeBalancedNativeForce+(18:ℂ) • defectAction F-bracket Zbar (defectAction F) at he
  rw [he]
  have hn:=actual_balanced_native_scalar_current
  unfold balancedProjectionCurrent bracket at hn ⊢
  linear_combination (norm:=(noncomm_ring;module)) hn
private theorem balanced_force_scalar_price(F:Index)(w:QuantumTest):
    (sourcePair (balancedCompressionForce F w) (B w)).im=
      -9*(sourcePair w (SourceScalarOscillatorAbsorption.scalarCurrent w)).im-
        168*(sourcePair w (U (scalarSpatialDivergence w))).im+
          (sourcePair w (balancedProjectionCurrent F w)).im/2:=by
  have hp:sourcePair w (bracket (balancedCompressionForce F) B w)=
      sourcePair (balancedCompressionForce F w) (B w)-sourcePair (B w) (balancedCompressionForce F w):=by
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r,←actual_balanced_compression_pair,original_scalar_pair]
  have hc:=congrArg Complex.im (GaussNativeForm.pair_conjugate (balancedCompressionForce F w) (B w))
  have hi:=congrArg Complex.im hp
  rw [actual_balanced_compression_scalar_current] at hi
  have hadd(a b c:QuantumTest):sourcePair a (b+c)=sourcePair a b+sourcePair a c:=by simp only [sourcePair,map_add,inner_add_right]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    hadd,pair_sub_r,pair_smul_r,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.re_ofNat,
    Complex.im_ofNat,Complex.neg_re,Complex.neg_im,zero_mul,add_zero] at hi
  simp only [Complex.conj_im] at hc
  linarith only [hi,hc]

private theorem word_source(F:Index)(z:ℂ)(hz:z.im≠0)(A:End)(f:QuantumTest):
    H0 (A (resolventCore F z hz f))=
      A f+wordPhysicalEscape F A (resolventCore F z hz f)+z • A (resolventCore F z hz f):=by
  have h:=(actual_force_response_full_noether F z hz f).1
  simp only [wordPhysicalEscape,bracket,LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,h,map_add,map_smul]
  module
private theorem word_force_source(F:Index)(z:ℂ)(hz:z.im≠0)(A:End)(f:QuantumTest):
    H0 (A (balancedResponse F z hz f))=
      A (balancedCompressionForce F (resolventCore F z hz f))+
        wordPhysicalEscape F A (balancedResponse F z hz f)+z • A (balancedResponse F z hz f):=by
  simpa only [balancedResponse] using word_source F z hz A (balancedCompressionForce F (resolventCore F z hz f))

def balancedWholeForceState(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  ∑i:Fin 2,wholeClockWord s hs half advanced m ell F g x i
    (balancedResponse F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (coreEquiv.symm (inputSeed g i)))
def balancedWholeForceEscape(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  ∑i:Fin 2,wordPhysicalEscape F (wholeClockWord s hs half advanced m ell F g x i)
    (balancedResponse F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (coreEquiv.symm (inputSeed g i)))
def balancedWholeForceOuter(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  ∑i:Fin 2,bracket (balancedCompressionForce F) (wholeClockWord s hs half advanced m ell F g x i)
    (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (coreEquiv.symm (inputSeed g i)))
def balancedWholeForceSource(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q)-
    balancedWholeForceOuter s hs half advanced m ell F g x q+balancedWholeForceEscape s hs half advanced m ell F g x q

/-- The complete force response generates its own H0 forcing on the unchanged whole source. -/
theorem actual_balanced_whole_force_full_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    H0 (balancedWholeForceState s hs half advanced m ell F g x q)=
      balancedWholeForceSource s hs half advanced m ell F g x q+
        actualFrequency advanced (sourceNoetherFrequency half) q • balancedWholeForceState s hs half advanced m ell F g x q:=by
  have h:=congrArg (fun v:Fin 2→QuantumTest=>∑i,v i) (funext (fun i=>
    word_force_source F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (wholeClockWord s hs half advanced m ell F g x i) (coreEquiv.symm (inputSeed g i))))
  simp only [←map_sum,Finset.sum_add_distrib,←Finset.smul_sum] at h
  have he:balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q)-
      balancedWholeForceOuter s hs half advanced m ell F g x q=
        ∑i:Fin 2,wholeClockWord s hs half advanced m ell F g x i
          (balancedCompressionForce F (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q)
            (hz half advanced q) (coreEquiv.symm (inputSeed g i)))):=by
    rw [whole_two_seed s hs half advanced m ell F g x q]
    simp only [balancedWholeForceOuter,map_sum,bracket,LinearMap.sub_apply,Module.End.mul_apply,Finset.sum_sub_distrib]
    module
  change H0 (balancedWholeForceState s hs half advanced m ell F g x q)=
    (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q)-
      balancedWholeForceOuter s hs half advanced m ell F g x q)+balancedWholeForceEscape s hs half advanced m ell F g x q+
      actualFrequency advanced (sourceNoetherFrequency half) q • balancedWholeForceState s hs half advanced m ell F g x q
  rw [he]
  exact h

def balancedWholeForceNativeDebit(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let w:=wholeClockState s hs half advanced m ell F g x q
  let v:=balancedWholeForceState s hs half advanced m ell F g x q
  let f:=(clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2;
  -9*(sourcePair w (SourceScalarOscillatorAbsorption.scalarCurrent w)).im-
    168*(sourcePair w (U (scalarSpatialDivergence w))).im+
      (sourcePair w (balancedProjectionCurrent F w)).im/2-
      (sourcePair (balancedWholeForceOuter s hs half advanced m ell F g x q) (B w)).im+
      (sourcePair (balancedWholeForceEscape s hs half advanced m ell F g x q) (B w)).im-
      (sourcePair (B v) f).im-(sourcePair v (bracket H0 B w)).im

/-- The original whole force-B price is a signed native/scalar projection-current debit with its complete physical forcing. No force norm or fiber energy is assumed. -/
theorem actual_balanced_whole_force_native_noether(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    2*(actualFrequency advanced (sourceNoetherFrequency half) q).im*
      (sourcePair (balancedWholeForceState s hs half advanced m ell F g x q)
        (B (wholeClockState s hs half advanced m ell F g x q))).re=
      balancedWholeForceNativeDebit s hs half advanced m ell F g x q:=by
  have hw:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  have hv:=actual_balanced_whole_force_full_source s hs half advanced m ell F g x q
  have hw':H0 (wholeClockState s hs half advanced m ell F g x q)=
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2+
        actualFrequency advanced (sourceNoetherFrequency half) q • wholeClockState s hs half advanced m ell F g x q:=by
    simpa only [wholeClockState] using hw
  have h:=actual_full_source_mixed_scalar_noether _ _ _ _ _ hw' hv
  rw [balancedWholeForceSource] at h
  have hpair(a b c:QuantumTest):sourcePair (a-b+c) (B (wholeClockState s hs half advanced m ell F g x q))=
    sourcePair a (B (wholeClockState s hs half advanced m ell F g x q))-
      sourcePair b (B (wholeClockState s hs half advanced m ell F g x q))+
      sourcePair c (B (wholeClockState s hs half advanced m ell F g x q)):=by
    simp only [sourcePair,map_add,map_sub,inner_add_left,inner_sub_left]
  rw [hpair,Complex.add_im,Complex.sub_im,balanced_force_scalar_price] at h
  exact h

/-- The virtual source is exactly the force component already present in the original frequency Ward. -/
theorem actual_balanced_whole_force_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    balancedWholeForceState s hs half advanced m ell F g x q=
      correctedCompleteCore s hs x.1 x.2 (wholeSourceMap s hs half advanced m ell F g
        (balancedForceInput m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)):=by
  simp only [balancedWholeForceState,balancedForceInput,balancedResponse,wholeClockWord,map_sum,Module.End.mul_apply]
end LowEnergy.ReverseBalancedForcePayer
