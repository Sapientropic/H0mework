import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaugeElectricWardSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseScalarGaugeWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceScalarDoubleCurrent
open SourceClockPhiNormalizedScalarBudget SourceClockPhiNativeJointPayment SourceClockPhiCombinedScalePressure
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer FirstCurrentElectricSuccessor
open SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceScalarShiftedBulk SourceScalarEssentialBudget
open ClockPhiHeatCorrectedCovarianceSource ReverseNativeFrequencyWard ReverseNativeOuterSource ReverseGaugeOuterPayment
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev B:End:=scalarBulkComplete
private abbrev X:End:=weightedElectricCurrent
attribute [local irreducible] sourcePair embed scalarBulkComplete scalarEnergy correctedCompleteCore wholeStep wholeSourceMap
  wholeSourceNext frequencyState normalizedState normalizedForcing coreEquiv phiThetaAction phiInverseAction
  reverseInputVector reverseForceInput wholeOuterSource wholeOuterNoetherPrice wholeClockState resolventCore
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private abbrev Hz(half advanced:Bool)(q:ℝ):(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
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

def gaugeInputVector(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  ∑i:Fin 2,(bracket G (phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
    phaseRow m ell i (resolventCore F z hz (G (coreEquiv.symm (inputSeed g i)))))
def gaugeForceInput(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  ∑i:Fin 2,phaseRow m ell i (resolventCore F z hz (gaugeCompressionForce F
    (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))))
theorem actual_normalized_gauge_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    G (normalizedState m ell F z hz g)=gaugeInputVector m ell F z hz g-gaugeForceInput m ell F z hz g:=by
  rw [normalized_two_seed,map_sum]
  unfold gaugeInputVector gaugeForceInput
  rw [←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _=>actual_gauge_source_word F z hz (phaseRow m ell i) (coreEquiv.symm (inputSeed g i)))

def balancedInputVector(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  reverseInputVector m ell F z hz g-(9:ℂ) • gaugeInputVector m ell F z hz g
def balancedCompressionForce(F:Index):End:=reverseCompressionForce F-(9:ℂ) • gaugeCompressionForce F
def balancedForceInput(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  ∑i:Fin 2,phaseRow m ell i (resolventCore F z hz (balancedCompressionForce F
    (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))))
private theorem balanced_force_split(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    balancedForceInput m ell F z hz g=reverseForceInput m ell F z hz g-(9:ℂ) • gaugeForceInput m ell F z hz g:=by
  simp only [balancedForceInput,balancedCompressionForce,LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul,
    Finset.sum_sub_distrib,←Finset.smul_sum,reverseForceInput,gaugeForceInput]

/-- This is an auxiliary representative of the original scalar Ward pairing, not a replacement physical forcing. Both original response legs retain their full own-compression force. -/
def balancedWardWord(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):QuantumTest:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  (-36:ℂ) • ((wholeStep s hs half advanced m ell F g:ℂ) • X (frequencyState half advanced m ell F g q))+
    wholeSourceMap s hs half advanced m ell F g
      (balancedInputVector m ell F z (Hz half advanced q) g-balancedForceInput m ell F z (Hz half advanced q) g)
private theorem scalar_outer_electric(F:Index)(g:diagonal.domain):
    bracket ReverseNativeClock.reverseNativeClock X-(9:ℂ) • bracket G X=(-36:ℂ) • X:=by
  rw [actual_reverse_electric_outer_return F g,actual_gauge_electric_outer F g]
  module
private theorem gauge_map(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(w:QuantumTest):
    G (wholeSourceMap s hs half advanced m ell F g w)=
      (wholeStep s hs half advanced m ell F g:ℂ) • bracket G X w+
        wholeSourceMap s hs half advanced m ell F g (G w):=by
  unfold wholeSourceMap bracket
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.one_apply,Module.End.mul_apply,map_add,map_smul]
  module

/-- The complete gauge input and own-CF force cancel the entire electric gauge remainder inside the same scalar Ward word. -/
theorem actual_outer_gauge_word_difference(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    wholeOuterSource s hs half advanced m ell F g q-balancedWardWord s hs half advanced m ell F g q=
      (9:ℂ) • G ((wholeSourceNext s hs half advanced m ell F g q).1):=by
  have hw:(wholeSourceNext s hs half advanced m ell F g q).1=
      wholeSourceMap s hs half advanced m ell F g (frequencyState half advanced m ell F g q):=by
    unfold wholeSourceNext wholeSourceMap
    simp only [electricSourceDirection,Prod.fst_add,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply]
    rfl
  have hg:G (frequencyState half advanced m ell F g q)=
      gaugeInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q) g-
      gaugeForceInput m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (Hz half advanced q) g:=by
    unfold frequencyState
    exact actual_normalized_gauge_source m ell F _ _ g
  have hx:=LinearMap.congr_fun (scalar_outer_electric F g) (frequencyState half advanced m ell F g q)
  rw [hw,gauge_map]
  unfold wholeOuterSource balancedWardWord
  simp only [balancedInputVector,balanced_force_split,map_sub,map_smul,smul_add]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply] at hx
  rw [hg]
  simp only [map_sub]
  linear_combination (norm:=module) (wholeStep s hs half advanced m ell F g:ℂ) • hx

/-- Clock transport does not change the zero Gauge Ward: the complete scalar pairing is unchanged pointwise, including the original selected electric step. -/
theorem actual_clocked_scalar_ward_representative(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    (sourcePair (correctedCompleteCore s hs x.1 x.2 (wholeOuterSource s hs half advanced m ell F g q))
      (B (wholeClockState s hs half advanced m ell F g x q))).re=
    (sourcePair (correctedCompleteCore s hs x.1 x.2 (balancedWardWord s hs half advanced m ell F g q))
      (B (wholeClockState s hs half advanced m ell F g x q))).re:=by
  have hd:=congrArg (correctedCompleteCore s hs x.1 x.2) (actual_outer_gauge_word_difference s hs half advanced m ell F g q)
  have hg:=LinearMap.congr_fun (actual_complete_gauge_commute s hs x.1 x.2).eq
    ((wholeSourceNext s hs half advanced m ell F g q).1)
  have hu:correctedCompleteCore s hs x.1 x.2 ((wholeSourceNext s hs half advanced m ell F g q).1)=
      wholeClockState s hs half advanced m ell F g x q:=by unfold wholeClockState;rfl
  simp only [map_sub,map_smul] at hd
  change G (correctedCompleteCore s hs x.1 x.2 ((wholeSourceNext s hs half advanced m ell F g q).1))=
    correctedCompleteCore s hs x.1 x.2 (G ((wholeSourceNext s hs half advanced m ell F g q).1)) at hg
  rw [←hg,hu] at hd
  have hp:=congrArg (fun w:QuantumTest=>sourcePair w (B (wholeClockState s hs half advanced m ell F g x q))) hd
  have hr:=congrArg Complex.re hp
  simp only [sourcePair,map_sub,map_smul,inner_sub_left,inner_smul_left] at hr
  have hz:=actual_scalar_gauge_zero (wholeClockState s hs half advanced m ell F g x q)
  unfold sourcePair at hz ⊢
  norm_num [Complex.mul_re] at hr
  linarith

def balancedNoetherPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  18*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)-
    2*(sourcePair (correctedCompleteCore s hs x.1 x.2 (balancedWardWord s hs half advanced m ell F g q))
      (B (wholeClockState s hs half advanced m ell F g x q))).re
/-- The already-paid actual outer Noether price has a gauge-free electric word and the full compensated input/CF-force source, with exact equality rather than an added budget. -/
theorem actual_outer_noether_gauge_reduction(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeOuterNoetherPrice s hs half advanced m ell F g x q=balancedNoetherPrice s hs half advanced m ell F g x q:=by
  unfold wholeOuterNoetherPrice balancedNoetherPrice
  rw [actual_clocked_scalar_ward_representative]

/-- The compensation retains both actual own-defect commutators and the original full Hamiltonian. -/
theorem actual_balanced_compression_departments(F:Index):
    balancedCompressionForce F=ReverseNativeClock.reverseScaleForce-(9:ℂ) • bracket G diagonalAction+
      (18:ℂ) • SourceScalarPairedTransport.defectAction F-
        bracket (ReverseNativeClock.reverseNativeClock-(9:ℂ) • G) (SourceScalarPairedTransport.defectAction F):=by
  unfold balancedCompressionForce reverseCompressionForce gaugeCompressionForce SourceScalarPairedTransport.defectAction bracket
  noncomm_ring
  module

open ScalarCausalFrequencyMoment ReverseNativeClock
private theorem pair_add_left(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by
  simp only [sourcePair,map_add,inner_add_left]
def balancedFullNoetherPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  balancedNoetherPrice s hs half advanced m ell F g x q-2*(wholeClockWardKernel s hs half advanced m ell F g q x).re

/-- The complete causal Noether price is unchanged pointwise. Its clock word is still present; only a source-generated zero real Gauge Ward has been removed. -/
theorem actual_full_noether_gauge_reduction(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeNoetherCausalPrice s hs half advanced m ell F g x q=balancedFullNoetherPrice s hs half advanced m ell F g x q:=by
  unfold wholeNoetherCausalPrice balancedFullNoetherPrice balancedNoetherPrice
  rw [actual_whole_reverse_source_split]
  simp only [pair_add_left,Complex.add_re]
  rw [actual_clocked_scalar_ward_representative]
  have hc:sourcePair (bracket reverseNativeClock (correctedCompleteCore s hs x.1 x.2)
      ((wholeSourceNext s hs half advanced m ell F g q).1))
      (B (wholeClockState s hs half advanced m ell F g x q))=
      wholeClockWardKernel s hs half advanced m ell F g q x:=by
    unfold wholeClockWardKernel wholeClockState
    rfl
  rw [hc]
  ring
end LowEnergy.ReverseScalarGaugeWard
