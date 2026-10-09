import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPhasePhysicalForcingCancellation
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointInputScalarPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.PhaseCompressionCancellation
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockYukawaCubicCurrent SourceScalarPairedTransport SourceScalarDoubleCurrent SourceClockPhiCombinedScalePressure
open SourceClockPhiNormalizedScalarBudget SourceClockPhiNativeJointPayment SourcePhysicalKineticSquare
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource ReverseScalarGaugeWard ReverseForceNoetherPayer ReverseBalancedForcePayer
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget
open ClockPhiHeatCorrectedCovarianceSource ScalarInputJointNoether JointElectricSource
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev Zbar:End:=reverseNativeClock-(9:ℂ) • SourceGaugeScaleTransport.generator
private abbrev A:End:=gaugeBalancedNativeForce
attribute [local irreducible] diagonalAction resolventCore coreEquiv phaseRow inputSeed balancedInputSeed normalizedState normalizedForcing
  balancedInputVector balancedForceInput compressionCore defectAction balancedCompressionForce wholeClockState wholeClockWord
  wholeSourceNext wholeSourceMap correctedCompleteCore sourcePair embed balancedInputForcing gaugeBalancedNativeForce
  reverseNativeClock SourceGaugeScaleTransport.generator reverseInputVector gaugeInputVector

def phaseStateFrequencySource(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  ∑i:Fin 2,phaseRow m ell i (resolventCore F z hz (resolventCore F z hz (coreEquiv.symm (inputSeed g i))))
def phaseForcingFrequencySource(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  ∑i:Fin 2,wordPhysicalEscape F (phaseRow m ell i)
    (resolventCore F z hz (resolventCore F z hz (coreEquiv.symm (inputSeed g i))))
attribute [local irreducible] phaseStateFrequencySource phaseForcingFrequencySource
private theorem input_rows(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    balancedInputVector m ell F z hz g=∑i:Fin 2,
      (bracket Zbar (phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
        phaseRow m ell i (resolventCore F z hz (Zbar (coreEquiv.symm (inputSeed g i))))):=by
  have he:=congrArg (fun v:QuantumTest=>v-(9:ℂ) • gaugeInputVector m ell F z hz g)
    (actual_reverse_input_vector m ell F z hz g).symm
  unfold balancedInputVector
  refine he.trans ?_
  simp only [gaugeInputVector,Finset.smul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl;intro i _
  simp only [Zbar,bracket,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_smul]
  module
private theorem balanced_resolvent(F:Index)(z:ℂ)(hz:z.im≠0):
    let R:End:=resolventCore F z hz
    bracket Zbar R+(18:ℂ) • (R+z • (R*R))= -R*balancedCompressionForce F*R:=by
  dsimp only
  have hr:=actual_reverse_resolvent_ward F z hz
  have hg:=actual_gauge_resolvent_ward F z hz
  dsimp only at hr
  unfold bracket at hr hg
  unfold Zbar balancedCompressionForce bracket
  linear_combination (norm:=(noncomm_ring;module)) hr-(9:ℂ) • hg

private theorem input_force_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    balancedInputVector m ell F z hz g-balancedForceInput m ell F z hz g=
      Zbar (normalizedState m ell F z hz g)+(18:ℂ) •
        (normalizedState m ell F z hz g+z • phaseStateFrequencySource m ell F z hz g):=by
  have h(i:Fin 2):bracket Zbar (phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
      phaseRow m ell i (resolventCore F z hz (Zbar (coreEquiv.symm (inputSeed g i))))-
      phaseRow m ell i (resolventCore F z hz (balancedCompressionForce F
        (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))))=
      Zbar (phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (inputSeed g i))))+
      (18:ℂ) • (phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
        z • phaseRow m ell i (resolventCore F z hz (resolventCore F z hz (coreEquiv.symm (inputSeed g i))))):=by
    have hw:=congrArg (phaseRow m ell i) (LinearMap.congr_fun (balanced_resolvent F z hz) (coreEquiv.symm (inputSeed g i)))
    simp only [bracket,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.neg_apply,
      Module.End.mul_apply,map_add,map_sub,map_smul,map_neg] at hw ⊢
    linear_combination (norm:=module) -hw
  rw [input_rows]
  unfold balancedForceInput
  rw [←Finset.sum_sub_distrib]
  simp_rw [h]
  simp only [Finset.sum_add_distrib,←Finset.smul_sum,←map_sum,←actual_original_phase_state]
  unfold phaseStateFrequencySource
  rfl
private theorem word_source(F:Index)(z:ℂ)(hz:z.im≠0)(L:End)(f:QuantumTest):
    H0 (L (resolventCore F z hz f))=
      L f+wordPhysicalEscape F L (resolventCore F z hz f)+z • L (resolventCore F z hz f):=by
  have h:=(actual_force_response_full_noether F z hz f).1
  simp only [wordPhysicalEscape,bracket,LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,h,map_add,map_smul]
  module
private theorem frequency_full_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    H0 (phaseStateFrequencySource m ell F z hz g)=normalizedState m ell F z hz g+
      phaseForcingFrequencySource m ell F z hz g+z • phaseStateFrequencySource m ell F z hz g:=by
  have h(i:Fin 2):=word_source F z hz (phaseRow m ell i)
    (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))
  unfold phaseStateFrequencySource phaseForcingFrequencySource
  simp only [map_sum]
  simp_rw [h]
  simp only [Finset.sum_add_distrib,←Finset.smul_sum,←actual_original_phase_state]
private theorem full_scale:bracket Zbar H0=(18:ℂ) • H0+A:=by
  have h:=actual_reverse_full_hamiltonian_scale
  unfold bracket at h
  unfold Zbar A gaugeBalancedNativeForce bracket
  linear_combination (norm:=(noncomm_ring;module)) h

/-- Input and force share both RF legs. Their complete H0-forcing difference cancels all own-defect terms jointly; the residual is the original balanced native force and the physical-frequency forcing source. -/
theorem actual_input_force_source_cancellation(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    balancedInputForcing m ell F z hz g 1-
      (H0 (balancedForceInput m ell F z hz g)-z • balancedForceInput m ell F z hz g)=
        Zbar (normalizedForcing m ell F z hz g)+(18:ℂ) • (z • phaseForcingFrequencySource m ell F z hz g)-
          A (normalizedState m ell F z hz g):=by
  let w:=normalizedState m ell F z hz g
  let f:=normalizedForcing m ell F z hz g
  let d:=phaseStateFrequencySource m ell F z hz g
  let e:=phaseForcingFrequencySource m ell F z hz g
  have hw:H0 w=f+z • w:=actual_full_normalized_source m ell F z hz g
  have hd:H0 d=w+e+z • d:=frequency_full_source m ell F z hz g
  have hZ:H0 (Zbar w)=Zbar f+z • Zbar w-(18:ℂ) • (f+z • w)-A w:=by
    have h:=LinearMap.congr_fun full_scale w
    simp only [bracket,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,hw,map_add,map_smul] at h
    simp only [Zbar,LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul] at h ⊢
    linear_combination (norm:=module) -h
  have hb:=actual_balanced_input_full_source m ell F z hz g 1
  simp only [Module.End.one_apply] at hb
  have hs:=input_force_return m ell F z hz g
  have hc:=congrArg H0 hs
  simp only [map_sub,map_add,map_smul] at hc
  change H0 (balancedInputVector m ell F z hz g)-H0 (balancedForceInput m ell F z hz g)=
    H0 (Zbar w)+(18:ℂ) • (H0 w+z • H0 d) at hc
  rw [hZ,hw,hd] at hc
  linear_combination (norm:=module) hc-hb-z • hs

private theorem source_transport(H T:End)(z:ℂ)(b v f₀ fT c:QuantumTest)
    (h₀:H b=f₀+z • b)(hT:H (T b)=fT+z • T b)(hc:f₀-(H v-z • v)=c):
    fT-(H (T v)-z • T v)=T c+bracket H T (b-v):=by
  have h:=congrArg T hc
  have ht:=congrArg T h₀
  simp only [map_sub,map_add,map_smul] at h ht
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  linear_combination (norm:=module) h-hT+ht

/-- The actual clock/electric word keeps its full Hamiltonian commutator in the same joint forcing difference. -/
theorem actual_word_input_force_source_cancellation(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(T:End):
    balancedInputForcing m ell F z hz g T-
      (H0 (T (balancedForceInput m ell F z hz g))-z • T (balancedForceInput m ell F z hz g))=
        T (Zbar (normalizedForcing m ell F z hz g)+(18:ℂ) • (z • phaseForcingFrequencySource m ell F z hz g)-
          A (normalizedState m ell F z hz g))+
        bracket H0 T (balancedInputVector m ell F z hz g-balancedForceInput m ell F z hz g):=by
  have h₀:=actual_balanced_input_full_source m ell F z hz g 1
  simp only [Module.End.one_apply] at h₀
  exact source_transport H0 T z _ _ _ _ _ h₀
    (actual_balanced_input_full_source m ell F z hz g T)
    (actual_input_force_source_cancellation m ell F z hz g)

/-- This is the physical-frequency derivative of the original complete forcing on both causes, generated with the same two RF legs. -/
theorem actual_phase_forcing_frequency_source(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    HasDerivAt (fun r:ℝ=>embed (normalizedForcing m ell F (actualFrequency advanced μ r)
      (reverse_frequency_nonreal advanced μ hμ r) g))
      (embed (phaseForcingFrequencySource m ell F (actualFrequency advanced μ q)
        (reverse_frequency_nonreal advanced μ hμ q) g)) q:=by
  have h:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset (Fin 2))) (fun i _=>
    actual_physical_resolvent_derivative F advanced μ hμ (wordPhysicalEscape F (phaseRow m ell i))
      (coreEquiv.symm (inputSeed g i)) q)
  simpa only [actual_original_phase_forcing,phaseForcingFrequencySource,map_sum] using! h
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private abbrev hz(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q
private theorem whole_force_state_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    balancedWholeForceState s hs half advanced m ell F g x q=
      wholeInputWord s hs half advanced m ell F g x
        (balancedForceInput m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g):=by
  simp only [balancedWholeForceState,balancedForceInput,balancedResponse,wholeClockWord,wholeInputWord,
    map_sum,Module.End.mul_apply]

/-- The actual whole input and full compressed-force response share one physical forcing difference. All cutoff terms cancel inside it; the complete clock/electric H0 commutator survives. -/
theorem actual_whole_input_force_source_cancellation(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    wholeInputForcing s hs half advanced m ell F g x q-balancedWholeForceSource s hs half advanced m ell F g x q=
      wholeInputWord s hs half advanced m ell F g x
        (Zbar (normalizedForcing m ell F z (hz half advanced q) g)+
          (18:ℂ) • (z • phaseForcingFrequencySource m ell F z (hz half advanced q) g)-
          A (normalizedState m ell F z (hz half advanced q) g))+
      bracket H0 (wholeInputWord s hs half advanced m ell F g x)
        (balancedInputVector m ell F z (hz half advanced q) g-balancedForceInput m ell F z (hz half advanced q) g):=by
  dsimp only
  have h:=actual_word_input_force_source_cancellation m ell F
    (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g
    (wholeInputWord s hs half advanced m ell F g x)
  have hv:=actual_balanced_whole_force_full_source s hs half advanced m ell F g x q
  rw [whole_force_state_return] at hv
  unfold wholeInputForcing
  linear_combination (norm:=module) h+hv
end LowEnergy.PhaseCompressionCancellation
