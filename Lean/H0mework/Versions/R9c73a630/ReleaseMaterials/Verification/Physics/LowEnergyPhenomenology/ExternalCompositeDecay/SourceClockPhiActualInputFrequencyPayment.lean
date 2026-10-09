import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFixedSourceFrequencyPair
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiInputForceJointCancellation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.InputForceFrequencyPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockYukawaCubicCurrent SourceScalarPairedTransport SourceScalarDoubleCurrent SourceClockPhiCombinedScalePressure
open SourceClockPhiNormalizedScalarBudget SourceClockPhiNativeJointPayment SourcePhysicalKineticSquare
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource ReverseScalarGaugeWard ReverseForceNoetherPayer ReverseBalancedForcePayer
open ScalarInputJointNoether PhaseCompressionCancellation SourceInverseNoetherChannelGap SourceJointResidualEnergy FinitePhysicalSource
open MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev Zbar:End:=reverseNativeClock-(9:ℂ) • SourceGaugeScaleTransport.generator
private abbrev originalColumn (m ell:ℕ)(F:Index)(g:diagonal.domain):Channel F→QuantumTest:=sourceColumn 1 m ell F g
private abbrev freq(advanced:Bool)(μ q:ℝ):ℂ:=actualFrequency advanced μ q
private abbrev hz(advanced:Bool)(μ:ℝ)(hμ:0<μ)(q:ℝ):(freq advanced μ q).im≠0:=reverse_frequency_nonreal advanced μ hμ q
attribute [local irreducible] diagonalAction resolventCore coreEquiv phaseRow inputSeed balancedInputSeed normalizedState normalizedForcing
  balancedInputVector balancedForceInput compressionCore defectAction balancedCompressionForce sourceColumn sourceDrift
  reverseNativeClock SourceGaugeScaleTransport.generator reverseInputVector gaugeInputVector sourcePair embed phaseStateFrequencySource phaseForcingFrequencySource
private theorem core_channels(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    resolventCore F z hz (coreEquiv.symm g)=∑j:Channel F,((channelValue F j:ℂ)-z)⁻¹ • channelTest F g j:=by
  have h:resolventCore F z hz (coreEquiv.symm g)=SourceScalarPositiveBulkWard.state F z hz g:=by
    simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
  rw [h,actual_state_channels]
private theorem state_channels(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    normalizedState m ell F (freq advanced μ q) (hz advanced μ hμ q) g=
      fixedSourceWave advanced μ (channelValue F) (originalColumn m ell F g) q:=by
  rw [actual_original_phase_state]
  simp_rw [core_channels,map_sum,map_smul]
  rw [Finset.sum_comm]
  simp only [fixedSourceWave,originalColumn,sourceColumn,Module.End.one_apply,Finset.smul_sum]
private theorem state_derivative_channels(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    phaseStateFrequencySource m ell F (freq advanced μ q) (hz advanced μ hμ q) g=
      fixedSourceDerivative advanced μ (channelValue F) (originalColumn m ell F g) q:=by
  have h:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset (Fin 2))) (fun i _=>
    actual_physical_resolvent_derivative F advanced μ hμ (phaseRow m ell i) (coreEquiv.symm (inputSeed g i)) q)
  have ha:HasDerivAt (fun r:ℝ=>embed (normalizedState m ell F (freq advanced μ r) (hz advanced μ hμ r) g))
      (embed (phaseStateFrequencySource m ell F (freq advanced μ q) (hz advanced μ hμ q) g)) q:=by
    simpa only [actual_original_phase_state,phaseStateFrequencySource,map_sum] using! h
  simp only [state_channels μ hμ advanced m ell F g] at ha
  exact embed_injective (ha.unique (actual_fixed_wave_derivative advanced μ hμ (channelValue F) (originalColumn m ell F g) q))
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

private theorem difference_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
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
private theorem shifted_pole(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):
    ((a:ℂ)-freq advanced μ q)⁻¹+freq advanced μ q*(((a:ℂ)-freq advanced μ q)⁻¹)^2=
      (a:ℂ)*(((a:ℂ)-freq advanced μ q)⁻¹)^2:=by
  have hn:(a:ℂ)-freq advanced μ q≠0:=by
    intro he
    apply hz advanced μ hμ q
    rw [←sub_eq_zero.mp he]
    rfl
  field_simp [hn]
  ring

/-- The same input-minus-force response has only its original single and double poles. The coefficients are generated by Zbar on the original zero-source columns. -/
theorem actual_input_force_difference_channels(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(T:End)(q:ℝ):
    T (balancedInputVector m ell F (freq advanced μ q) (hz advanced μ hμ q) g-
      balancedForceInput m ell F (freq advanced μ q) (hz advanced μ hμ q) g)=
        fixedSourceWave advanced μ (channelValue F) (fun j=>T (Zbar (originalColumn m ell F g j))) q+
        fixedSourceDerivative advanced μ (channelValue F) (fun j=>(18*(channelValue F j:ℂ)) • T (originalColumn m ell F g j)) q:=by
  rw [difference_return,state_channels μ hμ advanced m ell F g,state_derivative_channels μ hμ advanced m ell F g]
  simp only [fixedSourceWave,fixedSourceDerivative,map_add,map_smul,map_sum,Finset.smul_sum,←Finset.sum_add_distrib,smul_smul]
  apply Finset.sum_congr rfl;intro j _
  have h:=shifted_pole advanced μ hμ (channelValue F j) q
  have he:=congrArg (fun c:ℂ=>(18*c) • T (originalColumn m ell F g j)) h
  simp only [add_smul,mul_smul] at he
  linear_combination (norm:=module) he
private theorem joint_channels(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L R:End)(q:ℝ):
    L (normalizedState m ell F (freq advanced μ q) (hz advanced μ hμ q) g)+
      R (balancedInputVector m ell F (freq advanced μ q) (hz advanced μ hμ q) g-
        balancedForceInput m ell F (freq advanced μ q) (hz advanced μ hμ q) g)=
      fixedSourceWave advanced μ (channelValue F) (fun j=>L (originalColumn m ell F g j)+R (Zbar (originalColumn m ell F g j))) q+
      fixedSourceDerivative advanced μ (channelValue F) (fun j=>(18*(channelValue F j:ℂ)) • R (originalColumn m ell F g j)) q:=by
  rw [actual_input_force_difference_channels μ hμ advanced m ell F g,state_channels μ hμ advanced m ell F g]
  simp only [fixedSourceWave,map_sum,map_smul,smul_add,Finset.sum_add_distrib]
  module

/-- Every joint original state/difference pair has ordinary whole-frequency L1, including the force/input loss and all QF/local cross terms. No common price is supplied. -/
theorem actual_input_force_joint_pair_integrable(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L R A B:End):
    Integrable (fun q:ℝ=>sourcePair
      (L (normalizedState m ell F (freq advanced μ q) (hz advanced μ hμ q) g)+
        R (balancedInputVector m ell F (freq advanced μ q) (hz advanced μ hμ q) g-
          balancedForceInput m ell F (freq advanced μ q) (hz advanced μ hμ q) g))
      (A (normalizedState m ell F (freq advanced μ q) (hz advanced μ hμ q) g)+
        B (balancedInputVector m ell F (freq advanced μ q) (hz advanced μ hμ q) g-
          balancedForceInput m ell F (freq advanced μ q) (hz advanced μ hμ q) g))):=by
  have h:=actual_fixed_jet_pair_integrable advanced μ hμ (channelValue F)
    (fun j=>L (originalColumn m ell F g j)+R (Zbar (originalColumn m ell F g j)))
    (fun j=>(18*(channelValue F j:ℂ)) • R (originalColumn m ell F g j))
    (fun j=>A (originalColumn m ell F g j)+B (Zbar (originalColumn m ell F g j)))
    (fun j=>(18*(channelValue F j:ℂ)) • B (originalColumn m ell F g j))
  exact h.congr (Eventually.of_forall (fun q=>by
    dsimp only
    rw [joint_channels μ hμ advanced m ell F g L R q,joint_channels μ hμ advanced m ell F g A B q]))
private theorem forcing_channels(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(T:End)(q:ℝ):
    T (normalizedForcing m ell F (freq advanced μ q) (hz advanced μ hμ q) g)=
      fixedSourceWave advanced μ (channelValue F) (fun j=>T (sourceDrift 1 m ell F g j)) q:=by
  rw [actual_original_phase_forcing]
  simp_rw [core_channels,map_sum,map_smul]
  rw [Finset.sum_comm]
  have hd(j:Channel F):sourceDrift 1 m ell F g j=
      ∑i:Fin 2,wordPhysicalEscape F (phaseRow m ell i) (channelTest F (inputSeed g i) j):=by
    rw [actual_source_drift_native]
    simp only [one_mul,Module.End.one_apply,wordPhysicalEscape,LinearMap.add_apply,Module.End.mul_apply]
  simp only [fixedSourceWave,hd,map_sum,Finset.smul_sum]
private theorem forcing_derivative_channels(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(T:End)(q:ℝ):
    T (phaseForcingFrequencySource m ell F (freq advanced μ q) (hz advanced μ hμ q) g)=
      fixedSourceDerivative advanced μ (channelValue F) (fun j=>T (sourceDrift 1 m ell F g j)) q:=by
  have h:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset (Fin 2))) (fun i _=>
    actual_physical_resolvent_derivative F advanced μ hμ (T*wordPhysicalEscape F (phaseRow m ell i))
      (coreEquiv.symm (inputSeed g i)) q)
  have ha:HasDerivAt (fun r:ℝ=>embed (T (normalizedForcing m ell F (freq advanced μ r) (hz advanced μ hμ r) g)))
      (embed (T (phaseForcingFrequencySource m ell F (freq advanced μ q) (hz advanced μ hμ q) g))) q:=by
    simpa only [actual_original_phase_forcing,phaseForcingFrequencySource,map_sum,Module.End.mul_apply] using! h
  simp only [forcing_channels μ hμ advanced m ell F g T] at ha
  exact embed_injective (ha.unique (actual_fixed_wave_derivative advanced μ hμ (channelValue F)
    (fun j=>T (sourceDrift 1 m ell F g j)) q))

def inputForceDifferenceDerivative(μ:ℝ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(T:End)(q:ℝ):QuantumTest:=
  fixedSourceDerivative advanced μ (channelValue F) (fun j=>T (Zbar (originalColumn m ell F g j))) q+
    fixedSourceSecondDerivative advanced μ (channelValue F)
      (fun j=>(18*(channelValue F j:ℂ)) • T (originalColumn m ell F g j)) q

/-- The original difference inherits its full physical-frequency derivative, including the double-pole source's third pole. T is fixed before frequency. -/
theorem actual_input_force_difference_derivative(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(T:End)(q:ℝ):
    HasDerivAt (fun r:ℝ=>embed (T (balancedInputVector m ell F (freq advanced μ r) (hz advanced μ hμ r) g-
      balancedForceInput m ell F (freq advanced μ r) (hz advanced μ hμ r) g)))
      (embed (inputForceDifferenceDerivative μ advanced m ell F g T q)) q:=by
  have h0:=actual_fixed_wave_derivative advanced μ hμ (channelValue F) (fun j=>T (Zbar (originalColumn m ell F g j))) q
  have h1:=actual_fixed_derivative_derivative advanced μ hμ (channelValue F)
    (fun j=>(18*(channelValue F j:ℂ)) • T (originalColumn m ell F g j)) q
  simpa only [actual_input_force_difference_channels μ hμ advanced m ell F g T,inputForceDifferenceDerivative,map_add] using! h0.add h1

/-- The actual full forcing and the same input-minus-force difference retain every ordered interference in paired frequency transport. No norm of zf is requested. -/
theorem actual_input_force_frequency_pair(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L R:End):
    let z:=freq advanced μ
    let f:=fun q=>L (normalizedForcing m ell F (z q) (hz advanced μ hμ q) g)
    let fprime:=fun q=>L (phaseForcingFrequencySource m ell F (z q) (hz advanced μ hμ q) g)
    let d:=fun q=>R (balancedInputVector m ell F (z q) (hz advanced μ hμ q) g-
      balancedForceInput m ell F (z q) (hz advanced μ hμ q) g)
    let dprime:=inputForceDifferenceDerivative μ advanced m ell F g R
    Integrable (fun q:ℝ=>sourcePair (f q) (d q)) ∧
    Integrable (fun q:ℝ=>sourcePair (z q • fprime q) (d q)) ∧
    Integrable (fun q:ℝ=>sourcePair (z q • f q) (dprime q)) ∧
    (∫q:ℝ,sourcePair (z q • fprime q) (d q))=
      -(∫q:ℝ,sourcePair (f q) (d q))-(∫q:ℝ,sourcePair (z q • f q) (dprime q)):=by
  dsimp only
  have h:=actual_fixed_jet_frequency_pair advanced μ hμ (channelValue F)
    (fun j=>L (sourceDrift 1 m ell F g j))
    (fun j=>R (Zbar (originalColumn m ell F g j)))
    (fun j=>(18*(channelValue F j:ℂ)) • R (originalColumn m ell F g j))
  simpa only [forcing_channels μ hμ advanced m ell F g L,forcing_derivative_channels μ hμ advanced m ell F g L,actual_input_force_difference_channels μ hμ advanced m ell F g R,inputForceDifferenceDerivative] using! h

private theorem pair_smul_left(c:ℂ)(u v:QuantumTest):sourcePair (c • u) v=star c*sourcePair u v:=by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]

/-- This is the signed 18z fprime word from the actual scalar Ward. The transported derivative remains on the complete original difference, for either cause and any frequency-independent source word. -/
theorem actual_input_force_signed_frequency_payment(μ:ℝ)(hμ:0<μ)(advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L R:End):
    let z:=freq advanced μ
    let f:=fun q=>L (normalizedForcing m ell F (z q) (hz advanced μ hμ q) g)
    let fprime:=fun q=>L (phaseForcingFrequencySource m ell F (z q) (hz advanced μ hμ q) g)
    let d:=fun q=>R (balancedInputVector m ell F (z q) (hz advanced μ hμ q) g-
      balancedForceInput m ell F (z q) (hz advanced μ hμ q) g)
    let dprime:=inputForceDifferenceDerivative μ advanced m ell F g R
    (∫q:ℝ,inputCausalSign advanced*(sourcePair ((18:ℂ) • (z q • fprime q)) (d q)).im)=
      -18*inputCausalSign advanced*(∫q:ℝ,(sourcePair (f q) (d q)).im)-
        18*inputCausalSign advanced*(∫q:ℝ,(sourcePair (z q • f q) (dprime q)).im):=by
  dsimp only
  have h:=actual_input_force_frequency_pair μ hμ advanced m ell F g L R
  dsimp only at h
  have h0:=integral_im h.1
  have h1:=integral_im h.2.1
  have h2:=integral_im h.2.2.1
  simp only [RCLike.im_eq_complex_im] at h0 h1 h2
  have he:=congrArg Complex.im h.2.2.2
  simp only [Complex.sub_im,Complex.neg_im] at he
  rw [←h0,←h1,←h2] at he
  have hp(u v:QuantumTest):(sourcePair ((18:ℂ) • u) v).im=18*(sourcePair u v).im:=by
    rw [pair_smul_left]
    norm_num [Complex.mul_im]
  simp only [hp]
  rw [integral_const_mul,integral_const_mul]
  linear_combination (norm:=ring) (18*inputCausalSign advanced)*he

end LowEnergy.InputForceFrequencyPayment
