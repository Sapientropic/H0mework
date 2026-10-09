import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeForceNoetherDebit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseForcePhysicalPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open FullYSourceResolventGraphSplice FinitePhysicalSource SourceClockPhiNativeJointPayment SourceInverseNoetherChannelGap SourceScalarPairedTransport
open SourceClockYukawaCubicCurrent SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget SourceScalarSpatialCurrent
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiWholeSignedWorkIntegrable SourceScalarInverseNativeEnergy SourceJointResidualEnergy SourceBulkTwoTime
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource ReverseForceNoetherPayer ScalarCausalFrequencyMoment
open ClockPhiHeatCorrectedCovarianceSource MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev B:End:=scalarBulkComplete
private abbrev Z:End:=reverseNativeClock
private abbrev H0:End:=diagonalAction
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction compressionCore resolventCore
  reverseNativeClock reverseScaleForce reverseCompressionForce scalarBulkComplete
  normalizedState normalizedForcing wholeClockState wholeSourceNext wholeSourceMap correctedCompleteCore weightedElectricCurrent
  forceResponse phaseRow inputSeed wholeClockWord wholeForceState wholeForceNativeDebit
  reverseScalarCurrent reverseScalarReserve reverseNoetherFactor reverseNoetherNormCost scalarNoetherFactor scalarEnergy geometricScalarCurrent clockSourcePair
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<n:=by rw [show n=sourceTime 0 from rfl,source_time_generated];exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private abbrev hz(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q
private theorem whole_state_map(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeClockState s hs half advanced m ell F g x q=
      correctedCompleteCore s hs x.1 x.2 (wholeSourceMap s hs half advanced m ell F g
        (frequencyState half advanced m ell F g q)):=by
  simp only [wholeClockState,clockSourcePair,wholeSourceNext,wholeSourceMap,electricSourceDirection,
    Prod.fst_add,Prod.smul_fst,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply]
theorem actual_whole_state_pair_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(L R:End):
    Integrable (fun q:ℝ=>sourcePair (L (wholeClockState s hs half advanced m ell F g x q))
      (R (wholeClockState s hs half advanced m ell F g x q))):=by
  have hi:=actual_normalized_pair_integrable _ (frequency_positive half) advanced m ell F g
    (L*correctedCompleteCore s hs x.1 x.2*wholeSourceMap s hs half advanced m ell F g)
    (R*correctedCompleteCore s hs x.1 x.2*wholeSourceMap s hs half advanced m ell F g)
  simpa only [whole_state_map,frequencyState,Module.End.mul_apply] using hi
theorem actual_whole_state_square_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(L:End):
    Integrable (fun q:ℝ=>‖embed (L (wholeClockState s hs half advanced m ell F g x q))‖^2):=by
  have hi:=(actual_whole_state_pair_integrable s hs half advanced m ell F g x L L).re
  simpa only [sourcePair,RCLike.re_eq_complex_re,inner_self_eq_norm_sq] using hi
private theorem energy_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>scalarEnergy (wholeClockState s hs half advanced m ell F g x q)):=by
  simpa only [Module.End.one_apply,RCLike.re_eq_complex_re,original_scalar_energy] using (actual_whole_state_pair_integrable s hs half advanced m ell F g x 1 B).re
private theorem reserve_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>reverseScalarReserve (wholeClockState s hs half advanced m ell F g x q)):=by
  have hc:Integrable (fun q:ℝ=>reverseScalarCurrent (wholeClockState s hs half advanced m ell F g x q)):=by
    simpa only [reverseScalarCurrent,Module.End.one_apply,RCLike.re_eq_complex_re] using (actual_whole_state_pair_integrable s hs half advanced m ell F g x 1 (bracket Z B)).re
  have hn:Integrable (fun q:ℝ=>‖embed (wholeClockState s hs half advanced m ell F g x q)‖^2):=by
    simpa only [Module.End.one_apply] using actual_whole_state_square_integrable s hs half advanced m ell F g x 1
  exact ((hc.sub ((energy_integrable s hs half advanced m ell F g x).const_mul 3)).add
    (hn.const_mul (6*n*‖vacuum‖^2))).congr (Eventually.of_forall (fun q=>by
      dsimp only [Pi.add_apply,Pi.sub_apply]
      linarith only [actual_reverse_clock_scalar_form (wholeClockState s hs half advanced m ell F g x q)]))

def wholeNonForceSource(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  ∑i:Fin 2,(bracket Z (wholeClockWord s hs half advanced m ell F g x i)
    (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
      (coreEquiv.symm (inputSeed g i)))+
    wholeClockWord s hs half advanced m ell F g x i
      (resolventCore F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
        (Z (coreEquiv.symm (inputSeed g i)))))
def wholeForceCausalPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  18*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)-
    2*(sourcePair (wholeNonForceSource s hs half advanced m ell F g x q)
      (B (wholeClockState s hs half advanced m ell F g x q))).re+
    wholeForceNativeDebit s hs half advanced m ell F g x q/(actualFrequency advanced (sourceNoetherFrequency half) q).im
private theorem force_causal_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeNoetherCausalPrice s hs half advanced m ell F g x q=wholeForceCausalPrice s hs half advanced m ell F g x q:=by
  have hspl:wholeReverseSource s hs half advanced m ell F g x q=
      wholeNonForceSource s hs half advanced m ell F g x q-wholeForceState s hs half advanced m ell F g x q:=by
    simp only [wholeReverseSource,wholeNonForceSource,wholeForceState,forceResponse,Finset.sum_sub_distrib]
  have hp:=actual_whole_force_native_noether s hs half advanced m ell F g x q
  have hd:wholeForceNativeDebit s hs half advanced m ell F g x q/(actualFrequency advanced (sourceNoetherFrequency half) q).im=
      2*(sourcePair (wholeForceState s hs half advanced m ell F g x q) (B (wholeClockState s hs half advanced m ell F g x q))).re:=by
    rw [←hp]
    field_simp [hz half advanced q]
  unfold wholeNoetherCausalPrice wholeForceCausalPrice
  rw [hspl,hd]
  simp only [sourcePair,map_sub,inner_sub_left,Complex.sub_re]
  ring

/-- The original finite Noether work consumes the native force current with both actual response legs. The source pole is nonzero before either causal branch is selected; no force price is assumed. -/
theorem actual_whole_force_noether_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(h:ℝ)(hh:0<h):
    let W:=fun q:ℝ=>let z:=actualFrequency advanced (sourceNoetherFrequency half) q
      let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
      reverseScalarNoetherWork h z a.1 a.2
    Integrable W ∧ Integrable (wholeForceCausalPrice s hs half advanced m ell F g x) ∧
      (∫q:ℝ,W q) ≤ ∫q:ℝ,wholeForceCausalPrice s hs half advanced m ell F g x q:=by
  have hp:=actual_whole_noether_causal_price s hs half advanced m ell F g x h hh
  have he:wholeNoetherCausalPrice s hs half advanced m ell F g x=wholeForceCausalPrice s hs half advanced m ell F g x:=
    funext (force_causal_return s hs half advanced m ell F g x)
  simpa only [he] using hp

def wholeScalarForcingPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
  scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
    ((sourcePair a.2 (B a.1)).im-(sourcePair a.1 (geometricScalarCurrent a.1)).im/2)
def wholeScalarForceUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  reverseNoetherFactor half*(wholeForceCausalPrice s hs half advanced m ell F g x q-
    reverseScalarReserve (wholeClockState s hs half advanced m ell F g x q))+
    reverseNoetherNormCost half*‖embed (wholeClockState s hs half advanced m ell F g x q)‖^2
private theorem scalar_source(z:ℂ)(w f:QuantumTest)(he:H0 w=f+z • w):
    (sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2=
      z.im*scalarEnergy w+(sourcePair w (scalarCurrentComplete w)).im/2:=by
  have h:=actual_full_source_mixed_scalar_noether z w f w f he he
  have hc:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B w))
  simp only [Complex.conj_im] at hc
  have heq:bracket H0 B=scalarCurrentComplete+geometricScalarCurrent:=original_scalar_current_geometric
  rw [heq,original_scalar_energy] at h
  have hadd(a b c:QuantumTest):sourcePair a (b+c)=sourcePair a b+sourcePair a c:=by simp only [sourcePair,map_add,inner_add_right]
  simp only [LinearMap.add_apply,hadd,Complex.add_im] at h
  change -(sourcePair f (B w)).im=(sourcePair (B w) f).im at hc
  change 2*z.im*scalarEnergy w=(sourcePair f (B w)).im-(sourcePair (B w) f).im-
    ((sourcePair w (scalarCurrentComplete w)).im+(sourcePair w (geometricScalarCurrent w)).im) at h
  linarith only [h,hc]
private theorem scalar_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (wholeScalarForcingPrice s hs half advanced m ell F g x):=by
  have he:wholeScalarForcingPrice s hs half advanced m ell F g x=fun q:ℝ=>
      scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
        ((if advanced then -sourceNoetherFrequency half else sourceNoetherFrequency half)*
          scalarEnergy (wholeClockState s hs half advanced m ell F g x q)+
          (sourcePair (wholeClockState s hs half advanced m ell F g x q)
            (scalarCurrentComplete (wholeClockState s hs half advanced m ell F g x q))).im/2):=by
    funext q
    have hh:=scalar_source _ _ _ (((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
    dsimp only [wholeScalarForcingPrice]
    rw [hh]
    cases advanced <;> simp only [wholeClockState,actualFrequency,Bool.false_eq_true,ite_false,ite_true,Complex.star_def,Complex.conj_im,line_im]
  rw [he]
  have hi:Integrable (fun q:ℝ=>(sourcePair (wholeClockState s hs half advanced m ell F g x q)
      (scalarCurrentComplete (wholeClockState s hs half advanced m ell F g x q))).im):=by
    simpa only [Module.End.one_apply,RCLike.im_eq_complex_im] using (actual_whole_state_pair_integrable s hs half advanced m ell F g x 1 scalarCurrentComplete).im
  exact (((energy_integrable s hs half advanced m ell F g x).const_mul _).add (hi.div_const 2)).const_mul _

/-- The original kappa-scalar full-forcing price is paid by the complete force/current source upper. Both native reserves survive in the output; no endpoint or frequency budget is a premise. -/
theorem actual_whole_scalar_force_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (wholeScalarForcingPrice s hs half advanced m ell F g x) ∧
    Integrable (wholeScalarForceUpper s hs half advanced m ell F g x) ∧
    (∫q:ℝ,wholeScalarForcingPrice s hs half advanced m ell F g x q) ≤
      ∫q:ℝ,wholeScalarForceUpper s hs half advanced m ell F g x q:=by
  let W:=fun q:ℝ=>let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
    reverseScalarNoetherWork 1 z a.1 a.2
  let R:=fun q:ℝ=>reverseScalarReserve (wholeClockState s hs half advanced m ell F g x q)
  let N:=fun q:ℝ=>reverseNoetherNormCost half*‖embed (wholeClockState s hs half advanced m ell F g x q)‖^2
  let a:=reverseNoetherFactor half
  have hW:=actual_whole_force_noether_payment s hs half advanced m ell F g x 1 (by norm_num)
  have hR:Integrable R:=reserve_integrable s hs half advanced m ell F g x
  have hN:Integrable N:=by
    have hn:=actual_whole_state_square_integrable s hs half advanced m ell F g x 1
    simpa only [N,Module.End.one_apply] using hn.const_mul (reverseNoetherNormCost half)
  have hJ:=scalar_integrable s hs half advanced m ell F g x
  have hT:Integrable (fun q:ℝ=>a*(W q-R q)+N q):=((hW.1.sub hR).const_mul a).add hN
  have hU:Integrable (wholeScalarForceUpper s hs half advanced m ell F g x):=((hW.2.1.sub hR).const_mul a).add hN
  have hpt(q:ℝ):wholeScalarForcingPrice s hs half advanced m ell F g x q ≤ a*(W q-R q)+N q:=by
    have he:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
    have hp:=actual_full_source_scalar_reverse_payment half advanced q _ _ he
    have hw:=(actual_reverse_scalar_noether_work 1 (by norm_num) _ (hz half advanced q) _ _ he).2
    dsimp only [wholeScalarForcingPrice,W,R,N,a,wholeClockState]
    rw [hw]
    simpa only [wholeClockState] using hp
  have ha:0 ≤ a:=by
    unfold a reverseNoetherFactor
    have hk:0<scalarNoetherFactor half:=(actual_scalar_noether_fraction half).1
    have hn:0<n:=by rw [show n=sourceTime 0 from rfl,source_time_generated];exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
    have hμ:=frequency_positive half
    positivity
  refine ⟨hJ,hU,(integral_mono hJ hT hpt).trans ?_⟩
  change (∫q:ℝ,a*(W q-R q)+N q) ≤ ∫q:ℝ,a*(wholeForceCausalPrice s hs half advanced m ell F g x q-R q)+N q
  have hint(T:ℝ→ℝ)(hT:Integrable T):
      (∫q:ℝ,a*(T q-R q)+N q)=a*((∫q:ℝ,T q)-(∫q:ℝ,R q))+(∫q:ℝ,N q):=by
    erw [integral_add ((hT.sub hR).const_mul a) hN]
    simp only [Pi.sub_apply]
    rw [integral_const_mul,integral_sub hT hR]
  rw [hint W hW.1,hint _ hW.2.1]
  have hb:=mul_le_mul_of_nonneg_left (sub_le_sub_right hW.2.2 (∫q:ℝ,R q)) ha
  linarith only [hb]
end LowEnergy.ReverseForcePhysicalPayment
