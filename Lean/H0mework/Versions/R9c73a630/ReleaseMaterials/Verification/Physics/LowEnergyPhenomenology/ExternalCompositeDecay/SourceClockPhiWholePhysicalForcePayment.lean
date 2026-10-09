import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeForceScalarPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseForcePhysicalPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open FullYSourceResolventGraphSplice FinitePhysicalSource SourceClockPhiNativeJointPayment SourceInverseNoetherChannelGap SourceScalarPairedTransport
open SourceClockPhiNativeMatchedSource FirstCurrentDilationPrimitive GaussYukawaOperator
open SourceClockYukawaCubicCurrent SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare SourceClockReflectedForm SourceScalarVirialBulk
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget SourceScalarSpatialCurrent SourceScalarInverseNativeEnergy
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiWholeSignedWorkIntegrable SourceJointResidualEnergy SourceBulkTwoTime SourceFourPoleEnergyClosed
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource ReverseForceNoetherPayer OriginalRPrimitiveDifference OriginalRCommutatorSource
open ClockPhiHeatCorrectedCovarianceSource MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev M:End:=matchedTester
private abbrev H0:End:=diagonalAction
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction compressionCore resolventCore
  reverseNativeClock reverseScaleForce reverseCompressionForce scalarBulkComplete
  normalizedState normalizedForcing wholeClockState wholeSourceNext wholeSourceMap correctedCompleteCore weightedElectricCurrent
  forceResponse phaseRow inputSeed wholeClockWord wholeForceState wholeForceNativeDebit
  reverseScalarCurrent reverseScalarReserve reverseNoetherFactor reverseNoetherNormCost scalarNoetherFactor scalarEnergy geometricScalarCurrent clockSourcePair
  matchedTester nativeDilationWord combinedGenerator inverseVolumeAction originalNormalizerPrice
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<n:=by rw [show n=sourceTime 0 from rfl,source_time_generated];exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private abbrev hz(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q
private def P(advanced:Bool)(μ a q:ℝ):ℂ:=((a:ℂ)-actualFrequency advanced μ q)⁻¹
private theorem pole_pair_integrable(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Integrable (fun q:ℝ=>star (P advanced μ a q)*P advanced μ b q):=by
  cases advanced
  · simpa only [P,actualFrequency,Bool.false_eq_true,ite_false,pole] using! two_pole_integrable μ a b hμ
  · have h:=(RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (two_pole_integrable μ a b hμ)
    have he(q:ℝ):star (P true μ a q)*P true μ b q=star (star (pole μ a q)*pole μ b q):=by
      simp only [P,actualFrequency,ite_true,pole,star_mul,star_inv₀,star_sub,Complex.star_def,Complex.conj_ofReal]
      ring
    simpa only [he] using! h
private theorem finite_pair {ι:Type*}[Fintype ι](c d:ι→QuantumTest)(a:ι→ℂ):
    sourcePair (∑i,a i • c i) (∑j,a j • d j)=∑i,∑j,(star (a i)*a j)*sourcePair (c i) (d j):=by
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  ring
private theorem finite_pair_integrable {ι:Type*}[Fintype ι](a:ι→ℝ)(c d:ι→QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Integrable (fun q:ℝ=>sourcePair (∑i,P advanced μ (a i) q • c i) (∑i,P advanced μ (a i) q • d i)):=by
  have hi:Integrable (fun q:ℝ=>∑i,∑j,(star (P advanced μ (a i) q)*P advanced μ (a j) q)*sourcePair (c i) (d j)):=
    integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>
      (pole_pair_integrable advanced μ hμ (a i) (a j)).mul_const _))
  exact hi.congr (Eventually.of_forall (fun q=>(finite_pair c d _).symm))
private theorem finite_forcing {ι:Type*}[Fintype ι](a:ι→ℝ)(c:ι→QuantumTest)(hc:(∑i,c i)=0)
    (z:ℂ)(hz:z.im≠0):
    H0 (∑i,((a i:ℂ)-z)⁻¹ • c i)-z • (∑i,((a i:ℂ)-z)⁻¹ • c i)=
      ∑i,((a i:ℂ)-z)⁻¹ • (H0 (c i)-(a i:ℂ) • c i):=by
  have hn(i:ι):(a i:ℂ)-z≠0:=by
    intro h
    have him:=congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at him
    exact hz him
  have he(i:ι):H0 (((a i:ℂ)-z)⁻¹ • c i)-z • (((a i:ℂ)-z)⁻¹ • c i)=
      ((a i:ℂ)-z)⁻¹ • (H0 (c i)-(a i:ℂ) • c i)+c i:=by
    have hcoef:((a i:ℂ)-z)⁻¹*(a i:ℂ)-z*((a i:ℂ)-z)⁻¹=1:=by field_simp [hn i]
    simp only [map_smul,smul_sub,smul_smul]
    linear_combination (norm:=module) congrArg (fun b:ℂ=>b • c i) hcoef
  simp only [map_sum,Finset.smul_sum,←Finset.sum_sub_distrib,he,Finset.sum_add_distrib,hc,add_zero]
private theorem whole_forcing_columns(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2=
      ∑j:Channel F,P advanced (sourceNoetherFrequency half) (channelValue F j) q •
        (H0 (wholeClockColumn s hs half advanced m ell F g x j)-
          (channelValue F j:ℂ) • wholeClockColumn s hs half advanced m ell F g x j):=by
  have hc:(∑j:Channel F,wholeClockColumn s hs half advanced m ell F g x j)=0:=by
    unfold wholeClockColumn
    rw [←map_sum,(actual_whole_electric_source_carrier s hs half advanced m ell F g).1,map_zero]
  have he:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  have he':H0 (wholeClockState s hs half advanced m ell F g x q)=
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2+
        actualFrequency advanced (sourceNoetherFrequency half) q • wholeClockState s hs half advanced m ell F g x q:=by
    simpa only [wholeClockState] using he
  have h:=finite_forcing (channelValue F) (wholeClockColumn s hs half advanced m ell F g x) hc
    (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q)
  rw [←actual_whole_clock_channels,he'] at h
  simpa only [add_sub_cancel_right,P] using h

/-- Both complete forcing and its negative matched completion retain their actual finite/escape columns. Their frequency integrability is generated, without a norm budget. -/
theorem actual_whole_completed_forcing_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>‖embed (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2‖^2) ∧
    Integrable (fun q:ℝ=>‖embed (M (wholeClockState s hs half advanced m ell F g x q))+
      ((144/n:ℝ):ℂ) • embed (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2‖^2):=by
  let c:=wholeClockColumn s hs half advanced m ell F g x
  let d:=fun j:Channel F=>H0 (c j)-(channelValue F j:ℂ) • c j
  have hn(e:Channel F→QuantumTest):Integrable (fun q:ℝ=>‖embed (∑i,P advanced (sourceNoetherFrequency half) (channelValue F i) q • e i)‖^2):=by
    simpa only [sourcePair,RCLike.re_eq_complex_re,inner_self_eq_norm_sq] using
      (finite_pair_integrable (channelValue F) e e advanced _ (frequency_positive half)).re
  constructor
  · exact (hn d).congr (Eventually.of_forall (fun q=>by dsimp only;rw [whole_forcing_columns]))
  · apply (hn (fun j=>M (c j)+((144/n:ℝ):ℂ) • d j)).congr
    apply Eventually.of_forall;intro q
    dsimp only
    rw [whole_forcing_columns,actual_whole_clock_channels]
    simp only [c,d,P,map_add,map_sum,map_smul,smul_add,Finset.sum_add_distrib,Finset.smul_sum,smul_smul,mul_comm]

def retainedNativePrice(w:QuantumTest):ℝ:=
  -3*(sourcePair w (U (nativeDilationWord w))).re+12*n*spinForm (U w)+12*n*densityForm (U w)-
    24*n*radiusForm w-12*(sourcePair w (U (scalarSpatialAction w))).re-13*n*inverseNativeEnergy w+
    (35*n/96)*‖embed (U (D w))‖^2-2*gaugeForm (U w)-8*(sourcePair w (U (magneticAction w))).re
private theorem native_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>retainedNativePrice (wholeClockState s hs half advanced m ell F g x q)):=by
  let w:=wholeClockState s hs half advanced m ell F g x
  have hP(L R:End):Integrable (fun q:ℝ=>sourcePair (L (w q)) (R (w q))):=
    actual_whole_state_pair_integrable s hs half advanced m ell F g x L R
  have hN(L:End):Integrable (fun q:ℝ=>‖embed (L (w q))‖^2):=
    actual_whole_state_square_integrable s hs half advanced m ell F g x L
  have hs:Integrable (fun q:ℝ=>spinForm (U (w q))):=by
    unfold spinForm
    exact integrable_finsetSum Finset.univ (fun a _=>(hN (GaussCoframeSpin.current a*U)).const_mul _)
  have hd:Integrable (fun q:ℝ=>densityForm (U (w q))):=by
    unfold densityForm numberForm
    exact (((hN (GaussCoframeForm.number*U)).const_mul _).add
      ((hP U (GaussCoframeForm.number*U)).re.const_mul _)).add ((hN U).const_mul _)
  have hr:Integrable (fun q:ℝ=>radiusForm (w q)):=by
    unfold radiusForm
    apply Integrable.re (𝕜:=ℂ)
    simpa only [Module.End.one_apply] using hP 1 _
  have hI:Integrable (fun q:ℝ=>inverseNativeEnergy (w q)):=by
    unfold inverseNativeEnergy
    exact integrable_finsetSum Finset.univ (fun a _=>hN (U*GaussCoreDifferential.covariantMomentum (scalarDirection a)))
  have hg:Integrable (fun q:ℝ=>gaugeForm (U (w q))):=by
    unfold gaugeForm
    apply Integrable.const_mul
    apply Integrable.re (𝕜:=ℂ)
    apply integrable_finsetSum;intro a _
    apply integrable_finsetSum;intro i _
    apply integrable_finsetSum;intro j _
    simp only [←Module.End.mul_apply]
    exact hP _ _
  change Integrable (fun q:ℝ=>retainedNativePrice (w q))
  unfold retainedNativePrice
  have h0:=((hP 1 (U*nativeDilationWord)).re.const_mul (-3)).add (hs.const_mul (12*n))
  have h1:=(h0.add (hd.const_mul (12*n))).sub (hr.const_mul (24*n))
  have h2:=(h1.sub ((hP 1 (U*scalarSpatialAction)).re.const_mul (12:ℝ))).sub (hI.const_mul (13*n))
  have h3:=((h2.add ((hN (U*D)).const_mul (35*n/96))).sub (hg.const_mul (2:ℝ))).sub
    ((hP 1 (U*magneticAction)).re.const_mul (8:ℝ))
  convert! h3 using 1

def wholeRetainedPhysicalPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  retainedNativePrice (wholeClockState s hs half advanced m ell F g x q)+
    originalNormalizerPrice s hs x (wholeSourceNext s hs half advanced m ell F g q)
def wholePhysicalForceUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  wholeScalarForceUpper s hs half advanced m ell F g x q+wholeRetainedPhysicalPrice s hs half advanced m ell F g x q
private theorem physical_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))=
    wholeScalarForcingPrice s hs half advanced m ell F g x q+wholeRetainedPhysicalPrice s hs half advanced m ell F g x q:=by
  have h:=actual_original_whole_native_return s hs half advanced m ell F g q x
  dsimp only at h
  unfold nativePhysicalFields at h
  dsimp only [wholeScalarForcingPrice,wholeRetainedPhysicalPrice,retainedNativePrice,wholeClockState]
  simp only [wholeClockState]
  linarith only [h]
private theorem retained_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (wholeRetainedPhysicalPrice s hs half advanced m ell F g x):=by
  have hn:=actual_whole_completed_forcing_integrable s hs half advanced m ell F g x
  have hN:Integrable (fun q:ℝ=>originalNormalizerPrice s hs x (wholeSourceNext s hs half advanced m ell F g q)):=by
    simpa only [originalNormalizerPrice,wholeClockState,Pi.sub_apply] using! (hn.1.const_mul (432/n)).sub (hn.2.const_mul (n/48))
  exact (native_integrable s hs half advanced m ell F g x).add hN

/-- The complete starting physical action now consumes the actual force/current upper. The full native departments, original forcing and negative matched completion remain in one frequency price. -/
theorem actual_whole_physical_force_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) ∧
    Integrable (wholePhysicalForceUpper s hs half advanced m ell F g x) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) ≤
      ∫q:ℝ,wholePhysicalForceUpper s hs half advanced m ell F g x q:=by
  have hS:=actual_whole_scalar_force_payment s hs half advanced m ell F g x
  have hR:=retained_integrable s hs half advanced m ell F g x
  have hP:Integrable (fun q:ℝ=>physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))):=
    (hS.1.add hR).congr (Eventually.of_forall (fun q=>(physical_return s hs half advanced m ell F g x q).symm))
  refine ⟨hP,hS.2.1.add hR,?_⟩
  simp_rw [physical_return]
  change (∫q:ℝ,wholeScalarForcingPrice s hs half advanced m ell F g x q+wholeRetainedPhysicalPrice s hs half advanced m ell F g x q) ≤
    ∫q:ℝ,wholeScalarForceUpper s hs half advanced m ell F g x q+wholeRetainedPhysicalPrice s hs half advanced m ell F g x q
  rw [integral_add hS.1 hR,integral_add hS.2.1 hR]
  linarith only [hS.2.2]
end LowEnergy.ReverseForcePhysicalPayment
