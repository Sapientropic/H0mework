import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalEcWard
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1600000
noncomputable section
namespace LowEnergy.FirstCurrentWholeCarrier
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore ClockPhiHeatComparisonWork
open ClockPhiHeatCorrectedCovarianceSource SourceClockPhiProfileNativeReturn SourceClockPhiProfileLocalNativeReturn
open SourceClockPhiCorrectedGaussianPair SourceClockPhiCorrectedWeightTransport SourceClockPhiForwardNativeReturn
open SourceClockPhiCombinedScalePressure SourceScalarVirialBulk SourceClockPhiHeatLocalNativeGaussian
open SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource SourceClockReflectedForm SourceScalarInverseNativeEnergy
open SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarDoubleCurrent SourceScalarOscillatorAbsorption
open SourceHamiltonianVolume SourceClockPhiMatchedElectricSource SourceInverseNoetherEnergy SourceScalarNativeComparison
open FirstCurrentJointBudget FirstCurrentJointBudgetNext FirstCurrentElectricSuccessor FirstCurrentGeometricPayer
open FirstCurrentPayerNext SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentAdmissibleElectric FirstCurrentAdmissibleElectric.PhysicalGaussian FirstCurrentOriginalEcPayer
open NativePointReturn PositiveClockGenerator FirstCurrentAdmissibleElectric.ScalarGaussian
open SourceClockPhiWholeSignedWorkIntegrable ClockPhiCorrectedPhysicalWorkAbel MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev n:ℝ:=sourceTime 0
private abbrev G(s:ℝ):End:=SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)
attribute [local irreducible] diagonalAction embed normalizedState normalizedForcing sourcePair
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hg:=actual_source_noether_gap half
  linarith
private theorem frequency_nonreal(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
  have hp:=frequency_positive half
  cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hp.ne'
def frequencyState(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):QuantumTest:=
  normalizedState m ell F (actualFrequency advanced (sourceNoetherFrequency half) q)
    (frequency_nonreal half advanced q) g
private theorem pair_frequency(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L R:End):
    Integrable (fun q:ℝ=>sourcePair (L (frequencyState half advanced m ell F g q))
      (R (frequencyState half advanced m ell F g q))):=
  actual_normalized_pair_integrable _ (frequency_positive half) advanced m ell F g L R
private theorem norm_frequency(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>‖embed (L (frequencyState half advanced m ell F g q))‖^2):=by
  have h:=(pair_frequency half advanced m ell F g L L).re
  have he(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
    simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  simpa only[he,RCLike.re_eq_complex_re] using h
private theorem weighted_self_frequency(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>(q:ℂ)*sourcePair (L (frequencyState half advanced m ell F g q))
      (L (frequencyState half advanced m ell F g q))):=by
  have hf:=(actual_linear_physical_work_source L (sourceNoetherFrequency half) (frequency_positive half)
    advanced m ell F g).2.2.2.1
  change Integrable (fun q:ℝ=>sourcePair (L (frequencyState half advanced m ell F g q))
    (diagonalAction (L (frequencyState half advanced m ell F g q))-
      ((actualFrequency advanced (sourceNoetherFrequency half) q).re:ℂ) • L (frequencyState half advanced m ell F g q))) at hf
  have h:=(pair_frequency half advanced m ell F g L (diagonalAction*L)).sub hf
  apply h.congr
  exact Eventually.of_forall (fun q=>by
    dsimp only[Pi.sub_apply,Module.End.mul_apply]
    have hre:(actualFrequency advanced (sourceNoetherFrequency half) q).re=q:=by
      cases advanced <;> simp[actualFrequency,SourceResolventBandLimit.line]
    rw [hre]
    simp only[sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right]
    ring)
private theorem weighted_pair_frequency(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L R:End):
    Integrable (fun q:ℝ=>(q:ℂ)*sourcePair (L (frequencyState half advanced m ell F g q))
      (R (frequencyState half advanced m ell F g q))):=by
  have hL:=weighted_self_frequency half advanced m ell F g L
  have hR:=weighted_self_frequency half advanced m ell F g R
  have hLR:=pair_frequency half advanced m ell F g L R
  apply (hL.norm.add hR.norm).mono'
    ((Complex.continuous_ofReal.aestronglyMeasurable).mul hLR.aestronglyMeasurable)
  exact Eventually.of_forall (fun q=>by
    dsimp only[Pi.add_apply]
    let u:=embed (L (frequencyState half advanced m ell F g q))
    let v:=embed (R (frequencyState half advanced m ell F g q))
    simp only[Pi.mul_apply,sourcePair]
    change ‖(q:ℂ)*inner ℂ u v‖≤‖(q:ℂ)*inner ℂ u u‖+‖(q:ℂ)*inner ℂ v v‖
    rw [norm_mul,norm_mul,norm_mul,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
    simp only[norm_pow,Complex.norm_real,Real.norm_eq_abs,RCLike.norm_ofReal,abs_norm]
    have h:=mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜:=ℂ) u v) (abs_nonneg q)
    have hs:=mul_nonneg (abs_nonneg q) (sq_nonneg (‖u‖-‖v‖))
    nlinarith only[h,hs,mul_nonneg (abs_nonneg q) (sq_nonneg ‖u‖),mul_nonneg (abs_nonneg q) (sq_nonneg ‖v‖)])
private theorem pole_pair_frequency(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L R:End):
    Integrable (fun q:ℝ=>actualFrequency advanced (sourceNoetherFrequency half) q*
      sourcePair (L (frequencyState half advanced m ell F g q)) (R (frequencyState half advanced m ell F g q))):=by
  have h:=weighted_pair_frequency half advanced m ell F g L R
  have hi:=pair_frequency half advanced m ell F g L R
  apply (h.add (hi.const_mul (actualFrequency advanced (sourceNoetherFrequency half) 0))).congr
  exact Eventually.of_forall (fun q=>by
    dsimp only[Pi.add_apply]
    have hz:actualFrequency advanced (sourceNoetherFrequency half) q=(q:ℂ)+actualFrequency advanced (sourceNoetherFrequency half) 0:=by
      cases advanced <;> simp[actualFrequency,SourceResolventBandLimit.line]
    rw [hz]
    ring)
private def scalarAtoms:Fin 4→End:=![scalarKinetic,centeredAction,vacuumLinearAction,vacuumConstantAction]
private def scalarExponents:Fin 4→ℝ:=![-7/9,17/9,14/9,12/9]
private def scalarCoefficients:Fin 3→Fin 4→ℂ:=
  ![![-8,8,-8,2],![-14,34,-56,128/5],![-2/(n:ℂ),0,0,0]]
private def scalarAffine(a:ScalarIndex):End:=multiply
  (fun z=>inner ℝ (scalarField z) (scalarBasis a))
  (fun _=>(scalarField_smooth.inner ℝ contDiff_const).contDiffAt)
private theorem scalar_frequency(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End)(i:Fin 3):
    Integrable (fun q:ℝ=>scalarMean s hs i (L (frequencyState half advanced m ell F g q))):=by
  have h:=integrable_finsetSum (μ:=volume) (s:=Finset.univ) (fun j (_:j∈Finset.univ)=>
    (pair_frequency half advanced m ell F g (forwardUAction s hs.le*L)
      (gaussianProfileWeight s hs (scalarExponents j)*scalarAtoms j*L)).const_mul (scalarCoefficients i j))
  exact h.re
private theorem quarter_frequency(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>quarterMean s hs (L (frequencyState half advanced m ell F g q))):=by
  have h:=integrable_finsetSum (μ:=volume) (s:=Finset.univ) (fun a (_:a∈Finset.univ)=>
    (pair_frequency half advanced m ell F g (forwardUAction s hs.le*GaussCoreDifferential.covariantMomentum (scalarDirection a)*L)
      (gaussianProfileWeight s hs (1/3)*scalarAffine a*L)).sub
    ((pair_frequency half advanced m ell F g (forwardUAction s hs.le*GaussCoreDifferential.covariantMomentum (scalarDirection a)*L)
      (gaussianProfileWeight s hs (2/9)*L)).const_mul ((3*inner ℝ (scalarBasis a) vacuum/4:ℝ):ℂ)))
  exact h
private theorem native_frequency(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>nativePositiveMean s hs (L (frequencyState half advanced m ell F g q))
      (L (frequencyState half advanced m ell F g q))):=by
  have hp(p:ℝ)(T:End):Integrable (fun q:ℝ=>sourcePair (forwardUAction s hs.le (L (frequencyState half advanced m ell F g q)))
      (gaussianProfileWeight s hs p (T (L (frequencyState half advanced m ell F g q))))):=
    pair_frequency half advanced m ell F g (forwardUAction s hs.le*L) (gaussianProfileWeight s hs p*T*L)
  exact (((((((hp (-7/9) scalarKinetic).const_mul (-14:ℂ)).add ((hp (11/9) gaugeKinetic).const_mul 22)).sub
    ((hp (-1/9) GaussMatterCore.matterAction).const_mul 2)).add ((hp (17/9) centeredAction).const_mul 34)).sub
    ((hp (14/9) vacuumLinearAction).const_mul 56)).add ((hp (12/9) vacuumConstantAction).const_mul 24)).add
    ((hp (6/9) scalarSpatialAction).const_mul 12) |>.add ((hp (8/9) magneticAction).const_mul 16)
private theorem local_frequency(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>localPositiveMean s hs (L (frequencyState half advanced m ell F g q))
      (L (frequencyState half advanced m ell F g q))):=by
  have hp(p:ℝ)(T:End):Integrable (fun q:ℝ=>sourcePair (forwardUAction s hs.le (L (frequencyState half advanced m ell F g q)))
      (gaussianProfileWeight s hs p (T (L (frequencyState half advanced m ell F g q))))):=
    pair_frequency half advanced m ell F g (forwardUAction s hs.le*L) (gaussianProfileWeight s hs p*T*L)
  exact (((hp (-2/3) SourceCoframeCovariantSquare.spinRemainder).const_mul (-12:ℂ)).add
    ((hp (-2/3) GaussCoframeForm.numberShift).const_mul (-12:ℂ))).add ((hp (4/3) (multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth)).const_mul 24)
private theorem field_frequency(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>matchedFieldMean s hs (L (frequencyState half advanced m ell F g q))):=by
  have hp(p:ℝ)(T:End):Integrable (fun q:ℝ=>sourcePair (forwardUAction s hs.le (L (frequencyState half advanced m ell F g q)))
      (gaussianProfileWeight s hs p (T (L (frequencyState half advanced m ell F g q))))):=
    pair_frequency half advanced m ell F g (forwardUAction s hs.le*L) (gaussianProfileWeight s hs p*T*L)
  have hn:Integrable (fun q:ℝ=>matchedNativeMean s hs (L (frequencyState half advanced m ell F g q))):=
    (((((hp (-1/9) GaussMatterCore.matterAction).const_mul (2:ℂ)).add
      ((hp (4/3) vacuumConstantAction).const_mul (8/5:ℂ))).sub ((hp (11/9) gaugeKinetic).const_mul 12)).sub
      ((hp (2/3) scalarSpatialAction).const_mul 12)).sub ((hp (8/9) magneticAction).const_mul 12)
  let T:End:=G s*forwardUAction s hs.le*L
  have hspin:Integrable (fun q:ℝ=>spinForm (T (frequencyState half advanced m ell F g q))):=by
    exact integrable_finsetSum (μ:=volume) (s:=Finset.univ) (fun a (_:a∈Finset.univ)=>
      (norm_frequency half advanced m ell F g (GaussCoframeSpin.current a*T)).const_mul (SourceCoframeCovariantSquare.residualWeight a))
  have hnum:Integrable (fun q:ℝ=>numberForm (T (frequencyState half advanced m ell F g q))):=
    (pair_frequency half advanced m ell F g T (GaussCoframeForm.number*T)).re
  have hden:Integrable (fun q:ℝ=>densityForm (T (frequencyState half advanced m ell F g q))):=
    (((norm_frequency half advanced m ell F g (GaussCoframeForm.number*T)).const_mul (9/16:ℝ)).add
      (hnum.const_mul 3)).add ((norm_frequency half advanced m ell F g T).const_mul (15/2:ℝ))
  exact hn.re.add ((hspin.add hden).const_mul (12*n))

private def cfRow(s:ℝ)(hs:0<s):Fin 3→End:=
  ![coframeQuadraticColumn s hs (0,0)+coframeQuadraticColumn s hs (1,1)+coframeQuadraticColumn s hs (2,2),
    coframeQuadraticColumn s hs (0,1)+coframeQuadraticColumn s hs (1,0),
    coframeQuadraticColumn s hs (0,2)+coframeQuadraticColumn s hs (2,0)]
private def matchedRow(s:ℝ)(hs:0<s):Fin 3→End:=
  ![matchedTester,-(noiseAction s hs 1 0*combinedGenerator),-(noiseAction s hs 0 1*combinedGenerator)]
attribute [local irreducible] coframeQuadraticColumn matchedTester noiseAction combinedGenerator
  SourceClockPhiActualCovarianceStep.sourceGain
private theorem cf_return(s:ℝ)(hs:0<s)(z:ℂ)(f:QuantumTest):
    signedCoframeMean s hs z f=
      -6*((∑i:Fin 3,sourcePair (G s (matchedRow s hs i f)) (G s (cfRow s hs i f)))-
        z*sourcePair (G s (matchedTester f)) (G s f)).re-
      (n/48)*(∑i:Fin 3,sourcePair (G s (matchedRow s hs i f)) (G s (matchedRow s hs i f))).re:=by
  unfold signedCoframeMean
  rw [(actual_matched_coframe_cubic_price s hs z f).1,(actual_matched_coframe_cubic_price s hs z f).2]
  have hm:matchedSourceRows s hs f=(fun i=>matchedRow s hs i f):=by
    funext i
    fin_cases i <;> rfl
  have h0:coframeForcingColumn s hs z f (0,0)+coframeForcingColumn s hs z f (1,1)+
      coframeForcingColumn s hs z f (2,2)=cfRow s hs 0 f-z • f:=by
    change (coframeQuadraticColumn s hs (0,0) f-z • f)+(coframeQuadraticColumn s hs (1,1) f-0)+
      (coframeQuadraticColumn s hs (2,2) f-0)=
      (coframeQuadraticColumn s hs (0,0) f+coframeQuadraticColumn s hs (1,1) f+coframeQuadraticColumn s hs (2,2) f)-z • f
    module
  have h1:coframeForcingColumn s hs z f (0,1)+coframeForcingColumn s hs z f (1,0)=cfRow s hs 1 f:=by
    change (coframeQuadraticColumn s hs (0,1) f-0)+(coframeQuadraticColumn s hs (1,0) f-0)=_
    simp only[sub_zero]
    rfl
  have h2:coframeForcingColumn s hs z f (0,2)+coframeForcingColumn s hs z f (2,0)=cfRow s hs 2 f:=by
    change (coframeQuadraticColumn s hs (0,2) f-0)+(coframeQuadraticColumn s hs (2,0) f-0)=_
    simp only[sub_zero]
    rfl
  rw [hm]
  simp only[cubicSourcePair,h0,h1,h2,Fin.sum_univ_three,map_sub,map_smul,sourcePair,inner_sub_right,inner_smul_right,Complex.add_re,Complex.sub_re]
  have hm0:matchedRow s hs 0=matchedTester:=rfl
  simp only[hm0,G]
  ring
private theorem coframe_frequency(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>signedCoframeMean s hs (actualFrequency advanced (sourceNoetherFrequency half) q)
      (L (frequencyState half advanced m ell F g q))):=by
  have hc:=integrable_finsetSum (μ:=volume) (s:=Finset.univ) (fun i (_:i∈Finset.univ)=>
    pair_frequency half advanced m ell F g (G s*matchedRow s hs i*L) (G s*cfRow s hs i*L))
  have hm:=integrable_finsetSum (μ:=volume) (s:=Finset.univ) (fun i (_:i∈Finset.univ)=>
    pair_frequency half advanced m ell F g (G s*matchedRow s hs i*L) (G s*matchedRow s hs i*L))
  have hz:=pole_pair_frequency half advanced m ell F g (G s*matchedTester*L) (G s*L)
  have h:=((hc.sub hz).re.const_mul (-6)).sub (hm.re.const_mul (n/48))
  apply h.congr
  exact Eventually.of_forall (fun q=>by
    dsimp only[Pi.add_apply,Pi.sub_apply,Module.End.mul_apply]
    simp only[RCLike.re_eq_complex_re]
    exact (cf_return s hs _ _).symm)

/-- The complete positive-clock physical price is integrable over the original frequency curve
for every fixed source word. The zero-column physical identity pays its genuine frequency term. -/
theorem actual_physical_mean_frequency_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>physicalMean s hs half advanced q (L (frequencyState half advanced m ell F g q))):=by
  have h0:=scalar_frequency s hs half advanced m ell F g L 0
  have h1:=scalar_frequency s hs half advanced m ell F g L 1
  have h2:=scalar_frequency s hs half advanced m ell F g L 2
  have hQ:=(quarter_frequency s hs half advanced m ell F g L).re
  have hN:=((native_frequency s hs half advanced m ell F g L).add (local_frequency s hs half advanced m ell F g L)).re
  have hF:=field_frequency s hs half advanced m ell F g L
  have hC:=coframe_frequency s hs half advanced m ell F g L
  have hUD:Integrable (fun q:ℝ=>(FirstCurrentPayer.clockUDDensity s hs (L (frequencyState half advanced m ell F g q))).re):=
    (pair_frequency half advanced m ell F g (forwardUAction s hs.le*combinedConjugate*L)
      (gaussianProfileWeight s hs (-2/3)*combinedConjugate*L)).re
  have hnorm:=norm_frequency half advanced m ell F g (G s*L)
  have h:=(((((((h0.const_mul (sourceNoetherFrequency half)).add
    (hQ.const_mul ((if advanced then (-1:ℝ) else 1)*16*n^2))).const_mul (scalarNoetherFactor half)).add
    hN).add hF).sub h1).add hC).add (hUD.const_mul (35*n/96)) |>.sub (hnorm.const_mul (72*n)) |>.sub (h2.const_mul (7*n))
  apply h.congr
  exact Eventually.of_forall (fun q=>by
    dsimp only[Pi.add_apply,Pi.sub_apply,Module.End.mul_apply]
    simp only[physicalMean,RCLike.re_eq_complex_re])

/-- The full signed first-current mean has its own original-frequency L1 source,
including the genuine frequency term and every negative completed-square contribution. -/
theorem actual_first_current_mean_frequency_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)
    (m ell:ℕ)(F:Index)(g:diagonal.domain)(L:End):
    Integrable (fun q:ℝ=>firstCurrentGaussianMean s hs (actualFrequency advanced (sourceNoetherFrequency half) q)
      (L (frequencyState half advanced m ell F g q))):=by
  have hN:=((native_frequency s hs half advanced m ell F g L).add (local_frequency s hs half advanced m ell F g L)).re
  have hF:=field_frequency s hs half advanced m ell F g L
  have hC:=coframe_frequency s hs half advanced m ell F g L
  have hUD:Integrable (fun q:ℝ=>(FirstCurrentPayer.clockUDDensity s hs (L (frequencyState half advanced m ell F g q))).re):=
    (pair_frequency half advanced m ell F g (forwardUAction s hs.le*combinedConjugate*L)
      (gaussianProfileWeight s hs (-2/3)*combinedConjugate*L)).re
  apply (((hN.add hF).add (hUD.const_mul (35*n/96))).add hC).congr
  exact Eventually.of_forall (fun q=>by
    dsimp only[Pi.add_apply,Module.End.mul_apply]
    simp only[firstCurrentGaussianMean,signedCoframeMean,RCLike.re_eq_complex_re]
    ring)
end LowEnergy.FirstCurrentWholeCarrier
