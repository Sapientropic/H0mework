import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedPhysicalWorkAbel
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedGaussianMeanSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedNoetherWorkSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiCorrectedFluctuationPhysicalWork
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourceClockPhiNativeJointPayment
open SourceClockPhiCombinedScalePressure SourceClockPhiNormalizedScalarBudget
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceScalarPairedTransport SourceLocalizedInverseFormPayment SourceScalarPositiveBulkWard
open SourceBulkTwoTime SourceResolventBandLimit SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceInverseJetEnergy FullYSourceResolventGraphSplice
open SourceInverseNoetherChannelGap SourceInverseElectricMomentChannels
open ClockPhiHeatCorrectedCovarianceSource ClockPhiCorrectedGaussianMeanSource
open ClockPhiCorrectedPhysicalWorkAbel ClockPhiHeatCorrectedHamiltonianSource
open MeasureTheory Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] diagonalAction compressionCore defectAction resolventCore sourcePair embed
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ₂:=γ.prod γ
private abbrev Pair:=ℝ×ℝ

def fluctuationCore(τ:ℝ)(hτ:0<τ)(x:Pair):End:=correctedCompleteCore τ hτ x.1 x.2-1
private theorem fluctuation_apply(τ:ℝ)(hτ:0<τ)(x:Pair)(f:QuantumTest):
    fluctuationCore τ hτ x f=correctedCompleteCore τ hτ x.1 x.2 f-f:=rfl
private theorem mass_pair(τ:ℝ)(hτ:0<τ)(x:Pair)(f g:QuantumTest):
    sourcePair (correctedCompleteCore τ hτ x.1 x.2 f) (correctedCompleteCore τ hτ x.1 x.2 g)=
      sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) g):=by
  change sourcePair
    (SourceClockPhiCoframeForwardCore.sourceForwardCore τ hτ.le
      (correctedProfileCore τ hτ x.1 x.2 (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)))
    (SourceClockPhiCoframeForwardCore.sourceForwardCore τ hτ.le
      (correctedProfileCore τ hτ x.1 x.2 (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) g)))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact ClockPhiConservativeHeatSource.clockProfileAction_pair _ _ _ _ _ _
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]

private theorem fluctuation_hamiltonian_integrable(τ:ℝ)(hτ:0<τ)(f g:QuantumTest):
    Integrable (fun x:Pair=>sourcePair (fluctuationCore τ hτ x f)
      (diagonalAction (fluctuationCore τ hτ x g))) γ₂:=by
  have hi:=(actual_corrected_hamiltonian_gaussian τ hτ f g).1
  have hf:=(actual_corrected_complete_mean_source τ hτ f).1.inner_const (𝕜:=ℂ) (embed (diagonalAction g))
  have hg:=(actual_corrected_complete_mean_source τ hτ g).1.const_inner (𝕜:=ℂ) (embed (diagonalAction f))
  have he(x:Pair):sourcePair (fluctuationCore τ hτ x f) (diagonalAction (fluctuationCore τ hτ x g))=
      sourcePair (correctedCompleteCore τ hτ x.1 x.2 f) (diagonalAction (correctedCompleteCore τ hτ x.1 x.2 g))-
      inner ℂ (embed (correctedCompleteCore τ hτ x.1 x.2 f)) (embed (diagonalAction g))-
      inner ℂ (embed (diagonalAction f)) (embed (correctedCompleteCore τ hτ x.1 x.2 g))+
      sourcePair f (diagonalAction g):=by
    simp only [fluctuation_apply,map_sub,pair_sub_l,pair_sub_r]
    rw [diagonalAction_pair f]
    simp only [sourcePair]
    ring
  exact (((hi.sub hf).sub hg).add (integrable_const _)).congr
    (Eventually.of_forall (fun x=>(he x).symm))
private theorem fluctuation_mass_integrable(τ:ℝ)(hτ:0<τ)(f g:QuantumTest):
    Integrable (fun x:Pair=>sourcePair (fluctuationCore τ hτ x f) (fluctuationCore τ hτ x g)) γ₂:=by
  have hf:=(actual_corrected_complete_mean_source τ hτ f).1.inner_const (𝕜:=ℂ) (embed g)
  have hg:=(actual_corrected_complete_mean_source τ hτ g).1.const_inner (𝕜:=ℂ) (embed f)
  have h0:Integrable (fun _:Pair=>sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) g)) γ₂:=integrable_const _
  have he(x:Pair):sourcePair (fluctuationCore τ hτ x f) (fluctuationCore τ hτ x g)=
      sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) f)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt τ) g)-
      inner ℂ (embed (correctedCompleteCore τ hτ x.1 x.2 f)) (embed g)-
      inner ℂ (embed f) (embed (correctedCompleteCore τ hτ x.1 x.2 g))+sourcePair f g:=by
    simp only [fluctuation_apply,pair_sub_l,pair_sub_r]
    rw [mass_pair]
    simp only [sourcePair]
    ring
  exact (((h0.sub hf).sub hg).add (integrable_const _)).congr
    (Eventually.of_forall (fun x=>(he x).symm))

private theorem frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(q:ℝ):
    (actualFrequency advanced μ q).im≠0:=by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private def causeTime(advanced:Bool)(t:ℝ):ℝ:=if advanced then -t else t
private def polePair(advanced:Bool)(μ a b q:ℝ):ℂ:=
  star (((a:ℂ)-actualFrequency advanced μ q)⁻¹)*((b:ℂ)-actualFrequency advanced μ q)⁻¹
private def phasePair(advanced:Bool)(μ a b t:ℝ):ℂ:=
  Complex.exp (-(2*(μ:ℂ))*(t:ℂ))*star (phase a (causeTime advanced t))*phase b (causeTime advanced t)
private def sourceColumn(m ell:ℕ)(F:Index)(g:diagonal.domain)(j:Channel F):QuantumTest:=
  ∑i:Fin 2,phaseRow m ell i (channelTest F (inputSeed g i) j)
private def fluctuationChannel(τ:ℝ)(hτ:0<τ)(x:Pair)(m ell:ℕ)(F:Index)(g:diagonal.domain)(j:Channel F):QuantumTest:=
  ∑i:Fin 2,fluctuationCore τ hτ x (phaseRow m ell i (channelTest F (inputSeed g i) j))
private def fluctuationTransition(τ:ℝ)(hτ:0<τ)(x:Pair)(m ell:ℕ)(F:Index)(g:diagonal.domain)(i j:Channel F):ℂ:=
  sourcePair (fluctuationChannel τ hτ x m ell F g i) (diagonalAction (fluctuationChannel τ hτ x m ell F g j))-
    (((channelValue F i+channelValue F j)/2:ℝ):ℂ)*
      sourcePair (fluctuationChannel τ hτ x m ell F g i) (fluctuationChannel τ hτ x m ell F g j)
private theorem fluctuation_channel(τ:ℝ)(hτ:0<τ)(x:Pair)(m ell:ℕ)(F:Index)(g:diagonal.domain)(j:Channel F):
    fluctuationChannel τ hτ x m ell F g j=fluctuationCore τ hτ x (sourceColumn m ell F g j):=by
  simp only [fluctuationChannel,sourceColumn,map_sum]
private theorem transition_integrable(τ:ℝ)(hτ:0<τ)(m ell:ℕ)(F:Index)(g:diagonal.domain)(i j:Channel F):
    Integrable (fun x:Pair=>fluctuationTransition τ hτ x m ell F g i j) γ₂:=by
  have hH:=fluctuation_hamiltonian_integrable τ hτ (sourceColumn m ell F g i) (sourceColumn m ell F g j)
  have hM:=fluctuation_mass_integrable τ hτ (sourceColumn m ell F g i) (sourceColumn m ell F g j)
  simpa only [fluctuationTransition,fluctuation_channel,Pi.sub_apply] using!
    hH.sub (hM.const_mul (((channelValue F i+channelValue F j)/2:ℝ):ℂ))

def fluctuationFrequencyMiddle(τ:ℝ)(hτ:0<τ)(x:Pair)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℂ:=
  let u:=fluctuationCore τ hτ x (normalizedState m ell F z hz g)
  sourcePair u (diagonalAction u-(z.re:ℂ) • u)
def fluctuationPhysicalColumn(τ:ℝ)(hτ:0<τ)(x:Pair)(m ell:ℕ)(F:Index)(g:diagonal.domain)(t:ℝ):QuantumTest:=
  ∑i:Fin 2,fluctuationCore τ hτ x (phaseRow m ell i (coreTime F (inputSeed g i) t))
def fluctuationPhysicalClock(τ:ℝ)(hτ:0<τ)(x:Pair)(m ell:ℕ)(F:Index)(g:diagonal.domain)(t:ℝ):QuantumTest:=
  ∑i:Fin 2,fluctuationCore τ hτ x (phaseRow m ell i (compressionCore F (coreTime F (inputSeed g i) t)))
def fluctuationPhysicalDrift(τ:ℝ)(hτ:0<τ)(x:Pair)(m ell:ℕ)(F:Index)(g:diagonal.domain)(t:ℝ):QuantumTest:=
  ∑i:Fin 2,(SourceScalarDoubleCurrent.bracket diagonalAction (fluctuationCore τ hτ x*phaseRow m ell i)
      (coreTime F (inputSeed g i) t)+
    fluctuationCore τ hτ x (phaseRow m ell i (defectAction F (coreTime F (inputSeed g i) t))))
def fluctuationPhysicalAbel(τ:ℝ)(hτ:0<τ)(x:Pair)(advanced:Bool)(μ:ℝ)(m ell:ℕ)(F:Index)(g:diagonal.domain)(t:ℝ):ℂ:=
  let y:=fluctuationPhysicalColumn τ hτ x m ell F g (causeTime advanced t)
  let c:=fluctuationPhysicalClock τ hτ x m ell F g (causeTime advanced t)
  Complex.exp (-(2*(μ:ℂ))*(t:ℂ))*(sourcePair y (diagonalAction y)-(sourcePair c y+sourcePair y c)/2)

/-- The original zero-column producer is consumed by the literal same-noise K-I legs, with all defects retained. -/
theorem actual_fluctuation_joint_physical_work(τ:ℝ)(hτ:0<τ)(μ:ℝ)(hμ:0<μ)(advanced:Bool)
    (m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (fun u:Pair×ℝ=>fluctuationFrequencyMiddle τ hτ u.1 m ell F (actualFrequency advanced μ u.2)
      (frequency_nonreal advanced μ hμ u.2) g) (γ₂.prod volume) ∧
    Integrable (fun u:Pair×ℝ=>fluctuationPhysicalAbel τ hτ u.1 advanced μ m ell F g u.2)
      (γ₂.prod (volume.restrict (Set.Ioi 0))) ∧
    (∫q:ℝ,∫x:Pair,fluctuationFrequencyMiddle τ hτ x m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g ∂γ₂)=
      2*(Real.pi:ℂ)*(∫t:ℝ in Set.Ioi 0,∫x:Pair,fluctuationPhysicalAbel τ hτ x advanced μ m ell F g t ∂γ₂) ∧
    ∀x:Pair,∀t:ℝ,(fluctuationPhysicalAbel τ hτ x advanced μ m ell F g t).re=
      Real.exp (-2*μ*t)*(sourcePair (fluctuationPhysicalColumn τ hτ x m ell F g (causeTime advanced t))
        (fluctuationPhysicalDrift τ hτ x m ell F g (causeTime advanced t))).re:=by
  have hs(x:Pair):=actual_linear_physical_work_source (fluctuationCore τ hτ x) μ hμ advanced m ell F g
  let C:Channel F→Channel F→Pair→ℂ:=fun i j x=>fluctuationTransition τ hτ x m ell F g i j
  have hC(i j:Channel F):Integrable (C i j) γ₂:=transition_integrable τ hτ m ell F g i j
  have hP(a b:ℝ):Integrable (polePair advanced μ a b) ∧ IntegrableOn (phasePair advanced μ a b) (Set.Ioi 0):=
    (hs (0,0)).2.2.1 a b
  have heF(x:Pair)(q:ℝ):fluctuationFrequencyMiddle τ hτ x m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g=
      ∑i:Channel F,∑j:Channel F,polePair advanced μ (channelValue F i) (channelValue F j) q*C i j x:=
    ((hs x).1 _ (frequency_nonreal advanced μ hμ q)).2
  have heA(x:Pair)(t:ℝ):fluctuationPhysicalAbel τ hτ x advanced μ m ell F g t=
      ∑i:Channel F,∑j:Channel F,phasePair advanced μ (channelValue F i) (channelValue F j) t*C i j x:=
    (hs x).2.1 t
  have hF:Integrable (fun u:Pair×ℝ=>fluctuationFrequencyMiddle τ hτ u.1 m ell F (actualFrequency advanced μ u.2)
      (frequency_nonreal advanced μ hμ u.2) g) (γ₂.prod volume):=by
    simp_rw [heF]
    apply integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>?_))
    simpa only [mul_comm] using (hC i j).mul_prod (hP (channelValue F i) (channelValue F j)).1
  have hA:Integrable (fun u:Pair×ℝ=>fluctuationPhysicalAbel τ hτ u.1 advanced μ m ell F g u.2)
      (γ₂.prod (volume.restrict (Set.Ioi 0))):=by
    simp_rw [heA]
    apply integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>?_))
    simpa only [mul_comm] using (hC i j).mul_prod (hP (channelValue F i) (channelValue F j)).2
  refine ⟨hF,hA,?_,fun x=>(hs x).2.2.2.2.2.2⟩
  have hr(x:Pair):(∫q:ℝ,fluctuationFrequencyMiddle τ hτ x m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g)=
      2*(Real.pi:ℂ)*(∫t:ℝ in Set.Ioi 0,fluctuationPhysicalAbel τ hτ x advanced μ m ell F g t):=
    (hs x).2.2.2.2.2.1
  rw [←integral_integral_swap hF]
  simp_rw [hr]
  rw [integral_const_mul,integral_integral_swap hA]

private def baseFrequencyMiddle(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℂ:=
  let w:=normalizedState m ell F z hz g
  sourcePair w (diagonalAction w-(z.re:ℂ) • w)
private def basePhysicalAbel(advanced:Bool)(μ:ℝ)(m ell:ℕ)(F:Index)(g:diagonal.domain)(t:ℝ):ℂ:=
  let y:=∑i:Fin 2,phaseRow m ell i (coreTime F (inputSeed g i) (causeTime advanced t))
  let c:=∑i:Fin 2,phaseRow m ell i (compressionCore F (coreTime F (inputSeed g i) (causeTime advanced t)))
  Complex.exp (-(2*(μ:ℂ))*(t:ℂ))*(sourcePair y (diagonalAction y)-(sourcePair c y+sourcePair y c)/2)

def noetherMeanSource(τ:ℝ)(hτ:0<τ)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  let w:=normalizedState m ell F z hz g
  2*(inner ℂ (ClockPhiCorrectedNoetherWorkSource.actualMeanIncrement τ hτ w)
      (embed (normalizedForcing m ell F z hz g))).re-
    2*z.im*(inner ℂ (ClockPhiCorrectedNoetherWorkSource.actualMeanIncrement τ hτ w) (embed w)).im

/-- The finite Noether mean source, including its phase, is the same physical-time difference of complete, base, and K-I work. -/
theorem actual_noether_mean_joint_physical_source(τ:ℝ)(hτ:0<τ)(μ:ℝ)(hμ:0<μ)(advanced:Bool)
    (m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (fun q:ℝ=>noetherMeanSource τ hτ m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g) ∧
    (∫q:ℝ,noetherMeanSource τ hτ m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g)=
      (2*(Real.pi:ℂ)*((∫t:ℝ in Set.Ioi 0,∫x:Pair,
        correctedPhysicalAbel τ hτ x.1 x.2 advanced μ m ell F g t ∂γ₂)-
        (∫t:ℝ in Set.Ioi 0,basePhysicalAbel advanced μ m ell F g t)-
        (∫t:ℝ in Set.Ioi 0,∫x:Pair,fluctuationPhysicalAbel τ hτ x advanced μ m ell F g t ∂γ₂))).re:=by
  have hc:=actual_corrected_joint_physical_work_abel τ hτ μ hμ advanced m ell F g
  have hd:=actual_fluctuation_joint_physical_work τ hτ μ hμ advanced m ell F g
  have h0:=actual_linear_physical_work_source (1:End) μ hμ advanced m ell F g
  let C:ℝ→ℂ:=fun q=>∫x:Pair,correctedFrequencyMiddle τ hτ x.1 x.2 m ell F (actualFrequency advanced μ q)
    (frequency_nonreal advanced μ hμ q) g ∂γ₂
  let D:ℝ→ℂ:=fun q=>∫x:Pair,fluctuationFrequencyMiddle τ hτ x m ell F (actualFrequency advanced μ q)
    (frequency_nonreal advanced μ hμ q) g ∂γ₂
  let B:ℝ→ℂ:=fun q=>baseFrequencyMiddle m ell F (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g
  have hiC:Integrable C:=hc.1.integral_prod_right
  have hiD:Integrable D:=hd.1.integral_prod_right
  have hiB:Integrable B:=h0.2.2.2.1
  have he(q:ℝ):noetherMeanSource τ hτ m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g=(C q).re-(B q).re-(D q).re:=by
    have h:=(ClockPhiCorrectedNoetherWorkSource.actual_corrected_noether_frequency_work τ hτ m ell F
      (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g).2
    let w:=normalizedState m ell F (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g
    change (C q-B q).re=(D q).re+
      2*(inner ℂ (ClockPhiCorrectedNoetherWorkSource.actualMeanIncrement τ hτ w)
        (embed (normalizedForcing m ell F (actualFrequency advanced μ q) (frequency_nonreal advanced μ hμ q) g))).re-
      2*(actualFrequency advanced μ q).im*
        (inner ℂ (ClockPhiCorrectedNoetherWorkSource.actualMeanIncrement τ hτ w) (embed w)).im at h
    simp only [Complex.sub_re] at h
    dsimp only [noetherMeanSource]
    dsimp only [w] at h
    linarith only [h]
  have hi:Integrable (fun q:ℝ=>noetherMeanSource τ hτ m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g):=
    ((hiC.re.sub hiB.re).sub hiD.re).congr (Eventually.of_forall (fun q=>(he q).symm))
  refine ⟨hi,?_⟩
  have hreal:(∫q:ℝ,noetherMeanSource τ hτ m ell F (actualFrequency advanced μ q)
      (frequency_nonreal advanced μ hμ q) g)=((∫q:ℝ,C q)-(∫q:ℝ,B q)-(∫q:ℝ,D q)).re:=by
    have hj:Integrable (fun q:ℝ=>C q-B q-D q):=(hiC.sub hiB).sub hiD
    calc
      _=∫q:ℝ,(C q-B q-D q).re:=by
        apply integral_congr_ae
        exact Eventually.of_forall (fun q=>by dsimp only;rw [he];simp only [Complex.sub_re])
      _=(∫q:ℝ,C q-B q-D q).re:=Complex.reCLM.integral_comp_comm hj
      _=_:=by
        have hiCB:Integrable (fun q:ℝ=>C q-B q):=hiC.sub hiB
        rw [integral_sub hiCB hiD,integral_sub hiC hiB]
  have hB:(∫q:ℝ,B q)=2*(Real.pi:ℂ)*(∫t:ℝ in Set.Ioi 0,basePhysicalAbel advanced μ m ell F g t):=
    h0.2.2.2.2.2.1
  have hC:(∫q:ℝ,C q)=2*(Real.pi:ℂ)*(∫t:ℝ in Set.Ioi 0,∫x:Pair,
      correctedPhysicalAbel τ hτ x.1 x.2 advanced μ m ell F g t ∂γ₂):=hc.2.2
  have hD:(∫q:ℝ,D q)=2*(Real.pi:ℂ)*(∫t:ℝ in Set.Ioi 0,∫x:Pair,
      fluctuationPhysicalAbel τ hτ x advanced μ m ell F g t ∂γ₂):=hd.2.2.1
  rw [hreal,hC,hB,hD]
  congr 1
  ring
end LowEnergy.ClockPhiCorrectedFluctuationPhysicalWork
