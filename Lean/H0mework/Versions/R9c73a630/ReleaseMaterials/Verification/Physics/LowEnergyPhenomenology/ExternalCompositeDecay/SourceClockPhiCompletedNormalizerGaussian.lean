import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompletedSourceNormalizer
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRCommutatorSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource
open ClockPhiHeatCorrectedCovarianceSource FirstCurrentWholeVariance FirstCurrentPayerNext
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier GaussianProfileFirstMoment
open SourceClockPhiCorrectedGaussianPair SourceClockPhiNormalizedScalarBudget PositiveClockGenerator
open ClockPhiHeatCorrectedHamiltonianSource MeasureTheory
open scoped BigOperators InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev K(s:ℝ)(hs:0<s)(x:ℝ×ℝ):End:=correctedCompleteCore s hs x.1 x.2
private abbrev G(s:ℝ):End:=SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)
private abbrev W(s:ℝ)(hs:0<s)(p q:ℝ)(x:ℝ×ℝ):End:=correctedProfileWeight s hs p q x.1 x.2
private abbrev HC(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(w:QuantumTest):QuantumTest:=actualClockDefect s hs x w (diagonalAction w)
private abbrev n:ℝ:=sourceTime 0
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ₂:=γ.prod γ
attribute [local irreducible] sourcePair embed diagonalAction correctedCompleteCore matchedTester actualClockDefect
  nativeVarianceRow coframeQuadraticColumn matchedNoiseRow firstMomentAction
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by
  simp only [sourcePair,map_sub,inner_sub_left]
private def column(a:QuadraticIndex)(f:QuantumTest):QuadraticIndex→QuantumTest:=fun b=>if b=a then f else 0
private theorem column_return(a:QuadraticIndex)(f:QuantumTest)(x:ℝ×ℝ):
    quadraticSource (column a f) x=(noiseQuadratic a x:ℂ) • f:=by
  classical
  unfold quadraticSource column
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim
private theorem source_add(v w:QuadraticIndex→QuantumTest)(x:ℝ×ℝ):quadraticSource (v+w) x=quadraticSource v x+quadraticSource w x:=by
  simp only [quadraticSource,Pi.add_apply,smul_add,Finset.sum_add_distrib]

def matchedFluctuationColumn(s:ℝ)(hs:0<s)(w:QuantumTest):QuadraticIndex→QuantumTest:=
  column (1,0) (matchedNoiseRow s hs false w)+column (2,0) (matchedNoiseRow s hs true w)
private theorem fluctuation_column_return(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(w:QuantumTest):
    quadraticSource (matchedFluctuationColumn s hs w) x=matchedNoiseSource s hs x w:=by
  rw [matchedFluctuationColumn,source_add,column_return,column_return]
  simp only [noiseQuadratic,(noiseLinear_values x).1,(noiseLinear_values x).2.1,(noiseLinear_values x).2.2,
    mul_one,matchedNoiseSource]
private theorem gain_source(s:ℝ)(v:QuadraticIndex→QuantumTest)(x:ℝ×ℝ):
    G s (quadraticSource v x)=quadraticSource (fun a=>G s (v a)) x:=by
  simp only [quadraticSource,map_sum,map_smul]
private theorem packet_gaussian(s:ℝ)(v w:QuadraticIndex→QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (G s (quadraticSource v x)) (G s (quadraticSource w x))) γ₂ ∧
    (∫x:ℝ×ℝ,sourcePair (G s (quadraticSource v x)) (G s (quadraticSource w x)) ∂γ₂)=coframeGaussianPair s v w:=by
  simpa only [gain_source,Module.End.one_apply,coframeGaussianPair] using
    quadratic_gaussian_pair (fun a=>G s (v a)) (fun a=>G s (w a)) (1:End)

private def nativeCross(s:ℝ)(hs:0<s)(i:Fin 11)(w v:QuantumTest):ℂ:=
  sourcePair (nativeVarianceRow i w) (firstMomentAction s hs false (nativeVariancePower i) (nativeVarianceDegree i) (matchedNoiseRow s hs false v))+
    sourcePair (nativeVarianceRow i w) (firstMomentAction s hs true (nativeVariancePower i) (nativeVarianceDegree i) (matchedNoiseRow s hs true v))
private theorem native_cross_gaussian(s:ℝ)(hs:0<s)(w v:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (G s (nativeVarianceReturn s hs x w)) (G s (matchedNoiseSource s hs x v))) γ₂ ∧
    (∫x:ℝ×ℝ,sourcePair (G s (nativeVarianceReturn s hs x w)) (G s (matchedNoiseSource s hs x v)) ∂γ₂)=∑i:Fin 11,nativeCross s hs i w v:=by
  let row:=fun i:Fin 11=>fun x:ℝ×ℝ=>(x.1:ℂ)*sourcePair
    (G s (W s hs (nativeVariancePower i-1/3) (nativeVarianceDegree i) x (nativeVarianceRow i w))) (G s (matchedNoiseRow s hs false v))+
    (x.2:ℂ)*sourcePair (G s (W s hs (nativeVariancePower i-1/3) (nativeVarianceDegree i) x (nativeVarianceRow i w))) (G s (matchedNoiseRow s hs true v))
  have h(i:Fin 11):Integrable (row i) γ₂ ∧ (∫x:ℝ×ℝ,row i x ∂γ₂)=nativeCross s hs i w v:=by
    have hξ:=actual_gained_single_profile_first_moment s hs false (nativeVariancePower i-1/3) (nativeVarianceDegree i)
      (nativeVarianceRow i w) (matchedNoiseRow s hs false v)
    have hη:=actual_gained_single_profile_first_moment s hs true (nativeVariancePower i-1/3) (nativeVarianceDegree i)
      (nativeVarianceRow i w) (matchedNoiseRow s hs true v)
    have he:(nativeVariancePower i-1/3)+1/3=nativeVariancePower i:=by ring
    simp only [he,noiseCoordinate,Bool.false_eq_true,ite_false,ite_true] at hξ hη
    refine ⟨hξ.1.add hη.1,?_⟩
    rw [integral_add hξ.1 hη.1,hξ.2,hη.2]
    rfl
  have he(x:ℝ×ℝ):sourcePair (G s (nativeVarianceReturn s hs x w)) (G s (matchedNoiseSource s hs x v))=∑i:Fin 11,row i x:=by
    simp only [nativeVarianceReturn,LinearMap.sum_apply,Module.End.mul_apply,matchedNoiseSource,map_sum,map_add,map_smul,
      sourcePair,sum_inner,inner_add_right,inner_smul_right,row,Finset.sum_add_distrib,Finset.mul_sum]
  refine ⟨(integrable_finsetSum Finset.univ (fun i _=>(h i).1)).congr (Filter.Eventually.of_forall (fun x=>(he x).symm)),?_⟩
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _=>(h i).1)]
  exact Finset.sum_congr rfl (fun i _=>(h i).2)

/-- All eleven native rows and the full ordered coframe columns enter this actual mixed source price. -/
def commutatorMatchedMean(s:ℝ)(hs:0<s)(w v:QuantumTest):ℂ:=
  (∑i:Fin 11,nativeCross s hs i w v)+coframeGaussianPair s (fun a=>coframeQuadraticColumn s hs a w) (matchedFluctuationColumn s hs v)

theorem actual_full_matched_cross_gaussian(s:ℝ)(hs:0<s)(w v:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (HC s hs x w) (matchedClockDefect s hs x v)) γ₂ ∧
    (∫x:ℝ×ℝ,sourcePair (HC s hs x w) (matchedClockDefect s hs x v) ∂γ₂)=commutatorMatchedMean s hs w v:=by
  have hn:=native_cross_gaussian s hs w v
  have hc:=packet_gaussian s (fun a=>coframeQuadraticColumn s hs a w) (matchedFluctuationColumn s hs v)
  simp only [fluctuation_column_return] at hc
  have hz:=actual_matched_clock_centered s hs (diagonalAction w) v
  have he(x:ℝ×ℝ):sourcePair (HC s hs x w) (matchedClockDefect s hs x v)=
      sourcePair (G s (nativeVarianceReturn s hs x w)) (G s (matchedNoiseSource s hs x v))+
        sourcePair (G s (quadraticSource (fun a=>coframeQuadraticColumn s hs a w) x)) (G s (matchedNoiseSource s hs x v))-
          sourcePair (K s hs x (diagonalAction w)) (matchedClockDefect s hs x v):=by
    simp only [HC,actualClockDefect]
    rw [pair_sub_l,actual_whole_variance_column]
    simp only [actual_matched_clock_defect_source,actual_complete_clock_pair]
    simp only [wholeVarianceColumn,map_add,sourcePair,inner_add_left]
  refine ⟨((hn.1.add hc.1).sub hz.1).congr (Filter.Eventually.of_forall (fun x=>(he x).symm)),?_⟩
  simp_rw [he]
  erw [integral_sub (hn.1.add hc.1) hz.1,integral_add hn.1 hc.1,hn.2,hc.2,hz.2,sub_zero]
  rfl

private theorem pair_re(f g:QuantumTest):(sourcePair f g).re=(sourcePair g f).re:=by
  have h:=congrArg Complex.re (GaussNativeForm.pair_conjugate f g)
  simpa only [Complex.conj_re] using h
private theorem pair_self(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only [sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem n_pos:0<n:=by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

def originalNormalizerPrice(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(a:QuantumTest×QuantumTest):ℝ:=
  let b:=clockSourcePair s hs x a
  (432/n)*‖embed b.2‖^2-(n/48)*‖embed (matchedTester b.1)+((144/n:ℝ):ℂ) • embed b.2‖^2
def gainedNormalizerPrice(s:ℝ)(a:QuantumTest×QuantumTest):ℝ:=
  -6*(sourcePair (G s (matchedTester a.1)) (G s a.2)).re-(n/48)*‖embed (G s (matchedTester a.1))‖^2
def normalizerWorkMean(s:ℝ)(hs:0<s)(w:QuantumTest):ℝ:=
  -6*(fullDefectMean s hs 0 (-(matchedTester w)) w (diagonalAction w)).re-
    6*(commutatorMatchedMean s hs w w).re-(n/48)*(matchedDefectMean s hs w w).re

private theorem price_expansion(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(a:QuantumTest×QuantumTest):
    originalNormalizerPrice s hs x a=gainedNormalizerPrice s a-
      6*(sourcePair (K s hs x (matchedTester a.1)) (HC s hs x a.1)).re-
      6*(sourcePair (HC s hs x a.1) (matchedClockDefect s hs x a.1)).re-
      6*(sourcePair (K s hs x a.2) (matchedClockDefect s hs x a.1)).re-
      (n/24)*(sourcePair (K s hs x (matchedTester a.1)) (matchedClockDefect s hs x a.1)).re-
      (n/48)*(sourcePair (matchedClockDefect s hs x a.1) (matchedClockDefect s hs x a.1)).re:=by
  have hb:(clockSourcePair s hs x a).1=K s hs x a.1:=rfl
  have hf:(clockSourcePair s hs x a).2=K s hs x a.2+HC s hs x a.1:=by
    simp only [clockSourcePair,SourceScalarDoubleCurrent.bracket,Module.End.mul_apply,LinearMap.sub_apply,HC,actualClockDefect]
  have hm:matchedTester (K s hs x a.1)=K s hs x (matchedTester a.1)+matchedClockDefect s hs x a.1:=by
    unfold matchedClockDefect
    module
  have hp:=FiniteCausalSylvester.noether_clock_square n n_pos (embed (matchedTester (clockSourcePair s hs x a).1))
    (embed (clockSourcePair s hs x a).2)
  have hp': -6*(sourcePair (matchedTester (clockSourcePair s hs x a).1) (clockSourcePair s hs x a).2).re-
      (n/48)*‖embed (matchedTester (clockSourcePair s hs x a).1)‖^2=originalNormalizerPrice s hs x a:=by
    simpa only [sourcePair,originalNormalizerPrice] using hp
  rw [←hp',←pair_self,hb,hf,hm]
  have hp1:=pair_re (matchedClockDefect s hs x a.1) (K s hs x a.2)
  have hp2:=pair_re (matchedClockDefect s hs x a.1) (HC s hs x a.1)
  have hp3:=pair_re (matchedClockDefect s hs x a.1) (K s hs x (matchedTester a.1))
  have hb0:=actual_complete_clock_pair s hs x (matchedTester a.1) a.2
  have hb1:(sourcePair (K s hs x (matchedTester a.1)) (K s hs x (matchedTester a.1))).re=
      ‖embed (G s (matchedTester a.1))‖^2:=
    (congrArg Complex.re (actual_complete_clock_pair s hs x (matchedTester a.1) (matchedTester a.1))).trans (pair_self _)
  simp only [sourcePair,map_add,inner_add_left,inner_add_right,Complex.add_re] at hp1 hp2 hp3 hb0 hb1 ⊢
  unfold gainedNormalizerPrice
  simp only [sourcePair] at ⊢
  linear_combination -6*congrArg Complex.re hb0-(n/48)*hb1-6*hp1-6*hp2-(n/48)*hp3

/-- The un-subtracted original normalizer has a complete Gaussian finite update. The original forcing survives only in its gained base; every full-H0 square normalization is removed before estimating the remaining actual commutator current. -/
theorem actual_original_normalizer_gaussian(s:ℝ)(hs:0<s)(a:QuantumTest×QuantumTest):
    Integrable (fun x:ℝ×ℝ=>originalNormalizerPrice s hs x a) γ₂ ∧
    (∫x:ℝ×ℝ,originalNormalizerPrice s hs x a ∂γ₂)=gainedNormalizerPrice s a+normalizerWorkMean s hs a.1:=by
  have hc0:=actual_complete_source_defect_gaussian s hs 0 (-(matchedTester a.1)) a.1 (diagonalAction a.1)
  have he(x:ℝ×ℝ):actualClockDefect s hs x 0 (-(matchedTester a.1))=K s hs x (matchedTester a.1):=by
    simp only [actualClockDefect,map_zero,map_neg,zero_sub,neg_neg]
  simp only [he] at hc0
  have hc1:=actual_full_matched_cross_gaussian s hs a.1 a.1
  have h0:=actual_matched_clock_centered s hs a.2 a.1
  have h1:=actual_matched_clock_centered s hs (matchedTester a.1) a.1
  have hn:=actual_matched_clock_defect_gaussian s hs a.1 a.1
  have ic0:=hc0.1.re
  have ic1:=hc1.1.re
  have i0:=h0.1.re
  have i1:=h1.1.re
  have inn:=hn.1.re
  simp only [RCLike.re_eq_complex_re] at ic0 ic1 i0 i1 inn
  have hi:=(((((integrable_const (gainedNormalizerPrice s a)).sub (ic0.const_mul 6)).sub
    (ic1.const_mul 6)).sub (i0.const_mul 6)).sub (i1.const_mul (n/24))).sub (inn.const_mul (n/48))
  refine ⟨hi.congr (Filter.Eventually.of_forall (fun x=>(price_expansion s hs x a).symm)),?_⟩
  simp_rw [price_expansion]
  erw [integral_sub (((((integrable_const (gainedNormalizerPrice s a)).sub (ic0.const_mul 6)).sub
    (ic1.const_mul 6)).sub (i0.const_mul 6)).sub (i1.const_mul (n/24))) (inn.const_mul (n/48)),
    integral_sub ((((integrable_const (gainedNormalizerPrice s a)).sub (ic0.const_mul 6)).sub
    (ic1.const_mul 6)).sub (i0.const_mul 6)) (i1.const_mul (n/24)),
    integral_sub (((integrable_const (gainedNormalizerPrice s a)).sub (ic0.const_mul 6)).sub (ic1.const_mul 6)) (i0.const_mul 6),
    integral_sub ((integrable_const (gainedNormalizerPrice s a)).sub (ic0.const_mul 6)) (ic1.const_mul 6),
    integral_sub (integrable_const (gainedNormalizerPrice s a)) (ic0.const_mul 6)]
  simp only [integral_const_mul,integral_const,MeasureTheory.probReal_univ,one_smul]
  have hrc0:=Complex.reCLM.integral_comp_comm hc0.1
  have hrc1:=Complex.reCLM.integral_comp_comm hc1.1
  have hr0:=Complex.reCLM.integral_comp_comm h0.1
  have hr1:=Complex.reCLM.integral_comp_comm h1.1
  have hrn:=Complex.reCLM.integral_comp_comm hn.1
  simp only [Complex.reCLM_apply,hc0.2,hc1.2,h0.2,h1.2,hn.2,Complex.zero_re] at hrc0 hrc1 hr0 hr1 hrn
  rw [hrc0,hrc1,hr0,hr1,hrn]
  unfold normalizerWorkMean
  ring

/-- The apparent zero-leg H0-squared mean is exactly a first-H0 work pairing and the original gained source pair. No H0-squared source price is retained. -/
theorem actual_transport_matched_cross(s:ℝ)(hs:0<s)(w:QuantumTest):
    fullDefectMean s hs 0 (-(matchedTester w)) w (diagonalAction w)=
      wholePowerPair s hs (matchedTester w) w-sourcePair (G s (matchedTester w)) (G s (diagonalAction w)):=by
  have hd:=actual_complete_source_defect_gaussian s hs 0 (-(matchedTester w)) w (diagonalAction w)
  have h0(x:ℝ×ℝ):actualClockDefect s hs x 0 (-(matchedTester w))=K s hs x (matchedTester w):=by
    simp only [actualClockDefect,map_zero,map_neg,zero_sub,neg_neg]
  simp only [h0] at hd
  have he(x:ℝ×ℝ):sourcePair (K s hs x (matchedTester w)) (HC s hs x w)=
      sourcePair (K s hs x (matchedTester w)) (diagonalAction (K s hs x w))-
        sourcePair (G s (matchedTester w)) (G s (diagonalAction w)):=by
    have hp(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
      simp only [sourcePair,map_sub,inner_sub_right]
    simp only [HC,actualClockDefect]
    rw [hp,actual_complete_clock_pair]
  rw [←hd.2]
  change (∫x:ℝ×ℝ,sourcePair (K s hs x (matchedTester w)) (HC s hs x w) ∂γ₂)=_
  simp_rw [he]
  have hi:=(actual_corrected_hamiltonian_gaussian s hs (matchedTester w) w).1
  erw [integral_sub hi (integrable_const _)]
  have hp:(∫x:ℝ×ℝ,sourcePair (correctedCompleteCore s hs x.1 x.2 (matchedTester w))
      (diagonalAction (correctedCompleteCore s hs x.1 x.2 w)) ∂γ₂)=wholePowerPair s hs (matchedTester w) w:=
    actual_corrected_hamiltonian_power_source s hs (matchedTester w) w
  rw [hp]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]

private theorem matched_mean_nonnegative(s:ℝ)(hs:0<s)(w:QuantumTest):0≤(matchedDefectMean s hs w w).re:=by
  have hp(v:QuantumTest):0≤(sourcePair v v).re:=by rw [pair_self];positivity
  simp only [matchedDefectMean,Complex.add_re]
  exact add_nonneg (hp _) (hp _)

/-- The original wholeSourceNext receives an internally generated upper price for its actual raw completed-square normalizer. The only new work terms are first-H0 source pairings; the negative matched variance is already paid. -/
theorem actual_whole_source_normalizer_upper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    let a:=wholeSourceNext s hs half advanced m ell F g q
    Integrable (fun x:ℝ×ℝ=>originalNormalizerPrice s hs x a) γ₂ ∧
    (∫x:ℝ×ℝ,originalNormalizerPrice s hs x a ∂γ₂)≤gainedNormalizerPrice s a-
      6*(wholePowerPair s hs (matchedTester a.1) a.1-sourcePair (G s (matchedTester a.1)) (G s (diagonalAction a.1))).re-
      6*(commutatorMatchedMean s hs a.1 a.1).re:=by
  dsimp only
  let a:=wholeSourceNext s hs half advanced m ell F g q
  have h:=actual_original_normalizer_gaussian s hs a
  refine ⟨h.1,?_⟩
  rw [h.2,normalizerWorkMean,actual_transport_matched_cross]
  have hp:0≤(n/48)*(matchedDefectMean s hs a.1 a.1).re:=
    mul_nonneg (div_nonneg n_pos.le (by norm_num)) (matched_mean_nonnegative s hs a.1)
  linarith only [hp]

end LowEnergy.OriginalRCommutatorSource
