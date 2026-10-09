import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedVariancePower
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRMatchedVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiHeatLocalNativeGaussian OriginalRCommutatorSource FirstCurrentWholeVariance
open ClockPhiHeatCorrectedCovarianceSource FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier
open FirstCurrentJointBudget SourceScalarDoubleCurrent SourceLocalizedInverseFormPayment MeasureTheory Filter
open scoped Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev M:End:=matchedTester
private abbrev n:ℝ:=sourceTime 0
private abbrev K(s:ℝ)(hs:0<s)(x:ℝ×ℝ):End:=correctedCompleteCore s hs x.1 x.2
private abbrev G(s:ℝ):End:=SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ₂:=γ.prod γ
attribute [local irreducible] sourcePair embed diagonalAction matchedTester correctedCompleteCore combinedGenerator gaussianProfileWeight inverseRootAction inverseVolumeAction matchedDefectMean sourceTime
private theorem n_pos:0<n:=by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only [sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem pair_re(f g:QuantumTest):(sourcePair f g).re=(sourcePair g f).re:=by
  have h:=congrArg Complex.re (GaussNativeForm.pair_conjugate f g)
  simpa only [Complex.conj_re] using h
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]

def matchedRadialDebit(s:ℝ)(hs:0<s)(w:QuantumTest):ℝ:=
  (3*n/8)*s*‖embed (gaussianProfileWeight s hs (-5/6) (inverseRootAction (U (D w))))‖^2+
  (27*n/8)*s^2*‖embed (gaussianProfileWeight s hs (-5/6) (U (U (D w))))‖^2
private theorem radial_debit_source(s:ℝ)(hs:0<s)(w:QuantumTest):
    (n/48)*(matchedDefectMean s hs w w).re=matchedRadialDebit s hs w:=by
  have h:=congrArg Complex.re (actual_matched_variance_radial_squares s hs w w)
  simp only [←Complex.ofReal_pow,Complex.add_re,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,zero_mul,mul_zero,zero_add,sub_zero,pair_norm] at h
  calc
    _=(n/48)*((18*s)*‖embed (gaussianProfileWeight s hs (-5/6) (inverseRootAction (U (D w))))‖^2+
        (162*s^2)*‖embed (gaussianProfileWeight s hs (-5/6) (U (U (D w))))‖^2):=congrArg (fun v:ℝ=>(n/48)*v) h
    _=_:=by unfold matchedRadialDebit;ring

theorem actual_matched_radial_debit_nonnegative(s:ℝ)(hs:0<s)(w:QuantumTest):0 ≤ matchedRadialDebit s hs w:=by
  unfold matchedRadialDebit
  have hn:=n_pos
  positivity

/-- This is precisely the literal frequency-M and negative M-square department of physicalJointKernel. -/
def matchedPhysicalClockPrice(s:ℝ)(hs:0<s)(z:ℂ)(x:ℝ×ℝ)(w:QuantumTest):ℝ:=
  6*(sourcePair (M (K s hs x w)) (z • K s hs x w)).re-(n/48)*‖embed (M (K s hs x w))‖^2
def gainedMatchedPhysicalPrice(s:ℝ)(z:ℂ)(w:QuantumTest):ℝ:=
  6*(sourcePair (G s (M w)) (z • G s w)).re-(n/48)*‖embed (G s (M w))‖^2
private theorem matched_price_source(s:ℝ)(hs:0<s)(z:ℂ)(x:ℝ×ℝ)(w:QuantumTest):
    matchedPhysicalClockPrice s hs z x w=gainedMatchedPhysicalPrice s z w+
      6*(sourcePair (K s hs x (z • w)) (matchedClockDefect s hs x w)).re-
      (n/24)*(sourcePair (K s hs x (M w)) (matchedClockDefect s hs x w)).re-
      (n/48)*(sourcePair (matchedClockDefect s hs x w) (matchedClockDefect s hs x w)).re:=by
  have hm:M (K s hs x w)=K s hs x (M w)+matchedClockDefect s hs x w:=by
    unfold matchedClockDefect
    module
  have h0:=(congrArg Complex.re (actual_complete_clock_pair s hs x (M w) (z • w)))
  have h1:=(congrArg Complex.re (actual_complete_clock_pair s hs x (M w) (M w)))
  have h2:=pair_re (matchedClockDefect s hs x w) (K s hs x (z • w))
  have h3:=pair_re (matchedClockDefect s hs x w) (K s hs x (M w))
  unfold matchedPhysicalClockPrice gainedMatchedPhysicalPrice
  rw [←pair_norm,←pair_norm,hm]
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_add_right,Complex.add_re] at h0 h1 h2 h3 ⊢
  linear_combination 6*h0-(n/48)*h1+6*h2-(n/48)*h3

/-- The actual affine M return centers all linear noise before estimating the remaining source price. -/
theorem actual_matched_physical_gaussian(s:ℝ)(hs:0<s)(z:ℂ)(w:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>matchedPhysicalClockPrice s hs z x w) γ₂ ∧
    (∫x:ℝ×ℝ,matchedPhysicalClockPrice s hs z x w ∂γ₂)=
      gainedMatchedPhysicalPrice s z w-matchedRadialDebit s hs w:=by
  have hz:=actual_matched_clock_centered s hs (z • w) w
  have hm:=actual_matched_clock_centered s hs (M w) w
  have hn:=actual_matched_clock_defect_gaussian s hs w w
  have iz:=hz.1.re
  have im:=hm.1.re
  have inn:=hn.1.re
  simp only [RCLike.re_eq_complex_re] at iz im inn
  have hi:=(((integrable_const (gainedMatchedPhysicalPrice s z w)).add (iz.const_mul 6)).sub
    (im.const_mul (n/24))).sub (inn.const_mul (n/48))
  refine ⟨hi.congr (Eventually.of_forall (fun x=>(matched_price_source s hs z x w).symm)),?_⟩
  simp_rw [matched_price_source]
  erw [integral_sub (((integrable_const _).add (iz.const_mul 6)).sub (im.const_mul (n/24))) (inn.const_mul (n/48)),
    integral_sub ((integrable_const _).add (iz.const_mul 6)) (im.const_mul (n/24)),
    integral_add (integrable_const _) (iz.const_mul 6)]
  simp only [integral_const_mul,integral_const,MeasureTheory.probReal_univ,one_smul]
  have hz':=Complex.reCLM.integral_comp_comm hz.1
  have hm':=Complex.reCLM.integral_comp_comm hm.1
  have hn':=Complex.reCLM.integral_comp_comm hn.1
  simp only [Complex.reCLM_apply,hz.2,hm.2,hn.2,Complex.zero_re] at hz' hm' hn'
  rw [hz',hm',hn',radial_debit_source]
  ring

private theorem complete_source_matched_payment(s:ℝ)(hs:0<s)(z:ℂ)(x:ℝ×ℝ)(w f:QuantumTest)
    (he:diagonalAction w=f+z • w):
    originalNormalizerPrice s hs x (w,f)+
      6*(sourcePair (M (K s hs x w)) (diagonalAction (K s hs x w))).re=matchedPhysicalClockPrice s hs z x w:=by
  let b:=clockSourcePair s hs x (w,f)
  have hb:diagonalAction b.1=b.2+z • b.1:=by
    simp only [b,clockSourcePair,bracket,Module.End.mul_apply,LinearMap.sub_apply,he,map_add,map_smul]
    module
  have hp:=FiniteCausalSylvester.noether_clock_square n n_pos (embed (M b.1)) (embed b.2)
  have hp':originalNormalizerPrice s hs x (w,f)=
      -6*(sourcePair (M b.1) b.2).re-(n/48)*‖embed (M b.1)‖^2:=by
    simpa only [sourcePair,originalNormalizerPrice,b] using hp.symm
  rw [hp']
  change -6*(sourcePair (M b.1) b.2).re-(n/48)*‖embed (M b.1)‖^2+
    6*(sourcePair (M b.1) (diagonalAction b.1)).re=
    6*(sourcePair (M b.1) (z • b.1)).re-(n/48)*‖embed (M b.1)‖^2
  rw [hb,pair_add_r,Complex.add_re]
  ring

/-- The original full forcing and full H0 work cancel together, so neither an H0-squared common budget nor a separate commutator cross bound remains in the literal physical matched department. -/
theorem actual_full_source_normalizer_payment(s:ℝ)(hs:0<s)(z:ℂ)(w f:QuantumTest)(he:diagonalAction w=f+z • w):
    let p:=fun x:ℝ×ℝ=>originalNormalizerPrice s hs x (w,f)+
      6*(sourcePair (M (K s hs x w)) (diagonalAction (K s hs x w))).re
    Integrable p γ₂ ∧ (∫x:ℝ×ℝ,p x ∂γ₂)=gainedMatchedPhysicalPrice s z w-matchedRadialDebit s hs w:=by
  simpa only [complete_source_matched_payment s hs z _ w f he] using actual_matched_physical_gaussian s hs z w

/-- Direct consumer of the original wholeSourceNext, with its actual own-cutoff forcing and both causal frequencies retained. -/
theorem actual_original_whole_source_normalizer_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)
    (F:Index)(g:diagonal.domain)(q:ℝ):
    let z:=SourceLocalizedInverseFormPayment.actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=wholeSourceNext s hs half advanced m ell F g q
    let p:=fun x:ℝ×ℝ=>originalNormalizerPrice s hs x a+
      6*(sourcePair (M (K s hs x a.1)) (diagonalAction (K s hs x a.1))).re
    Integrable p γ₂ ∧ (∫x:ℝ×ℝ,p x ∂γ₂)=gainedMatchedPhysicalPrice s z a.1-matchedRadialDebit s hs a.1:=by
  dsimp only
  exact actual_full_source_normalizer_payment s hs _ _ _
    (((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.1)

private theorem gained_matched_upper(s:ℝ)(z:ℂ)(w:QuantumTest):
    gainedMatchedPhysicalPrice s z w≤(432/n)*‖embed (G s (z • w))‖^2:=by
  have h:=FiniteCausalSylvester.noether_clock_square n n_pos (embed (G s (M w))) (-(embed (G s (z • w))))
  have hp:0≤(n/48)*‖embed (G s (M w))+((144/n:ℝ):ℂ) • (-(embed (G s (z • w))))‖^2:=
    mul_nonneg (div_nonneg n_pos.le (by norm_num)) (sq_nonneg _)
  simp only [inner_neg_right,Complex.neg_re,norm_neg] at h
  have he:(sourcePair (G s (M w)) (z • G s w)).re=
      (inner ℂ (embed (G s (M w))) (embed (G s (z • w)))).re:=by
    simp only [sourcePair,map_smul]
  unfold gainedMatchedPhysicalPrice
  rw [he]
  linarith only [h,hp]

/-- The remaining upper price is the gained shifted source state. The complete radial negative price is retained, and no full-forcing square budget is introduced. -/
theorem actual_whole_source_matched_shifted_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)
    (F:Index)(g:diagonal.domain)(q:ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=wholeSourceNext s hs half advanced m ell F g q
    (∫x:ℝ×ℝ,matchedPhysicalClockPrice s hs z x a.1 ∂γ₂)≤
      (432/n)*‖embed (G s (z • a.1))‖^2-matchedRadialDebit s hs a.1:=by
  dsimp only
  rw [(actual_matched_physical_gaussian s hs _ _).2]
  exact sub_le_sub_right (gained_matched_upper s _ _) _
end LowEnergy.OriginalRMatchedVariance
