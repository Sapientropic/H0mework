import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaugeClockReturnSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseGaugeOuterPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceCoframeVolume SourceScalarShiftedBulk SourceScalarEssentialBudget
open SourceQuantumConfigurationHilbert SourceScalarDoubleCurrent SourceClockPhiNormalizedScalarBudget
open FirstCurrentElectricSuccessor
open SourceClockPhiNativeJointPayment FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open ClockPhiHeatCorrectedCovarianceSource ReverseNativeOuterSource
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev B:End:=scalarBulkComplete
private abbrev V:End:=volumeAction
private abbrev X:End:=weightedElectricCurrent
private def shiftedVolume(t:ℝ):End:=V-((18*t:ℝ):ℂ) • (1:End)
attribute [local irreducible] sourcePair embed scalarBulkComplete correctedCompleteCore wholeStep wholeSourceMap wholeSourceNext normalizedState normalizedForcing frequencyState scalarEnergy
  ReverseNativeFrequencyWard.wholeClockState wholeOuterNoetherPrice wholeOuterSource reverseInputVector reverseForceInput
private theorem pair_add_right(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_real_left(r:ℝ)(f g:QuantumTest):sourcePair ((r:ℂ) • f) g=(r:ℂ)*sourcePair f g:=by
  simp [sourcePair]
private theorem pair_real_right(r:ℝ)(f g:QuantumTest):sourcePair f ((r:ℂ) • g)=(r:ℂ)*sourcePair f g:=by
  simp [sourcePair]
private theorem pair_complex_left(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem shifted_pair(t:ℝ)(f g:QuantumTest):
    sourcePair f (shiftedVolume t g)=sourcePair (shiftedVolume t f) g:=by
  have hv:sourcePair f (V g)=sourcePair (V f) g:=multiply_pair _ _ _ _
  unfold sourcePair at hv ⊢
  simp only [shiftedVolume,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,map_sub,map_smul,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  rw [hv]
private theorem shifted_square_pair(t:ℝ)(f g:QuantumTest):
    sourcePair f ((shiftedVolume t*shiftedVolume t) g)=sourcePair ((shiftedVolume t*shiftedVolume t) f) g:=
  (shifted_pair t f (shiftedVolume t g)).trans (shifted_pair t (shiftedVolume t f) g)
private theorem shifted_commutes(t:ℝ):
    Commute G (shiftedVolume t) ∧ Commute B (shiftedVolume t):=by
  constructor
  · have h:=actual_gauge_volume_commute.eq
    unfold shiftedVolume
    change G*(V-((18*t:ℝ):ℂ) • (1:End))=(V-((18*t:ℝ):ℂ) • (1:End))*G
    linear_combination (norm:=noncomm_ring) h
  · have h:=actual_volume_scalar_commute.eq
    unfold shiftedVolume
    change B*(V-((18*t:ℝ):ℂ) • (1:End))=(V-((18*t:ℝ):ℂ) • (1:End))*B
    linear_combination (norm:=noncomm_ring) -h
private theorem shifted_scalar_skew(t:ℝ)(u:QuantumTest):
    (sourcePair ((shiftedVolume t*shiftedVolume t) (G u)) (B u)).re=0:=by
  let W:End:=shiftedVolume t*shiftedVolume t
  have hGW:G*W=W*G:=by
    have h:=(shifted_commutes t).1.eq
    dsimp only [W]
    linear_combination (norm:=noncomm_ring) h*shiftedVolume t+shiftedVolume t*h
  have hBW:B*W=W*B:=by
    have h:=(shifted_commutes t).2.eq
    dsimp only [W]
    linear_combination (norm:=noncomm_ring) h*shiftedVolume t+shiftedVolume t*h
  have hGB:=actual_gauge_scalar_commute.eq
  have hmove:G*(W*B)=W*B*G:=by
    linear_combination (norm:=noncomm_ring) hGW*B+W*hGB
  have hp:sourcePair (W (G u)) (B u)= -sourcePair (B u) (W (G u)):=by
    calc
      _=sourcePair (G u) (W (B u)):=(shifted_square_pair t (G u) (B u)).symm
      _= -sourcePair u (G (W (B u))):=actual_gauge_pair u (W (B u))
      _= -sourcePair u (W (B (G u))):=congrArg (fun v:QuantumTest=> -sourcePair u v) (LinearMap.congr_fun hmove u)
      _= -sourcePair u (B (W (G u))):=by
        exact congrArg (fun v:QuantumTest=> -sourcePair u v) (LinearMap.congr_fun hBW (G u)).symm
      _= -sourcePair (B u) (W (G u)):=congrArg Neg.neg (original_scalar_pair u (W (G u)))
  have hs:(sourcePair (B u) (W (G u))).re=(sourcePair (W (G u)) (B u)).re:=by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) (embed (B u)) (embed (W (G u)))
  have hr:=congrArg Complex.re hp
  simp only [Complex.neg_re] at hr
  change (sourcePair (W (G u)) (B u)).re=0
  linarith
private theorem clock_volume_square(t:ℝ)(ht:0<t)(ξ η:ℝ):
    correctedCompleteCore t ht ξ η*(V*V*G)=
      (shiftedVolume t*shiftedVolume t*G)*correctedCompleteCore t ht ξ η:=by
  let K:End:=correctedCompleteCore t ht ξ η
  have hv:K*V=shiftedVolume t*K:=by
    simpa only [shiftedVolume,Complex.ofReal_mul,Complex.ofReal_ofNat] using actual_complete_volume_input t ht ξ η
  have hg:K*G=G*K:=(actual_complete_gauge_commute t ht ξ η).eq.symm
  change K*(V*V*G)=(shiftedVolume t*shiftedVolume t*G)*K
  calc
    _=(K*V)*V*G:=rfl
    _=(shiftedVolume t*K)*V*G:=by rw [hv]
    _=shiftedVolume t*(K*V)*G:=rfl
    _=shiftedVolume t*(shiftedVolume t*K)*G:=by rw [hv]
    _=(shiftedVolume t*shiftedVolume t)*(K*G):=rfl
    _=(shiftedVolume t*shiftedVolume t)*(G*K):=by rw [hg]
    _=_:=rfl

/-- The original gauge part of the balanced electric source has identically zero scalar work on one actual clocked leg. This is a source pairing identity at every noise point. -/
theorem actual_clocked_gauge_scalar_zero(t:ℝ)(ht:0<t)(ξ η:ℝ)(w:QuantumTest):
    (sourcePair (correctedCompleteCore t ht ξ η ((V^2*G) w))
      (B (correctedCompleteCore t ht ξ η w))).re=0:=by
  have h:=LinearMap.congr_fun (clock_volume_square t ht ξ η) w
  change correctedCompleteCore t ht ξ η ((V^2*G) w)=
    (shiftedVolume t*shiftedVolume t) (G (correctedCompleteCore t ht ξ η w)) at h
  rw [h]
  exact shifted_scalar_skew t _

/-- The actual selected electric endpoint kills the linear gauge term before estimation. Its complete remaining contribution is the quadratic same-source cross. -/
theorem actual_clocked_gauge_electric_quadratic(t:ℝ)(ht:0<t)(ξ η h:ℝ)(w:QuantumTest):
    (sourcePair (correctedCompleteCore t ht ξ η ((h:ℂ) • (V^2*G) w))
      (B (correctedCompleteCore t ht ξ η (w+(h:ℂ) • X w)))).re=
    h^2*(sourcePair (correctedCompleteCore t ht ξ η ((V^2*G) w))
      (B (correctedCompleteCore t ht ξ η (X w)))).re:=by
  simp only [map_add,map_smul,pair_add_right,pair_real_left,pair_real_right,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.add_re]
  rw [actual_clocked_gauge_scalar_zero]
  ring

/-- The whole-source electric step uses exactly the same h_F, frequency state and complete clock as the paid outer Noether price. -/
theorem actual_whole_outer_gauge_quadratic(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    (sourcePair (correctedCompleteCore t ht x.1 x.2
      ((wholeStep t ht half advanced m ell F g:ℂ) • (V^2*G) (frequencyState half advanced m ell F g q)))
      (B (correctedCompleteCore t ht x.1 x.2 ((wholeSourceNext t ht half advanced m ell F g q).1)))).re=
    (wholeStep t ht half advanced m ell F g)^2*
      (sourcePair (correctedCompleteCore t ht x.1 x.2 ((V^2*G) (frequencyState half advanced m ell F g q)))
        (B (correctedCompleteCore t ht x.1 x.2 (X (frequencyState half advanced m ell F g q))))).re:=by
  have hw:(wholeSourceNext t ht half advanced m ell F g q).1=
      frequencyState half advanced m ell F g q+
        (wholeStep t ht half advanced m ell F g:ℂ) • X (frequencyState half advanced m ell F g q):=by
    unfold wholeSourceNext
    simp only [electricSourceDirection,Prod.fst_add]
    rfl
  rw [hw]
  exact actual_clocked_gauge_electric_quadratic t ht x.1 x.2 _ _

private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private abbrev Hz(half advanced:Bool)(q:ℝ):
    (SourceLocalizedInverseFormPayment.actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  ReverseNativeFrequencyWard.reverse_frequency_nonreal advanced (sourceNoetherFrequency half) (frequency_positive half) q
private theorem pair_add_left(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by
  simp only [sourcePair,map_add,inner_add_left]

/-- The complete paid outer Noether price now has no linear gauge term. The original electric step and full two-seed compression-force remainder are retained together with the exact quadratic gauge cross. -/
theorem actual_whole_outer_noether_gauge_elimination(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    let z:=SourceLocalizedInverseFormPayment.actualFrequency advanced (sourceNoetherFrequency half) q
    let w:=frequencyState half advanced m ell F g q
    let h:=wholeStep t ht half advanced m ell F g
    let K:=correctedCompleteCore t ht x.1 x.2
    let u:=ReverseNativeFrequencyWard.wholeClockState t ht half advanced m ell F g x q
    wholeOuterNoetherPrice t ht half advanced m ell F g x q=
      18*scalarEnergy u+36*h*(sourcePair (K (X w)) (B u)).re-
        36*h^2*(sourcePair (K ((V^2*G) w)) (B (K (X w)))).re-
        2*(sourcePair (K (wholeSourceMap t ht half advanced m ell F g
          (reverseInputVector m ell F z (Hz half advanced q) g-reverseForceInput m ell F z (Hz half advanced q) g)))
          (B u)).re:=by
  dsimp only
  let w:=frequencyState half advanced m ell F g q
  let h:=wholeStep t ht half advanced m ell F g
  let K:=correctedCompleteCore t ht x.1 x.2
  let u:=ReverseNativeFrequencyWard.wholeClockState t ht half advanced m ell F g x q
  have hu:u=K ((wholeSourceNext t ht half advanced m ell F g q).1):=by
    unfold u ReverseNativeFrequencyWard.wholeClockState
    rfl
  have hs:wholeOuterSource t ht half advanced m ell F g q=
      (-18:ℂ) • ((h:ℂ) • X w)+(18:ℂ) • ((h:ℂ) • (V^2*G) w)+
      wholeSourceMap t ht half advanced m ell F g
        (reverseInputVector m ell F (SourceLocalizedInverseFormPayment.actualFrequency advanced (sourceNoetherFrequency half) q)
          (Hz half advanced q) g-
        reverseForceInput m ell F (SourceLocalizedInverseFormPayment.actualFrequency advanced (sourceNoetherFrequency half) q)
          (Hz half advanced q) g):=by
    rw [actual_whole_outer_source_return]
    dsimp only [w,h]
    module
  have hg:(sourcePair (K ((h:ℂ) • (V^2*G) w)) (B u)).re=
      h^2*(sourcePair (K ((V^2*G) w)) (B (K (X w)))).re:=by
    rw [hu]
    simpa only [K,h,w] using actual_whole_outer_gauge_quadratic t ht half advanced m ell F g x q
  unfold wholeOuterNoetherPrice
  change 18*scalarEnergy u-2*(sourcePair (K (wholeOuterSource t ht half advanced m ell F g q)) (B u)).re=_
  rw [hs]
  simp only [map_add,map_smul,pair_add_left,pair_complex_left,Complex.add_re]
  norm_num [Complex.star_def,Complex.mul_re]
  have hg2:(sourcePair (K ((V^2*G) w)) (B u)).re*h=
      h^2*(sourcePair (K ((V^2*G) w)) (B (K (X w)))).re:=by
    simp only [map_smul,pair_real_left,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hg
    nlinarith only [hg]
  dsimp only [K,h,w,u] at hg2 ⊢
  simp only [Module.End.mul_apply] at hg2
  nlinarith only [hg2]
end LowEnergy.ReverseGaugeOuterPayment
