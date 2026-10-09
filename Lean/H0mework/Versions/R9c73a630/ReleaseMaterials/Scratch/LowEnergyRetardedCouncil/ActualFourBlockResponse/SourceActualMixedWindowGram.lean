import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovarianceCore
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualAffineCutoffCausalTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedWindowGram
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk GaussCoframeForm
open SourceResolventBandLimit FullYSourceResolventGraphSplice ActualMixedCovarianceTail
open SourceScalarAffineCutoffTail ActualAffineCutoffCausalTail
open Lean Meta Elab Term
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

elab "paid_mixed_gram%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovarianceGram 0) "LowEnergy") "ActualMixedCovarianceGram"
  let name:=Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing original mixed Gram proof"
  mkConstWithFreshMVarLevels name
elab "paid_mixed_core%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovarianceCore 0) "LowEnergy") "ActualMixedCovarianceTail"
  let name:=Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing actual returned covariance proof"
  mkConstWithFreshMVarLevels name

def coreWindow (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0) : End :=
  SourceNativeCutoffContact.thetaAction m ell*resolventCore F z hz
private theorem star_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
private def dualWindow (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0) : End :=
  resolventCore F (star z) (star_nonreal z hz)*SourceNativeCutoffContact.thetaAction m ell

private theorem window_pair(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0) :
    Paired (dualWindow m ell F z hz) (coreWindow m ell F z hz) := by
  intro f g
  simp only [dualWindow,coreWindow,Module.End.mul_apply]
  rw [(paid_mixed_core% resolvent_pair) F z hz]
  exact GaussNativeForm.multiply_pair _ _ _ _

private theorem window_product(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0) :
    coreCovariance m ell F z hz=dualWindow m ell F z hz*coreWindow m ell F z hz := by
  unfold coreCovariance dualWindow coreWindow
  simp only [mul_assoc]

/-- The exact mixed Gram belongs to the same cutoff covariance whose absolute tail
has been generated. The two ordered source cross terms are not separated. -/
theorem actual_window_gram(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest) :
    let W:=coreWindow m ell F z hz
    ‖embed (deltaGauge W g)‖^2+‖embed ((deltaPhi W-deltaGauge W) g)‖^2=
      ‖embed (deltaPhi W g)‖^2-2*(sourcePair (W g) (secondJet W g)).re+
        (sourcePair g (secondJet (coreCovariance m ell F z hz) g)).re := by
  dsimp only
  have hp : sourcePair g (secondJet (coreCovariance m ell F z hz) g)=
      sourcePair (secondJet (coreWindow m ell F z hz) g) (coreWindow m ell F z hz g)+
      sourcePair (coreWindow m ell F z hz g) (secondJet (coreWindow m ell F z hz) g)-
      sourcePair (deltaGauge (coreWindow m ell F z hz) g)
        ((deltaPhi (coreWindow m ell F z hz)-deltaGauge (coreWindow m ell F z hz)) g)-
      sourcePair ((deltaPhi (coreWindow m ell F z hz)-deltaGauge (coreWindow m ell F z hz)) g)
        (deltaGauge (coreWindow m ell F z hz) g) := by
    rw [window_product,(paid_mixed_gram% second_product)]
    have h:=window_pair m ell F z hz
    have hG:=(paid_mixed_gram% paired_gauge) _ _ h
    have hP:=(paid_mixed_gram% paired_phi) _ _ h
    have hS:=(paid_mixed_gram% paired_second) _ _ h
    simp only [Paired,sourcePair] at h hG hP hS
    simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,
      sourcePair,map_add,map_sub,inner_add_right,inner_sub_right,inner_sub_left,h,hG,hP,hS]
  have h:=congrArg Complex.re hp
  have swap(f k:QuantumTest):(sourcePair f k).re=(sourcePair k f).re := by
    simpa only [sourcePair,Complex.star_def,Complex.conj_re] using
      congrArg Complex.re (inner_conj_symm (𝕜:=ℂ) (embed k) (embed f))
  simp only [Complex.add_re,Complex.sub_re] at h
  rw [swap (secondJet (coreWindow m ell F z hz) g),
    swap ((deltaPhi (coreWindow m ell F z hz)-deltaGauge (coreWindow m ell F z hz)) g)] at h
  have hn:=norm_add_sq (𝕜:=ℂ) (embed (deltaGauge (coreWindow m ell F z hz) g))
    (embed ((deltaPhi (coreWindow m ell F z hz)-deltaGauge (coreWindow m ell F z hz)) g))
  have he:embed (deltaGauge (coreWindow m ell F z hz) g)+
      embed ((deltaPhi (coreWindow m ell F z hz)-deltaGauge (coreWindow m ell F z hz)) g)=
        embed (deltaPhi (coreWindow m ell F z hz) g) := by
    simp only [LinearMap.sub_apply,map_sub]
    abel
  rw [he] at hn
  change ‖embed (deltaPhi (coreWindow m ell F z hz) g)‖^2=_+
    2*(sourcePair (deltaGauge (coreWindow m ell F z hz) g)
      ((deltaPhi (coreWindow m ell F z hz)-deltaGauge (coreWindow m ell F z hz)) g)).re+_ at hn
  linarith only [h,hn]

private theorem derivations_commute(A:End) : deltaGauge (deltaPhi A)=deltaPhi (deltaGauge A) := by
  rw [←SourceGaugeScaleTransport.generator_commutator,
    ←SourceScalarAffineScaleTransport.generator_commutator,
    ←SourceScalarAffineScaleTransport.generator_commutator,
    ←SourceGaugeScaleTransport.generator_commutator]
  have hc:=SourceScalarAffineMixedJets.generators_affine_gauge.eq
  have hL:=congrArg (fun X:End=>X*A) hc
  have hR:=congrArg (fun X:End=>A*X) hc
  linear_combination (norm:=noncomm_ring) -hL+hR

/-- Gauge variation of the true affine cutoff contact vanishes by the two original
commuting source flows, including the affine vacuum term. -/
theorem actual_gauge_affine_cutoff_zero(m ell:ℕ) : deltaGauge (affineCutoff m ell)=0 := by
  rw [affineCutoff,derivations_commute,actual_gauge_cutoff_zero]
  exact deltaPhi.map_zero

/-- The mixed return keeps the moving gauge-resolvent input. The separately paid
fixed-input affine contact is not substituted for this third term. -/
theorem actual_window_mixed_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0) :
    secondJet (coreWindow m ell F z hz)=
      affineCutoff m ell*resolventCore F z hz+
      SourceNativeCutoffContact.thetaAction m ell*secondJet (resolventCore F z hz)-
      affineCutoff m ell*deltaGauge (resolventCore F z hz) := by
  have hs:secondJet (SourceNativeCutoffContact.thetaAction m ell)=affineCutoff m ell := by
    change (deltaPhi (SourceNativeCutoffContact.thetaAction m ell)-
      deltaGauge (SourceNativeCutoffContact.thetaAction m ell))-
      deltaGauge (deltaPhi (SourceNativeCutoffContact.thetaAction m ell)-
        deltaGauge (SourceNativeCutoffContact.thetaAction m ell))=_
    rw [actual_gauge_cutoff_zero,sub_zero,show deltaPhi (SourceNativeCutoffContact.thetaAction m ell)=
      affineCutoff m ell from rfl,actual_gauge_affine_cutoff_zero,sub_zero]
  rw [coreWindow,(paid_mixed_gram% second_product),hs,actual_gauge_cutoff_zero,
    zero_mul,sub_zero,sub_zero]
  rfl

end LowEnergy.ActualMixedWindowGram
