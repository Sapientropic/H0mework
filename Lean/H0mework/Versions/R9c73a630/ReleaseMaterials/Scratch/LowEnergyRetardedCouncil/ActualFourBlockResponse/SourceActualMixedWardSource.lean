import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardTail
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCompressionShape

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedWardSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk
open SourceResolventBandLimit FullYSourceResolventGraphSplice ActualMixedCovarianceTail ActualMixedWindowGram
open SourceNativeCutoffContact ActualMixedWardTail ActualMixedCompressionShape ActualMixedResolventWard
open ActualVectorJointCost MeasureTheory Filter
open Lean Meta Elab Term
open scoped InnerProductSpace ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

elab "paid_mixed_inverse%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedResolventWard 0) "LowEnergy") "ActualMixedResolventWard"
  let name:=Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing original mixed inverse proof"
  mkConstWithFreshMVarLevels name

private theorem gauge_inverse (F:Index)(z:ℂ)(hz:z.im≠0) :
    deltaGauge (resolventCore F z hz)=
      -resolventCore F z hz*deltaGauge (compressionCore F)*resolventCore F z hz := by
  rw [(paid_mixed_inverse% gauge_comm),(paid_mixed_inverse% gauge_comm)]
  have hi:=(paid_mixed_inverse% actual_inverse) F z hz
  have h:=(paid_mixed_inverse% inverse_comm) (compressionCore F-z • (1:End))
    (resolventCore F z hz) Gauge hi.1 hi.2
  simpa only [(paid_mixed_inverse% comm_spectral)] using h

private theorem difference_inverse (F:Index)(z:ℂ)(hz:z.im≠0) :
    deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)=
      -resolventCore F z hz*(deltaPhi (compressionCore F)-deltaGauge (compressionCore F))*resolventCore F z hz := by
  rw [(paid_mixed_inverse% difference_comm),(paid_mixed_inverse% difference_comm)]
  have hi:=(paid_mixed_inverse% actual_inverse) F z hz
  have h:=(paid_mixed_inverse% inverse_comm) (compressionCore F-z • (1:End))
    (resolventCore F z hz) (Phi-Gauge) hi.1 hi.2
  simpa only [(paid_mixed_inverse% comm_spectral)] using h

/-- The source bulk, all graded projection-shape terms, and the two ordered mixed
insertions belong to one original resolvent flux. -/
def sourceFlux (F:Index)(z:ℂ)(hz:z.im≠0) : End :=
  let R:=resolventCore F z hz
  let G:=deltaGauge (compressionCore F)
  let K:=deltaPhi (compressionCore F)-deltaGauge (compressionCore F);
  R*(coreCompression F (secondJet diagonalAction)+wholeShape F)*R+
    R*G*R*K*R+R*K*R*G*R

/-- This uses the actual graded pinching, not a replacement support-space PHP. -/
theorem actual_source_flux (F:Index)(z:ℂ)(hz:z.im≠0) :
    secondJet (resolventCore F z hz)= -sourceFlux F z hz := by
  have h:=actual_mixed_inverse F z hz
  dsimp only at h
  rw [actual_second_compression_shape] at h
  unfold sourceFlux
  linear_combination (norm:=noncomm_ring) h

/-- Every original complex cross term and every projection-shape component stays
inside this signed source current before any estimate. -/
def sourceCurrent (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest) : ℝ :=
  let R:=resolventCore F z hz
  let G:=deltaGauge (compressionCore F)
  let K:=deltaPhi (compressionCore F)-deltaGauge (compressionCore F);
  -2*(sourcePair (thetaAction m ell ((R*G*R) g)) (thetaAction m ell ((R*K*R) g))).re-
    2*(sourcePair (coreWindow m ell F z hz g) (thetaAction m ell (sourceFlux F z hz g))).re

/-- The complete original source current is the generated moving mixed Ward current. -/
theorem actual_source_current (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest) :
    sourceCurrent m ell F z hz g=wardCurrent m ell F z hz g := by
  have he:embed (thetaAction m ell (deltaGauge (resolventCore F z hz) g))+
      embed (thetaAction m ell ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g))=
        embed (thetaAction m ell (deltaPhi (resolventCore F z hz) g)) := by
    simp only [LinearMap.sub_apply,map_sub]
    abel
  have hn:=norm_add_sq (𝕜:=ℂ)
    (embed (thetaAction m ell (deltaGauge (resolventCore F z hz) g)))
    (embed (thetaAction m ell ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g)))
  rw [he] at hn
  change ‖embed (thetaAction m ell (deltaPhi (resolventCore F z hz) g))‖^2=_+
    2*(sourcePair (thetaAction m ell (deltaGauge (resolventCore F z hz) g))
      (thetaAction m ell ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g))).re+_ at hn
  have hp:sourcePair (thetaAction m ell (deltaGauge (resolventCore F z hz) g))
      (thetaAction m ell ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g))=
    sourcePair (thetaAction m ell ((resolventCore F z hz*deltaGauge (compressionCore F)*resolventCore F z hz) g))
      (thetaAction m ell ((resolventCore F z hz*(deltaPhi (compressionCore F)-deltaGauge (compressionCore F))*resolventCore F z hz) g)) := by
    rw [difference_inverse,gauge_inverse]
    simp only [neg_mul,LinearMap.neg_apply,map_neg,sourcePair,inner_neg_left,inner_neg_right,neg_neg]
  rw [hp] at hn
  dsimp only [sourceCurrent,wardCurrent]
  rw [actual_source_flux]
  simp only [LinearMap.neg_apply,map_neg,sourcePair,inner_neg_right,Complex.neg_re] at hn ⊢
  linarith only [hn]

private theorem causal_nonreal (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ) :
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

/-- The whole source bulk/shape/cross current has an absolute common causal tail.
Its summands have not been assigned independent budgets or signs. -/
theorem actual_source_current_causal_tail (μ:ℝ)(hμ:0 < μ)(g:QuantumTest) :
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal |sourceCurrent m ell F (causalFrequency advanced μ w)
          (causal_nonreal advanced μ hμ w) g|) ≤ ENNReal.ofReal ε := by
  simpa only [actual_source_current] using actual_ward_causal_tail μ hμ g

end LowEnergy.ActualMixedWardSource
