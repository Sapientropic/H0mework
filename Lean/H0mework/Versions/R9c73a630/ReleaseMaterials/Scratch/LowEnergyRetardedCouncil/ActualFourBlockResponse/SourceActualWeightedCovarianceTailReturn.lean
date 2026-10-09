import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualWeightedWardInputSplit
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovariancePairTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualWeightedCovarianceTailReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceClockYukawaCubicCurrent SourceClockPhiSecondBulk SourcePhysicalKineticSquare
open SourceNativeCutoffContact SourceResolventBandLimit ActualVectorJointCost ActualMixedCovarianceTail
open ActualWeightedWardInputSplit ActualMixedCovariancePairTail ActualInverseCurrentCoframeReturn
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] resolventCore secondJet weightedCovariance coreCovariance

/-- This is precisely the one source correction in the weighted input split. -/
def mixedCoframeCorrection (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):End :=
  secondJet (coreCovariance m ell F z hz*compressedCurrent F*resolventCore F z hz)

private theorem weighted_split (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    secondJet (weightedCovariance m ell F z hz)=
      secondJet (coreCovariance m ell F z hz)*inverseVolumeAction+mixedCoframeCorrection m ell F z hz := by
  rw [actual_weighted_second_covariance_input]
  have he:resolventCore F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz)*
      thetaAction m ell*thetaAction m ell*coframeFlux F z hz=
      coreCovariance m ell F z hz*compressedCurrent F*resolventCore F z hz := by
    unfold coreCovariance coframeFlux compressedCurrent
    noncomm_ring
  rw [he]
  rfl

/-- The fixed Ug source price and the complete own-coframe correction share the
same actual weighted covariance; no correction term is separated or discarded. -/
theorem actual_weighted_pair_return (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f g:QuantumTest):
    sourcePair f (secondJet (weightedCovariance m ell F z hz) g)-
      sourcePair f (mixedCoframeCorrection m ell F z hz g)=
        sourcePair f (secondJet (coreCovariance m ell F z hz) (inverseVolumeAction g)) := by
  rw [weighted_split]
  simp only [LinearMap.add_apply,Module.End.mul_apply,sourcePair,map_add,inner_add_right]
  abel

private theorem causal_nonreal (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

/-- The original fixed inverse-volume input is paid by the six ordered source
jets before m, ell, F, frequency and either causal sign are chosen. -/
theorem actual_weighted_pair_causal_tail_return (μ:ℝ)(hμ:0 < μ)(f g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖
          sourcePair f (secondJet (weightedCovariance m ell F (causalFrequency advanced μ w)
            (causal_nonreal advanced μ hμ w)) g)-
          sourcePair f (mixedCoframeCorrection m ell F (causalFrequency advanced μ w)
            (causal_nonreal advanced μ hμ w) g)‖)≤ENNReal.ofReal ε := by
  simpa only [actual_weighted_pair_return] using
    actual_covariance_pair_causal_tail μ hμ f (inverseVolumeAction g)

end LowEnergy.ActualWeightedCovarianceTailReturn
