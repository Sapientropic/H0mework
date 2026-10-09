import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardPositivePrice
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeEndpoint
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeRetarded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualWeightedWardFrequencyReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeForm SourceCoframeVolume
open SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceScalarVirialBulk SourceScalarPositiveBulkWard
open SourceScalarInverseBulk SourceScalarInverseNativeEnergy SourceScalarPairedTransport
open SourceScalarPositiveBulkEndpoint SourceClockYukawaCubicCurrent
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceRelativePowerTail
open ActualMixedWardPositivePrice ActualVectorJointCost SourceMixedNativeReturn
open Lean Meta Elab Term
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev T (m ell:ℕ) : End := SourceNativeCutoffContact.thetaAction m ell
attribute [local irreducible] sourcePair state resolvedBulk fixedBulk defectBulk
  inverseForm inverseWeightedBulkJet inverseSymmetricScale compressionCore

def weightedPair (m ell:ℕ)(p q:QuantumTest) : ℂ :=
  sourcePair (T m ell p) (inverseVolumeAction (T m ell q))

private theorem compression_state (F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain) :
    compressionCore F (state F z hz g)=coreEquiv.symm g+z • state F z hz g := by
  have h:=actual_raised_source F z hz g (1:End)
  simp only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,
    zero_add,defectAction,LinearMap.sub_apply] at h
  linear_combination (norm:=module) h

private theorem fixed_bulk_return (m ell:ℕ)(F:Index)(zl zr:ℂ)(hl:zl.im≠0)(hr:zr.im≠0)
    (g k:diagonal.domain) :
    fixedBulk F zl zr hl hr g k (inverseVolumeAction*T m ell) (inverseVolumeAction*T m ell)=
      (-3*(vacuumJetCoefficient:ℂ))*(weightedPair m ell (coreEquiv.symm k) (state F zr hr g)+
        weightedPair m ell (state F zl hl k) (coreEquiv.symm g)) := by
  have h:=congrArg (fun P:PairMatrix=>P (inverseVolumeAction*T m ell) (inverseVolumeAction*T m ell))
    (actual_fixed_bulk_collapse F zl zr hl hr g k)
  change fixedBulk F zl zr hl hr g k (inverseVolumeAction*T m ell) (inverseVolumeAction*T m ell)=
    (-6*(vacuumJetCoefficient:ℂ))*((1/2:ℂ)*(
      sourcePair (inverseVolumeAction (T m ell (coreEquiv.symm k)))
        (volumeAction (inverseVolumeAction (T m ell (state F zr hr g))))+
      sourcePair (volumeAction (inverseVolumeAction (T m ell (state F zl hl k))))
        (inverseVolumeAction (T m ell (coreEquiv.symm g))))) at h
  rw [volume_inverse,volume_inverse] at h
  have hp:sourcePair (inverseVolumeAction (T m ell (coreEquiv.symm k))) (T m ell (state F zr hr g))=
    weightedPair m ell (coreEquiv.symm k) (state F zr hr g) := (multiply_pair _ _ _ _).symm
  rw [hp] at h
  change _=(-6*(vacuumJetCoefficient:ℂ))*((1/2:ℂ)*(_+weightedPair m ell (state F zl hl k) (coreEquiv.symm g))) at h
  exact h.trans (by ring)

/-- This complete current retains U, both original spectral legs and all raised
coframe/source defects. The fixed and explicit frequency terms are merged first. -/
def weightedCurrent (m ell:ℕ)(F:Index)(zl zr:ℂ)(hl:zl.im≠0)(hr:zr.im≠0)
    (g k:diagonal.domain) : ℂ :=
  defectBulk F zl zr hl hr g k (inverseVolumeAction*T m ell) (inverseVolumeAction*T m ell)-
    (3*(vacuumJetCoefficient:ℂ))*(
      weightedPair m ell (compressionCore F (state F zl hl k)) (state F zr hr g)+
      weightedPair m ell (state F zl hl k) (compressionCore F (state F zr hr g)))

/-- The actual fixed-source forcing and complete complex frequency term cancel
through CF q=g+zq, before any potentially nonintegrable term is separated. -/
theorem actual_weighted_frequency_return (m ell:ℕ)(F:Index)(zl zr:ℂ)(hl:zl.im≠0)(hr:zr.im≠0)
    (g k:diagonal.domain) :
    resolvedBulk F zl zr hl hr g k (inverseVolumeAction*T m ell) (inverseVolumeAction*T m ell)=
      weightedCurrent m ell F zl zr hl hr g k := by
  rw [actual_inverse_bulk_normal,fixed_bulk_return]
  have he:weightedPair m ell (compressionCore F (state F zl hl k)) (state F zr hr g)+
      weightedPair m ell (state F zl hl k) (compressionCore F (state F zr hr g))=
    weightedPair m ell (coreEquiv.symm k) (state F zr hr g)+
      weightedPair m ell (state F zl hl k) (coreEquiv.symm g)+
      (star zl+zr)*weightedPair m ell (state F zl hl k) (state F zr hr g) := by
    rw [compression_state,compression_state]
    simp only [weightedPair,sourcePair,map_add,map_smul,inner_add_left,inner_add_right,
      inner_smul_left,inner_smul_right,starRingEnd_apply]
    ring
  unfold weightedCurrent
  rw [he]
  change _-3*(vacuumJetCoefficient:ℂ)*(star zl+zr)*weightedPair m ell (state F zl hl k) (state F zr hr g)=_
  ring

/-- The full merged same-frequency current is exactly the original positive
inverse-volume Ward energy, not a new assigned positive form. -/
theorem actual_weighted_current_energy (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain) :
    (weightedCurrent m ell F z z hz hz g g).re=inverseForm (T m ell (state F z hz g)) := by
  have h:=actual_inverse_bulk_ward F z z hz hz g g (T m ell) (T m ell)
  have h0:=actual_weighted_frequency_return m ell F z z hz hz g g
  have h1:=congrArg Complex.re (h.trans h0)
  unfold inverseForm
  exact h1.symm

theorem actual_weighted_current_nonnegative (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain) :
    0 ≤ (weightedCurrent m ell F z z hz hz g g).re := by
  rw [actual_weighted_current_energy]
  exact original_inverse_nonnegative _

/-- The original reader-free two-R output consumes the complete weighted source
current directly. No weighted-family or supplied current bound is required. -/
theorem actual_weighted_two_resolvent_price (advanced sharp:Bool)(m ell:ℕ)(F:Index)
    (μ:ℝ)(hμ:0 < μ)(g:diagonal.domain)(w:ℝ) :
    let z:=causalFrequency advanced μ w
    let hz:=ActualVectorBulkSourcePrice.causal_nonreal advanced μ hμ w
    ‖finiteResolvent F z (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g:H)))‖^2 ≤
      (μ⁻¹^2*ActualVectorBulkSourcePrice.formCoefficient sharp)*(weightedCurrent m ell F z z hz hz g g).re+
      (μ⁻¹^2*ActualVectorBulkSourcePrice.normCoefficient sharp)*‖embed (T m ell (state F z hz g))‖^2 := by
  dsimp only
  rw [actual_weighted_current_energy]
  exact ActualVectorBulkSourcePrice.actual_two_resolvent_source_price advanced sharp m ell F μ hμ g w

end LowEnergy.ActualWeightedWardFrequencyReturn
