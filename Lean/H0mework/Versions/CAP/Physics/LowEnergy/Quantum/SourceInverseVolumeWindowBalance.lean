import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeContactPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseWindowBalance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory SourcePhysicalKineticSquare
open SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarGaugeScale
open SourceScalarInverseEnergyExchange SourceScalarInverseLocalization
open SourceScalarInverseRetardedBudget SourceInverseFullResponse
open SourceInverseContactHardy InverseVolumeWardAlgebra InverseVolumeLocalizationAlgebra
attribute [local irreducible] GaussDiagonalHistory.diagonalAction
  InverseVolumeWardAlgebra.inverseWard SourceScalarPositiveBulkWard.pairDelta
  SourceInverseFullResponse.fullResolvedPair SourceInverseFullResponse.localizedResponse
  SourceScalarPositiveBulkWard.state SourceScalarPositiveBulkWard.resolvedBulk
  SourcePhysicalKineticSquare.inverseVolumeAction SourceScalarVirialBulk.vacuumJetCoefficient
  SourceScalarVirialBulk.deltaPhi SourceScalarInverseRetardedBudget.square
  GaussFockPair.sourcePair SourceScalarInverseEnergyExchange.yukawaCorrection
  SourceScalarInverseLocalization.firstSourceContact SourceScalarInverseLocalization.secondSourceContact
  InverseVolumeLocalizationAlgebra.jordan SourceScalarInverseEnergyExchange.inverseContact

/-- The literal full dynamic source word retains both defects, full frequency, Y and the two affine contacts. -/
def dynamicRemainder (sharp : Bool) (m ell : ℕ) (F : Index)
    (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0) (g k : diagonal.domain) : ℂ :=
  let p := state F zl hl k
  let q := state F zr hr g
  inverseWard (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe) (vacuumJetCoefficient : ℂ)
      (localizedResponse m ell (fullResolvedPair sharp F zl zr hl hr g k)) 1 1-
    sourcePair p (yukawaCorrection sharp m ell q)-
    sourcePair p (jordan firstSourceContact (deltaPhi (square m ell)) q)-
    sourcePair p (jordan secondSourceContact (deltaPhi (deltaPhi (square m ell))) q)

/-- The contact term is extracted from the existing whole two-frequency equation without separating defect legs. -/
theorem actual_dynamic_exchange (sharp : Bool) (m ell : ℕ) (F : Index)
    (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0) (g k : diagonal.domain) :
    dynamicRemainder sharp m ell F zl zr hl hr g k+
      inverseContact m ell (state F zl hl k) (state F zr hr g)=
      resolvedBulk F zl zr hl hr g k (inverseVolumeAction*theta m ell)
        (inverseVolumeAction*theta m ell) := by
  have h := actual_signed_dynamic_response sharp m ell F zl zr hl hr g k
  simpa only [dynamicRemainder] using! h

/-- The original dynamic word generates its two-window energy update with the source coefficient 72/3481. -/
theorem actual_diagonal_energy_balance (sharp : Bool) (m ell : ℕ)
    (hm : 1 ≤ m) (hell : m ≤ ell) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    (signedPair sharp m ell (state F z hz g) (state F z hz g)).re ≤
      (dynamicRemainder sharp m ell F z z hz hz g g).re+(72/3481 : ℝ)*
        ((signedPair sharp (m/2) m (state F z hz g) (state F z hz g)).re+
          (signedPair sharp (ell/2) ell (state F z hz g) (state F z hz g)).re) := by
  have he := actual_dynamic_exchange sharp m ell F z z hz hz g g
  rw [←actual_two_leg_exchange sharp m ell F z z hz hz g g] at he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re] at hr
  have hc := actual_signed_contact_window sharp m ell hm hell F z hz g
  linarith only [hr,hc]

end LowEnergy.SourceInverseWindowBalance
