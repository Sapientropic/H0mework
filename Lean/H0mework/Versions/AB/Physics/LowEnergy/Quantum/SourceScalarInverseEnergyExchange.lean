import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarInverseLocalization
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarInverseFullSource
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeRetarded
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarBulkResidualBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceScalarInverseEnergyExchange
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare
open SourceHamiltonianVolume SourceHamiltonianScaleJet SourceScalarVirialBulk SourceScalarGaugeScale
open SourceScalarPositiveBulkWard SourceScalarInverseBulk SourceScalarInverseNativeEnergy
open SourceScalarInverseRetardedBudget SourceScalarInverseLocalization SourceScalarInverseFullSource
open SourceScalarInverseInsertion InverseVolumeLocalizationAlgebra SourceMixedNativeReturn
open SourceGammaNativeBudget SourceClosedCostNativeProbe
open SourceMovingJetFlux
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open FullYSourceResolventGraphSplice
open scoped InnerProductSpace BigOperators
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] GaussDiagonalHistory.diagonalAction

private theorem phi_product (A B : End) : deltaPhi (A*B)=deltaPhi A*B+A*deltaPhi B := by
  change phiEulerAction*(A*B)-(A*B)*phiEulerAction=
    (phiEulerAction*A-A*phiEulerAction)*B+A*(phiEulerAction*B-B*phiEulerAction)
  noncomm_ring
private theorem gauge_product (A B : End) : deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B := by
  change SourceGaugeRadialPair.gaugeEulerAction*(A*B)-(A*B)*SourceGaugeRadialPair.gaugeEulerAction=
    (SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)*B+
      A*(SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)
  noncomm_ring
private theorem coframe_product (A B : End) :
    scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  rw [←SourceGaugeCoframeJets.K_commutator,←SourceGaugeCoframeJets.K_commutator,
    ←SourceGaugeCoframeJets.K_commutator]
  noncomm_ring
attribute [local irreducible] SourceScalarVirialBulk.deltaPhi SourceScalarGaugeScale.deltaGauge
  SourceHamiltonianScaleJet.scaleDerivative SourceScalarVirialBulk.positiveBulk
  SourceScalarVirialBulk.vacuumJetCoefficient

private theorem jet_add (A B : End) : inverseWeightedBulkJet (A+B)=
    inverseWeightedBulkJet A+inverseWeightedBulkJet B := by
  simp only [inverseWeightedBulkJet,InverseVolumeWardAlgebra.inverseWard,
    InverseVolumeWardAlgebra.mixedPolynomial,InverseVolumeWardAlgebra.affinePolynomial,
    InverseVolumeWardAlgebra.inverseLocalPolynomial,map_add,map_sub,map_smul,smul_add,smul_sub]
  module
private theorem jordan_add (A B T : End) : jordan (A+B) T=jordan A T+jordan B T := by
  simp only [jordan,add_mul,mul_add,smul_add]
  abel
private theorem jordan_smul (a : ℂ) (A T : End) : jordan (a • A) T=a • jordan A T := by
  simp only [jordan,smul_mul_assoc,mul_smul_comm,←smul_add]
  exact smul_comm _ _ _

def yukawaCorrection (sharp : Bool) (m ell : ℕ) : End :=
  (4 : ℂ) • jordan (inverseVolumeAction*fullAction sharp) (square m ell)+
    (4+3*(vacuumJetCoefficient : ℂ)) •
      jordan (inverseVolumeAction*fullAction sharp) (deltaPhi (square m ell))-
    (3*(vacuumJetCoefficient : ℂ)) •
      jordan (inverseVolumeAction*fullAction sharp) (deltaPhi (deltaPhi (square m ell)))

/-- VY has coframe degree -3. Its cutoff coefficients differ from those of the unweighted Y. -/
theorem original_weighted_yukawa_cutoff (sharp : Bool) (m ell : ℕ) :
    inverseWeightedBulkJet (jordan (inverseVolumeAction*fullAction sharp) (square m ell))=
      yukawaCorrection sharp m ell := by
  let A : End := inverseVolumeAction*fullAction sharp
  have hp : deltaPhi A=A := by
    dsimp only [A]
    rw [phi_product,inverse_phi,original_full_affine_jet,zero_mul,zero_add]
  have hg : deltaGauge A=0 := by
    dsimp only [A]
    rw [gauge_product,inverse_gauge,original_full_gauge_jet,zero_mul,mul_zero,add_zero]
  have hc : scaleDerivative A=(-3 : ℂ) • A := by
    dsimp only [A]
    rw [coframe_product,inverse_coframe,original_full_coframe_jet,mul_zero,add_zero,smul_mul_assoc]
  have hl : InverseVolumeWardAlgebra.inverseLocalPolynomial scaleDerivative A=(-3 : ℂ) • A := by
    simp only [InverseVolumeWardAlgebra.inverseLocalPolynomial,hc,map_smul]
    module
  have hfirst : firstContact deltaPhi deltaGauge scaleDerivative (vacuumJetCoefficient : ℂ) A=
      (4+3*(vacuumJetCoefficient : ℂ)) • A := by
    simp only [firstContact,gaugePolynomial,hg,hl,hp,map_zero,map_smul,smul_zero,zero_sub]
    module
  have hsecond : secondContact scaleDerivative (vacuumJetCoefficient : ℂ) A=
      (-3*(vacuumJetCoefficient : ℂ)) • A := by
    rw [secondContact,hl,smul_smul]
    congr 1
    ring
  have h := inverse_ward_jordan (R := End) deltaPhi deltaGauge scaleDerivative (vacuumJetCoefficient : ℂ)
    phi_product gauge_product coframe_product A (square m ell)
    (original_square_gauge m ell) (original_square_coframe m ell) (original_square_mixed m ell)
  change inverseWeightedBulkJet (jordan A (square m ell))=
    jordan (inverseWeightedBulkJet A) (square m ell)+
      jordan (firstContact deltaPhi deltaGauge scaleDerivative (vacuumJetCoefficient : ℂ) A)
        (deltaPhi (square m ell))+
      jordan (secondContact scaleDerivative (vacuumJetCoefficient : ℂ) A)
        (deltaPhi (deltaPhi (square m ell))) at h
  have hw : inverseWeightedBulkJet A=(4 : ℂ) • A := original_inverse_weighted_full_jet sharp
  rw [hw,hfirst,hsecond,jordan_smul,jordan_smul,jordan_smul] at h
  exact h.trans (by dsimp only [yukawaCorrection,A];module)

def wholeWard (sharp : Bool) (m ell : ℕ) : End :=
  inverseWeightedBulkJet (jordan (inverseFullSymmetricScale sharp) (square m ell))

/-- Both original H0+Y branches return the complete signed localized source word. -/
theorem original_full_localized_exchange (sharp : Bool) (m ell : ℕ) :
    wholeWard sharp m ell=
      jordan (inverseVolumeAction*positiveBulk) (square m ell)+
      jordan firstSourceContact (deltaPhi (square m ell))+
      jordan secondSourceContact (deltaPhi (deltaPhi (square m ell)))+
      yukawaCorrection sharp m ell := by
  have hs : inverseFullSymmetricScale sharp=inverseSymmetricScale+inverseVolumeAction*fullAction sharp := by
    unfold inverseFullSymmetricScale inverseSymmetricScale
    rw [add_mul,mul_add,(original_full_inverse_commute sharp).eq]
    module
  rw [wholeWard,hs,jordan_add,jet_add,original_weighted_yukawa_cutoff]
  change inverseWeightedBulkJet (symmetricCutoff m ell)+yukawaCorrection sharp m ell=_
  rw [original_inverse_square_localization]

private theorem theta_inverse (m ell : ℕ) : Commute (theta m ell) inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (SourceNativeCutoffContact.theta m ell z : ℂ) (reciprocalVolume z : ℂ) (f z)
private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (theta m ell g)=sourcePair (theta m ell f) g := multiply_pair _ _ _ _
private theorem square_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (square m ell g)=sourcePair (square m ell f) g := by
  change sourcePair f (theta m ell (theta m ell g))=sourcePair (theta m ell (theta m ell f)) g
  rw [theta_pair,theta_pair]
private theorem inverse_theta (m ell : ℕ) (f : QuantumTest) :
    inverseVolumeAction (theta m ell f)=theta m ell (inverseVolumeAction f) :=
  (LinearMap.congr_fun (theta_inverse m ell).eq f).symm
private theorem contact_inverse (i : ScalarIndex) (m ell : ℕ) (f : QuantumTest) :
    SourceNativeCutoffContact.contactAction (scalarDirection i) m ell (inverseVolumeAction f)=
      inverseVolumeAction (SourceNativeCutoffContact.contactAction (scalarDirection i) m ell f) := by
  apply DFunLike.ext
  intro z
  exact map_smul (SourceNativeCutoffContact.contactFiber (scalarDirection i) m ell z)
    (reciprocalVolume z : ℂ) (f z)

def inverseContact (m ell : ℕ) (p q : QuantumTest) : ℂ :=
  (4*(sourceTime 0 : ℂ))*∑ i : ScalarIndex,sourcePair
    (inverseVolumeAction (SourceNativeCutoffContact.contactAction (scalarDirection i) m ell p))
    (inverseVolumeAction (SourceNativeCutoffContact.contactAction (scalarDirection i) m ell q))

/-- Native70 IMS is transported on both original inverse-volume legs before any real part is taken. -/
theorem original_inverse_bilinear_ims (m ell : ℕ) (p q : QuantumTest) :
    sourcePair (theta m ell p) (inverseWeightedBulkJet inverseSymmetricScale (theta m ell q))=
      sourcePair p (jordan (inverseVolumeAction*positiveBulk) (square m ell) q)+inverseContact m ell p q := by
  have h := SourceScalarBulkResidualBudget.original_bulk_bilinear_ims m ell
    (inverseVolumeAction p) (inverseVolumeAction q)
  simp only [SourceScalarBulkResidualBudget.T] at h
  change sourcePair (theta m ell (inverseVolumeAction p))
    (volumeAction (positiveBulk (theta m ell (inverseVolumeAction q))))=
      (1/2 : ℂ)*(sourcePair (theta m ell (theta m ell (inverseVolumeAction p)))
        (volumeAction (positiveBulk (inverseVolumeAction q)))+
        sourcePair (inverseVolumeAction p)
          (volumeAction (positiveBulk (theta m ell (theta m ell (inverseVolumeAction q))))))+
      SourceScalarBulkResidualBudget.contactPair m ell (inverseVolumeAction p) (inverseVolumeAction q) at h
  simp only [←inverse_theta] at h
  rw [←inverse_bulk_pair_return,←inverse_bulk_pair_return,←inverse_bulk_pair_return] at h
  have hc : SourceScalarBulkResidualBudget.contactPair m ell (inverseVolumeAction p) (inverseVolumeAction q)=
      inverseContact m ell p q := by
    simp only [SourceScalarBulkResidualBudget.contactPair,SourceScalarBulkResidualBudget.C,
      contact_inverse,inverseContact]
  rw [hc] at h
  have hj : sourcePair p (jordan (inverseVolumeAction*positiveBulk) (square m ell) q)=
      (1/2 : ℂ)*(sourcePair (theta m ell (theta m ell p))
        (inverseWeightedBulkJet inverseSymmetricScale q)+sourcePair p
        (inverseWeightedBulkJet inverseSymmetricScale (theta m ell (theta m ell q)))) := by
    rw [←original_inverse_bulk_symmetric_jet]
    simp only [jordan,LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,
      sourcePair,map_smul,map_add,inner_smul_right,inner_add_right]
    have hs := square_pair m ell p (inverseWeightedBulkJet inverseSymmetricScale q)
    simp only [sourcePair] at hs
    rw [hs]
    simp only [square,Module.End.mul_apply]
    ring
  exact h.trans (by rw [hj])

def signedPair (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) : ℂ :=
  sourcePair p (wholeWard sharp m ell q)-sourcePair p (yukawaCorrection sharp m ell q)-
    sourcePair p (jordan firstSourceContact (deltaPhi (square m ell)) q)-
    sourcePair p (jordan secondSourceContact (deltaPhi (deltaPhi (square m ell))) q)+
    inverseContact m ell p q

/-- All source jets, full Yukawa contacts and inverse-weighted IMS terms remain in one polarized identity. -/
theorem original_pair_exchange (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    signedPair sharp m ell p q=
      sourcePair (theta m ell p) (inverseWeightedBulkJet inverseSymmetricScale (theta m ell q)) := by
  rw [signedPair,original_full_localized_exchange,original_inverse_bilinear_ims]
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right]
  ring

theorem original_diagonal_energy_exchange (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    (signedPair sharp m ell f f).re=inverseForm (theta m ell f) := by
  rw [original_pair_exchange]
  rfl

/-- The two source frequencies and both original g/k inputs are retained. This polarized value need not be positive. -/
theorem actual_two_leg_exchange (sharp : Bool) (m ell : ℕ) (F : Index)
    (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0) (g k : diagonal.domain) :
    signedPair sharp m ell (state F zl hl k) (state F zr hr g)=
      resolvedBulk F zl zr hl hr g k (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell) := by
  rw [original_pair_exchange]
  exact actual_inverse_bulk_ward F zl zr hl hr g k (theta m ell) (theta m ell)

/-- The original Gamma and moving current consume the actual diagonal signed exchange; no energy or tail certificate is supplied. -/
theorem actual_gamma_energy_exchange (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    4*sourceTime 0*‖sourceGamma sharp m ell F g k z+Complex.I*inner ℂ (k : H)
      ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
        orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))‖^2 ≤
      ‖-96*(sourceTime 0 : ℂ)^2‖^2*‖(k : H)‖^2*‖finiteResolvent F z‖^2*coefficientCost sharp*
        ((signedPair sharp m ell (state F z hz g) (state F z hz g)).re+
          2*sourceTime 0*‖vacuum‖^2*‖embed (theta m ell (state F z hz g))‖^2) := by
  rw [actual_two_leg_exchange]
  simpa only [theta,SourceNativeCutoffContact.theta_action_polynomial,
    SourceMixedNativeReturn.thetaAction] using! actual_resolved_gamma_bound sharp m ell F z hz g k

end LowEnergy.SourceScalarInverseEnergyExchange
