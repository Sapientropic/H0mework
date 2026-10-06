import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeAlgebra
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScalarPositiveBulkWard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarInverseBulk
open GaussCoreHilbert GaussCoreDifferential GaussNativeForm GaussNativeEnergy GaussDiagonalHistory
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume
open SourcePhysicalKineticSquare SourceHamiltonianScaleJet SourceScalarVirialBulk
open SourceScalarGaugeScale SourceScalarPositiveBulkWard
-- Match source laws without unfolding the generated Hamiltonian.
attribute [local irreducible] GaussDiagonalHistory.diagonalAction

abbrev End := SourceScalarGaugeScale.End

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

private theorem volume_right : volumeAction*inverseVolumeAction=(1 : End) := by
  apply LinearMap.ext
  exact volume_inverse

private theorem volume_left : inverseVolumeAction*volumeAction=(1 : End) := by
  have h : Commute inverseVolumeAction volumeAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (reciprocalVolume z : ℂ) (volume z : ℂ) (f z)
  exact h.eq.trans volume_right

private theorem volume_coframe : scaleDerivative volumeAction=(3 : ℂ) • volumeAction := by
  change (3*Complex.I/2) • (dilation*volumeAction-volumeAction*dilation)=_
  rw [SourceDilationKinetic.volume_scale_current,smul_smul]
  congr 1
  calc (3*Complex.I/2)*(-2*Complex.I) = -3*(Complex.I*Complex.I) := by ring
       _ = 3 := by rw [Complex.I_mul_I]; ring

theorem inverse_phi : deltaPhi inverseVolumeAction=0 := by
  simpa only [neg_zero,zero_smul] using
    InverseVolumeWardAlgebra.inverse_derivative (R := End) deltaPhi phi_product volumeAction inverseVolumeAction
      0 volume_right volume_left (by simpa only [zero_smul] using original_volume_phi)

theorem inverse_gauge : deltaGauge inverseVolumeAction=0 := by
  simpa only [neg_zero,zero_smul] using
    InverseVolumeWardAlgebra.inverse_derivative (R := End) deltaGauge gauge_product volumeAction inverseVolumeAction
      0 volume_right volume_left (by simpa only [zero_smul] using original_volume_gauge)

theorem inverse_coframe : scaleDerivative inverseVolumeAction=(-3 : ℂ) • inverseVolumeAction :=
  InverseVolumeWardAlgebra.inverse_derivative (R := End) scaleDerivative coframe_product volumeAction
    inverseVolumeAction 3 volume_right volume_left volume_coframe

private theorem current_phi : deltaPhi (diagonalAction*volumeAction-volumeAction*diagonalAction)=0 := by
  rw [full_source_volume_current,map_smul,original_dilation_phi,smul_zero]

private theorem current_gauge : deltaGauge (diagonalAction*volumeAction-volumeAction*diagonalAction)=0 := by
  rw [full_source_volume_current,map_smul,original_dilation_gauge,smul_zero]

private theorem current_coframe : scaleDerivative (diagonalAction*volumeAction-volumeAction*diagonalAction)=0 := by
  have h : scaleDerivative dilation=0 := by
    change (3*Complex.I/2) • (dilation*dilation-dilation*dilation)=0
    rw [sub_self,smul_zero]
  rw [full_source_volume_current,map_smul,h,smul_zero]

def inverseSymmetricScale : End :=
  (1/2 : ℂ) • (diagonalAction*inverseVolumeAction+inverseVolumeAction*diagonalAction)

def inverseWeightedBulkJet (A : End) : End :=
  InverseVolumeWardAlgebra.inverseWard deltaPhi deltaGauge scaleDerivative
    (vacuumJetCoefficient : ℂ) A

theorem original_inverse_volume_current_weight :
    scaleDerivative (diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction)=
      (-6 : ℂ) • (diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction) :=
  InverseVolumeWardAlgebra.inverse_current_weight (R := End) scaleDerivative coframe_product diagonalAction
    volumeAction inverseVolumeAction volume_right volume_left inverse_coframe current_coframe

attribute [local irreducible] SourceScalarVirialBulk.deltaPhi SourceScalarGaugeScale.deltaGauge
  SourceHamiltonianScaleJet.scaleDerivative SourceScalarVirialBulk.positiveBulk

/-- The same source H0 and exact inverse volume generate a bulk with no positive volume weight. -/
theorem original_inverse_bulk_symmetric_jet :
    inverseWeightedBulkJet inverseSymmetricScale=inverseVolumeAction*positiveBulk := by
  have h := InverseVolumeWardAlgebra.inverse_symmetric_ward (R := End) deltaPhi deltaGauge scaleDerivative
    (vacuumJetCoefficient : ℂ) phi_product gauge_product coframe_product diagonalAction
    volumeAction inverseVolumeAction volume_right volume_left
    inverse_phi inverse_gauge inverse_coframe current_phi current_gauge current_coframe
  have source : InverseVolumeWardAlgebra.ward deltaPhi deltaGauge scaleDerivative
      (vacuumJetCoefficient : ℂ) diagonalAction=positiveBulk := by
    change filteredBulk+(vacuumJetCoefficient : ℂ) • vacuumJet=positiveBulk
    exact original_positive_bulk_source_jet
  change inverseWeightedBulkJet inverseSymmetricScale=
    inverseVolumeAction*InverseVolumeWardAlgebra.ward deltaPhi deltaGauge scaleDerivative
      (vacuumJetCoefficient : ℂ) diagonalAction at h
  exact h.trans (congrArg (fun A : End => inverseVolumeAction*A) source)

end LowEnergy.SourceScalarInverseBulk
