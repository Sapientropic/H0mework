import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeBulk
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarInverseInsertion
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseFullAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.SourceScalarInverseFullSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory
open GaussNativePotential GaussNativeForm SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceMixedNativeReturn SourceScalarVirialBulk SourceScalarGaugeScale
open SourcePhysicalKineticSquare
open SourceHamiltonianScaleJet SourceScalarInverseBulk SourceScalarInverseInsertion
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
abbrev End := SourceScalarGaugeScale.End

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
attribute [local irreducible] SourceScalarVirialBulk.vacuumJetCoefficient

private theorem jet_add (A B : End) :
    inverseWeightedBulkJet (A+B)=inverseWeightedBulkJet A+inverseWeightedBulkJet B := by
  simp only [inverseWeightedBulkJet,InverseVolumeWardAlgebra.inverseWard,
    InverseVolumeWardAlgebra.mixedPolynomial,InverseVolumeWardAlgebra.affinePolynomial,
    InverseVolumeWardAlgebra.inverseLocalPolynomial,map_add,map_sub,map_smul,
    smul_add,smul_sub]
  module

/-- The inverse normal coefficient comes from the actual source volume weights. -/
theorem original_inverse_normal_jet :
    inverseWeightedBulkJet inverseVolumeAction=
      (-6*(vacuumJetCoefficient : ℂ)) • inverseVolumeAction := by
  have h := InverseVolumeFullAlgebra.source_weight (R := End) deltaPhi deltaGauge scaleDerivative
    (vacuumJetCoefficient : ℂ) 0 (-3) inverseVolumeAction
    (by simpa only [zero_smul] using inverse_phi) inverse_gauge inverse_coframe
  have he : (4*(0 : ℂ)+(vacuumJetCoefficient : ℂ)*(0^2-3*0+2)*
      ((-3 : ℂ)^3+12*(-3)^2+44*(-3)+48))= -6*(vacuumJetCoefficient : ℂ) := by ring
  rw [he] at h
  exact h

theorem original_full_inverse_commute (sharp : Bool) :
    Commute (fullAction sharp) inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (reciprocalVolume z : ℂ) (f z)
  · exact map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (reciprocalVolume z : ℂ) (f z)

/-- Multiplying by the same V retains the full source Yukawa insertion coefficient. -/
theorem original_inverse_weighted_full_jet (sharp : Bool) :
    inverseWeightedBulkJet (inverseVolumeAction*fullAction sharp)=
      (4 : ℂ) • (inverseVolumeAction*fullAction sharp) := by
  have hp : deltaPhi (inverseVolumeAction*fullAction sharp)=
      inverseVolumeAction*fullAction sharp := by
    rw [phi_product,inverse_phi,original_full_affine_jet,zero_mul,zero_add]
  have hg : deltaGauge (inverseVolumeAction*fullAction sharp)=0 := by
    rw [gauge_product,inverse_gauge,original_full_gauge_jet,zero_mul,mul_zero,add_zero]
  have hc : scaleDerivative (inverseVolumeAction*fullAction sharp)=
      (-3 : ℂ) • (inverseVolumeAction*fullAction sharp) := by
    rw [coframe_product,inverse_coframe,original_full_coframe_jet,
      mul_zero,add_zero,smul_mul_assoc]
  have h := InverseVolumeFullAlgebra.source_weight (R := End) deltaPhi deltaGauge scaleDerivative
    (vacuumJetCoefficient : ℂ) 1 (-3) (inverseVolumeAction*fullAction sharp)
    (by simpa only [one_smul] using hp) hg hc
  have he : (4*(1 : ℂ)+(vacuumJetCoefficient : ℂ)*(1^2-3*1+2)*
      ((-3 : ℂ)^3+12*(-3)^2+44*(-3)+48))=4 := by ring
  rw [he] at h
  exact h

def inverseFullSymmetricScale (sharp : Bool) : End :=
  (1/2 : ℂ) • ((diagonalAction+fullAction sharp)*inverseVolumeAction+
    inverseVolumeAction*(diagonalAction+fullAction sharp))

/-- The complete original H0+Y has its nonzero signed source term on each independent branch. -/
theorem original_full_inverse_bulk (sharp : Bool) :
    inverseWeightedBulkJet (inverseFullSymmetricScale sharp)=
      inverseVolumeAction*positiveBulk+
        (4 : ℂ) • (inverseVolumeAction*fullAction sharp) := by
  have hs : inverseFullSymmetricScale sharp=
      inverseSymmetricScale+inverseVolumeAction*fullAction sharp := by
    unfold inverseFullSymmetricScale inverseSymmetricScale
    rw [add_mul,mul_add,(original_full_inverse_commute sharp).eq]
    module
  rw [hs,jet_add,original_inverse_bulk_symmetric_jet,
    original_inverse_weighted_full_jet]

end LowEnergy.SourceScalarInverseFullSource
