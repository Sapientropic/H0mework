import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronPhysicalTransfer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.JointOriginalResolventPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronPhysicalJointInverse
open SourceQuantumConfigurationHilbert GaussCoreDifferential CanonicalGradedSpatialSource
open GaussCoreHilbert GaussHistoryHilbert
open ActualCompositeFieldCurrent ActualElectronPhysicalNormalization
open PreparationVacuumJointFieldResponse PreparationVacuumActionFieldLift
open ActualCompositeGaugeBand ActualCompositeOriginWard CanonicalGradedCharge
open PreparationPhysicalPhaseGaugeRealization ActualSourceMixed289ResponseOwn
open scoped InnerProductSpace
attribute [local irreducible] jointResolvent jointGenerator embed

def actualElectronPhysicalSeed (leg : CompositeLeg) : H :=embed (actualElectronAmputatedLeg leg)

theorem actual_electron_physical_seed_norm (leg : CompositeLeg) : ‖actualElectronPhysicalSeed leg‖=1 :=
  actual_electron_amputated_norm leg

theorem actual_electron_physical_seed_charge (leg : CompositeLeg) :
    chargeReader sourcePhaseGaugeLie (actualElectronPhysicalSeed leg)=
      (if leg.dual then (-1:ℂ) else 1) • actualElectronPhysicalSeed leg := by
  rw [actualElectronPhysicalSeed,chargeReader_core,←composite_charge_original,
    actual_electron_amputated_charge,map_smul]

theorem actual_electron_joint_inverse_left (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) : jointResolvent p F z 0*jointGenerator p F z 0=1 := by
  unfold jointResolvent
  exact Ring.inverse_mul_cancel _ (jointGenerator_unit p F z nonreal)

theorem actual_electron_joint_inverse_right (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) : jointGenerator p F z 0*jointResolvent p F z 0=1 := by
  unfold jointResolvent
  exact Ring.mul_inverse_cancel _ (jointGenerator_unit p F z nonreal)

def actualElectronJointOutput (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ)
    (leg : CompositeLeg) : H :=
  jointResolvent p F z 0 (embed (compositeInput leg))

def actualElectronPhysicalResponse (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ)
    (leg : CompositeLeg) : H :=jointResolvent p F z 0 (actualElectronPhysicalSeed leg)

theorem actual_electron_physical_response_original (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (leg : CompositeLeg) :
    actualElectronPhysicalResponse p F z leg=
      actualElectronInputInverseNorm leg • actualElectronJointOutput p F z leg := by
  rw [actualElectronPhysicalResponse,actualElectronPhysicalSeed,actual_electron_amputated_source,map_smul,map_smul]
  rfl

theorem actual_electron_physical_response_equation (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (leg : CompositeLeg) :
    jointGenerator p F z 0 (actualElectronPhysicalResponse p F z leg)=actualElectronPhysicalSeed leg :=
  congrArg (fun A : H→L[ℂ]H=>A (actualElectronPhysicalSeed leg)) (actual_electron_joint_inverse_right p F z nonreal)

theorem actual_electron_physical_response_nonzero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (leg : CompositeLeg) :actualElectronPhysicalResponse p F z leg≠0 := by
  intro zero
  have eq := actual_electron_physical_response_equation p F z nonreal leg
  rw [zero,map_zero] at eq
  have norm := actual_electron_physical_seed_norm leg
  rw [←eq,norm_zero] at norm
  exact zero_ne_one norm

def actualElectronPhysicalUnit (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ)
    (leg : CompositeLeg) : H :=
  (‖actualElectronPhysicalResponse p F z leg‖:ℂ)⁻¹ • actualElectronPhysicalResponse p F z leg

theorem actual_electron_physical_unit_norm (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (leg : CompositeLeg) :‖actualElectronPhysicalUnit p F z leg‖=1 := by
  rw [actualElectronPhysicalUnit,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr (actual_electron_physical_response_nonzero p F z nonreal leg))]

theorem actual_electron_physical_unit_amputation (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (leg : CompositeLeg) :
    jointGenerator p F z 0 (actualElectronPhysicalUnit p F z leg)=
      (‖actualElectronPhysicalResponse p F z leg‖:ℂ)⁻¹ • actualElectronPhysicalSeed leg := by
  rw [actualElectronPhysicalUnit,map_smul,actual_electron_physical_response_equation p F z nonreal leg]

theorem actual_electron_physical_response_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (leg : CompositeLeg) :
    ‖actualElectronPhysicalResponse p F z leg‖≤originalJointResolventPrice p F z := by
  exact ((jointResolvent p F z 0).le_opNorm (actualElectronPhysicalSeed leg)).trans
    (by rw [actual_electron_physical_seed_norm,mul_one]; exact originalJointResolvent_price p F z nonreal)

end LowEnergy.GaussComposite.ActualElectronPhysicalJointInverse
