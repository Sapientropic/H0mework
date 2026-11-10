import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronNoetherDensity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceElectronChargeUnit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronNoetherDensity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open ActualCompositeFieldCurrent ActualCompositeGaugeBand ActualDressedNoetherCoulombUnit
open ActualDressedTemporalForm PreparationPhysicalElectronChargeUnitReturn
open scoped InnerProductSpace
attribute [local irreducible] compositeUnitLeg compositeChargeCore compositeResolvent compositeChargeMixing
  actualDensityCorrection noetherEMCurrent sourcePair

private theorem unit_pair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (v : V) (unit : ‖v‖=1) : inner ℂ v v=1 := by
  rw [inner_self_eq_norm_sq_to_K,unit]
  norm_num

/-- The actual complete response, rather than its input, generates its diagonal unit overlap. -/
theorem actual_output_charge_overlap_one (leg : CompositeLeg) : actualChargeOverlap leg leg=1 := by
  unfold actualChargeOverlap sourcePair
  exact unit_pair (embed (compositeUnitLeg leg)) (composite_unit_norm leg)

/-- Canonical action charge retains the full output mixing after its source unit normalization. -/
theorem actual_canonical_output_charge (p : PhysicalMomentum) (leg : CompositeLeg) :
    emActionForm p (compositeUnitLeg leg) (compositeUnitLeg leg)=
      sourceInputCharge leg+actualChargeMixingRead leg leg := by
  rw [actual_canonical_em_action_charge,actual_output_charge_read,actual_output_charge_overlap_one,mul_one]
  rfl

def actualChargeMixingVector (leg : CompositeLeg) : QuantumTest :=
  compositeInverseNorm leg • compositeResolvent leg (compositeChargeMixing leg)

/-- Both genuine full-Y/frame mixing and coframe/independent-dual density correction remain on the same complete output. -/
def actualElectronCalibrationVector (leg : CompositeLeg) : QuantumTest :=
  actualChargeMixingVector leg+actualDensityCorrection leg

theorem actual_charge_mixing_vector_read (left right : CompositeLeg) :
    actualChargeMixingRead left right=sourcePair (compositeUnitLeg left) (actualChargeMixingVector right) := by
  simp only [actualChargeMixingRead,actualChargeMixingVector,sourcePair,map_smul,inner_smul_right]

/-- The original diagonal calibration is now an actual generated correction-vector read, with source volume and full fractional matrix retained. -/
theorem actual_electron_calibration_read (p : PhysicalMomentum) (leg : CompositeLeg) :
    noetherChargeCalibration p leg leg=sourcePair (compositeUnitLeg leg) (actualElectronCalibrationVector leg) := by
  rw [noetherChargeCalibration,actual_output_charge_overlap_one,sub_self,mul_zero,zero_add,
    actual_charge_mixing_vector_read,actual_noether_density_correction]
  simp only [actualElectronCalibrationVector,sourcePair,map_add,inner_add_right]

private theorem unit_inner_price {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (u v : V) (unit : ‖u‖=1) : ‖inner ℂ u v‖≤‖v‖ :=
  (norm_inner_le_norm u v).trans_eq (by rw [unit,one_mul])

/-- The source itself pays the actual calibration price; no scalar budget or charge-eigenstate is supplied. -/
theorem actual_electron_calibration_price (p : PhysicalMomentum) (leg : CompositeLeg) :
    ‖noetherChargeCalibration p leg leg‖≤‖embed (actualElectronCalibrationVector leg)‖ := by
  rw [actual_electron_calibration_read]
  unfold sourcePair
  exact unit_inner_price _ _ (composite_unit_norm leg)

/-- The zero-momentum raw Noether read is compared to the source's actual independent-dual electron unit, keeping its full generated correction. -/
theorem actual_electron_noether_unit_return (p : PhysicalMomentum) (leg : CompositeLeg) (side : Fin 2) :
    noetherEMCurrent p leg leg 0=
      sourceInputCharge leg*sourceElectronNoetherUnit side+
        sourcePair (compositeUnitLeg leg) (actualElectronCalibrationVector leg) := by
  rw [actual_calibrated_noether_charge,actual_electron_calibration_read,
    sourceElectronNoetherUnit_generated,sourceElectronChargeUnit_generated,mul_one]

/-- Actual physical charge is controlled around the generated electron unit by the original full-source calibration, at zero momentum and every identical temporal read. -/
theorem actual_electron_noether_unit_price (p : PhysicalMomentum) (leg : CompositeLeg) (side : Fin 2) :
    ‖noetherEMCurrent p leg leg 0-sourceInputCharge leg*sourceElectronNoetherUnit side‖≤
      ‖embed (actualElectronCalibrationVector leg)‖ := by
  rw [actual_electron_noether_unit_return,add_sub_cancel_left]
  unfold sourcePair
  exact unit_inner_price _ _ (composite_unit_norm leg)

/-- The original source fractional CAR increment stays distinct from the actual electron unit used in the same calibration. -/
theorem actual_electron_fraction_preserved (addition : Bool) :
    PreparationPhysicalJointEMCouplingUnitReturn.sourceJointIncrement addition≠sourceElectronChargeUnit :=
  sourceElectron_joint_increment_ne_unit addition

end LowEnergy.GaussComposite.ActualElectronNoetherDensity
