import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronSourceAmputation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronPhysicalNormalization
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource SourceQuantumFockGauge GaussCoreHilbert
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates GaussCoreDifferential
open GaussFockPair
open ActualCompositeFieldCurrent ActualCompositeGaugeBand ActualCompositeOriginWard
open ActualDressedTemporalForm ActualDressedNoetherCoulombUnit ActualElectronNoetherDensity
open scoped InnerProductSpace

/-- The charge character is generated on the amputated actual N3 source, rather than assumed on full-Y output. -/
theorem actual_electron_amputated_charge (leg : CompositeLeg) :
    compositeChargeCore (actualElectronAmputatedLeg leg)=
      (if leg.dual then (-1:ℂ) else 1) • actualElectronAmputatedLeg leg := by
  rw [actual_electron_amputated_source,map_smul,composite_input_charge_core,smul_comm]

theorem actual_electron_amputated_pair (leg : CompositeLeg) :
    sourcePair (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg)=1 := by
  unfold sourcePair
  rw [inner_self_eq_norm_sq_to_K,actual_electron_amputated_norm]
  norm_num

/-- Source time normalization and the full CAR pair contraction precede the diagonal unit read. -/
theorem actual_electron_amputated_action (p : PhysicalMomentum) (left : QuantumTest) (right : CompositeLeg) :
    emActionForm p left (actualElectronAmputatedLeg right)=
      (if right.dual then (-1:ℂ) else 1)*sourcePair left (actualElectronAmputatedLeg right) := by
  rw [em_action_form,←composite_charge_original,actual_electron_amputated_charge]
  simp only [sourcePair,map_smul,inner_smul_right]

theorem actual_electron_amputated_action_unit (p : PhysicalMomentum) (leg : CompositeLeg) :
    emActionForm p (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg)=
      (if leg.dual then (-1:ℂ) else 1) := by
  rw [actual_electron_amputated_action,actual_electron_amputated_pair,mul_one]

theorem actual_electron_amputated_absolute_unit (p : PhysicalMomentum) (leg : CompositeLeg) :
    ‖emActionForm p (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg)‖=1 := by
  rw [actual_electron_amputated_action_unit]
  cases leg.dual <;> norm_num

/-- Full-Y/frame charge mixing survives comparison with this separately generated amputated action unit. -/
theorem actual_electron_output_action_amputated_difference (p : PhysicalMomentum) (leg : CompositeLeg) :
    emActionForm p (compositeUnitLeg leg) (compositeUnitLeg leg)-
      emActionForm p (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg)=
        actualChargeMixingRead leg leg := by
  rw [actual_canonical_output_charge,actual_electron_amputated_action_unit]
  change (if leg.dual then (-1:ℂ) else 1)+actualChargeMixingRead leg leg-
    (if leg.dual then (-1:ℂ) else 1)=_
  ring

/-- The original raw Noether reader retains the full generated signed-volume and mixing calibration. -/
theorem actual_electron_raw_amputated_difference (p : PhysicalMomentum) (leg : CompositeLeg) :
    noetherEMCurrent p leg leg 0-
      emActionForm p (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg)=
        sourcePair (compositeUnitLeg leg) (actualElectronCalibrationVector leg) := by
  rw [actual_electron_amputated_action_unit]
  have paid := actual_noether_unit_charge p leg leg
  rw [actual_output_charge_overlap_one,mul_one,actual_charge_mixing_vector_read,
    actual_noether_density_correction] at paid
  rw [paid]
  simp only [actualElectronCalibrationVector,sourcePair,map_add,inner_add_right]
  ring

theorem actual_electron_raw_amputated_price (p : PhysicalMomentum) (leg : CompositeLeg) :
    ‖noetherEMCurrent p leg leg 0-
      emActionForm p (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg)‖≤
        ‖embed (actualElectronCalibrationVector leg)‖ := by
  rw [actual_electron_raw_amputated_difference]
  change ‖inner ℂ (embed (compositeUnitLeg leg)) (embed (actualElectronCalibrationVector leg))‖≤_
  exact (norm_inner_le_norm _ _).trans_eq (by rw [composite_unit_norm,one_mul])

theorem actual_electron_raw_norm_reserve (p : PhysicalMomentum) (leg : CompositeLeg) :
    1≤‖noetherEMCurrent p leg leg 0‖+‖embed (actualElectronCalibrationVector leg)‖ := by
  let q := emActionForm p (actualElectronAmputatedLeg leg) (actualElectronAmputatedLeg leg)
  let j := noetherEMCurrent p leg leg 0
  have charge : ‖q‖=1 := actual_electron_amputated_absolute_unit p leg
  have price : ‖j-q‖≤‖embed (actualElectronCalibrationVector leg)‖ := actual_electron_raw_amputated_price p leg
  calc
    1=‖q‖ := charge.symm
    _=‖j-(j-q)‖ := by congr 1; ring
    _≤‖j‖+‖j-q‖ := norm_sub_le _ _
    _≤_ := add_le_add le_rfl price

end LowEnergy.GaussComposite.ActualElectronPhysicalNormalization
