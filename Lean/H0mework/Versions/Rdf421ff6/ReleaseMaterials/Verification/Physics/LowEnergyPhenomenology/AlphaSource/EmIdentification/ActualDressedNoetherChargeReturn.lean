import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedOrderedSpatialReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMClockAction
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherBasis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNoetherCoulombUnit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreHilbert GaussCoreDifferential
open GaussFockPair GaussDensityCore GaussHistoryHilbert PreparationVacuumSourceActionJets
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart PreparationVacuumActionFieldLift
open PreparationVacuumJointFieldResponse
open ActualCompositeFieldCurrent ActualCompositeGaugeBand ActualEMCurrentSplit ActualEMCarrierOwn
open ActualDressedConstraintRead PhysicalEMGaugeRealization ActualDressedFullCoulomb MeasureTheory
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local irreducible] rawForm compositeUnitLeg ActualCompositeFieldCurrent.compositeCurrent emInsertion

def noetherEMCurrent (p : PhysicalMomentum) (left right : CompositeLeg) : Fin 4→ℂ :=
  (Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ • emCurrent (ActualCompositeFieldCurrent.compositeCurrent p left right)

/-- The unit read is generated from the original action symbol on the unchanged complete endpoints. -/
theorem actual_noether_em_reader (p : PhysicalMomentum) (left right : CompositeLeg) (mu : Fin 4) :
    noetherEMCurrent p left right mu=
      -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
        rawForm (emGaugeField mu) p (compositeUnitLeg left) (compositeUnitLeg right) 0 := by
  have basis := source_reader_form_basis (emGaugeField mu) p (compositeUnitLeg left) (compositeUnitLeg right) 0
    (by simpa only [norm_zero] using ambientRadius_positive (compositeUnitLeg left))
  have raw : rawForm (emGaugeField mu) p (compositeUnitLeg left) (compositeUnitLeg right) 0=
      ∑i : Fin 289,(emGaugeField mu i : ℂ)*rawForm (fieldUnit i) p (compositeUnitLeg left) (compositeUnitLeg right) 0 := by
    simpa only [noetherForm_source,smul_eq_mul] using basis
  simp only [noetherEMCurrent,Pi.smul_apply,smul_eq_mul,emCurrent,Matrix.mulVec,Matrix.transpose_apply,
    dotProduct,emInsertion,ActualCompositeFieldCurrent.compositeCurrent]
  rw [raw]
  simp only [mul_neg,Finset.sum_neg_distrib,neg_mul]

def actualChargeOverlap (left right : CompositeLeg) : ℂ := sourcePair (compositeUnitLeg left) (compositeUnitLeg right)

def actualChargeMixingRead (left right : CompositeLeg) : ℂ :=
  compositeInverseNorm right*sourcePair (compositeUnitLeg left)
    (compositeResolvent right (compositeChargeMixing right))

def actualChargeRead (left right : CompositeLeg) : ℂ :=
  sourcePair (compositeUnitLeg left) (compositeChargeCore (compositeUnitLeg right))

theorem actual_output_charge_read (left right : CompositeLeg) :
    actualChargeRead left right=(if right.dual then (-1:ℂ) else 1)*actualChargeOverlap left right+
      actualChargeMixingRead left right := by
  unfold actualChargeRead
  rw [composite_unit_charge_return]
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right,
    actualChargeOverlap,actualChargeMixingRead]

private theorem raw_sample_integrable (p : PhysicalMomentum) (left right : CompositeLeg) :
    Integrable (fun z=>rawSample (emGaugeField 0) p (compositeUnitLeg left) (compositeUnitLeg right) (0,z)) GaussHistoryHilbert.configurationMeasure :=
  parameter_slice_integrable _ (tsupport (compositeUnitLeg left)) (compositeUnitLeg left).hasCompactSupport 0
    (fun z=>rawSample_near_smooth _ p _ _ 0 z (by simpa only [norm_zero] using ambientRadius_positive (compositeUnitLeg left)))
    (rawSample_zero _ p _ _)

/-- Original action density divided by its generated Noether unit, minus the literal full504 charge density. -/
def noetherDensitySample (p : PhysicalMomentum) (left right : CompositeLeg) (z : SourceCoordinateSlice) : ℂ :=
  -(Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹ *
    rawSample (emGaugeField 0) p (compositeUnitLeg left) (compositeUnitLeg right) (0,z)-
      densityPair (compositeUnitLeg left) (compositeChargeCore (compositeUnitLeg right)) z

def noetherDensityDefect (p : PhysicalMomentum) (left right : CompositeLeg) : ℂ :=
  ∫z,noetherDensitySample p left right z ∂GaussHistoryHilbert.configurationMeasure

theorem actual_noether_density_return (p : PhysicalMomentum) (left right : CompositeLeg) :
    noetherEMCurrent p left right 0=actualChargeRead left right+noetherDensityDefect p left right := by
  rw [actual_noether_em_reader]
  unfold noetherDensityDefect noetherDensitySample
  rw [integral_sub ((raw_sample_integrable p left right).const_mul _)
    (densityPair_integrable _ _),integral_const_mul,←sourcePair_integral]
  rw [rawForm]
  unfold actualChargeRead
  ring

/-- Input ±1, the complete output overlap/mixing, and the original density reader all reach the same actual field current. -/
theorem actual_noether_unit_charge (p : PhysicalMomentum) (left right : CompositeLeg) :
    noetherEMCurrent p left right 0=(if right.dual then (-1:ℂ) else 1)*actualChargeOverlap left right+
      actualChargeMixingRead left right+noetherDensityDefect p left right := by
  rw [actual_noether_density_return,actual_output_charge_read]

/-- The literal coordinate Gram and the actual h-normalized action read pay this factor at both endpoints. -/
theorem actual_coordinate_noether_unit (p : PhysicalMomentum) (left right : CompositeLeg) :
    emCoordinateCurrent (ActualCompositeFieldCurrent.compositeCurrent p left right)=
      ((4/3:ℂ)*(Stage10.ActionNormalization.phaseMomentum : ℂ)) • noetherEMCurrent p left right := by
  have nonzero : (Stage10.ActionNormalization.phaseMomentum : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  simp only [noetherEMCurrent,emCoordinateCurrent,smul_smul]
  congr 1
  field_simp

end LowEnergy.GaussComposite.ActualDressedNoetherCoulombUnit
