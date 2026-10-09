import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageFixedMomentumCharge

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalVoltageNoetherChargeReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open PreparationVacuumNoetherChart PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumFullFieldRiesz PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalDensity PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussQuantumMultiplier
open SourceQuantumFockGauge SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open CanonicalGradedSpatialSource
open PreparationVacuumSourceActionJets
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators
attribute [local irreducible] noetherReader noetherReaderContact PreparationVacuumNonlinearFieldCurve.rawReader rawReaderContact

/-- The unit reader is built from the original source momentum matrix and original source tests. -/
def sourceVoltageUnitForm (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z) (quantizer (sourceVoltageUnitSymbol (sourceState z) p) (b z))
    ∂GaussHistoryHilbert.configurationMeasure

def sourceVoltageUnitReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H :=
  finiteRiesz F (fun i j=>sourceVoltageUnitForm p (frameTest F i) (frameTest F j))

theorem sourceVoltageNoetherForm_momentum (p : PhysicalMomentum) (a b : QuantumTest) :
    noetherForm (fieldUnit 20) p a b 0=(ActionNormalization.phaseMomentum:ℂ)*sourceVoltageUnitForm p a b := by
  rw [noetherForm,sourceVoltageUnitForm,←integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases inside : z∈tsupport a
  · have valid:=PreparationVacuumNonlinearFieldCurve.sourceState_valid (⟨z,a.tsupport_subset inside⟩:physicalChart)
    change pairSample z (a z) (quantizer (transportedRawSymbol (fieldUnit 20) (sourceState z) (ambientState (0,z)) p) (b z))=_
    rw [ambientState_zero,sourceVoltageTransportedSymbol _ _ valid]
    rw [quantizer.map_smul_of_tower]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_apply,pairSample_smul_right]
    rfl
  · simp only [noetherSample_zero _ _ _ _ _ _ inside,image_eq_zero_of_notMem_tsupport inside,
      pairSample_zero_left,mul_zero]

theorem sourceVoltageNoetherReader_momentum (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader (fieldUnit 20) p F 0=ActionNormalization.phaseMomentum • sourceVoltageUnitReader p F := by
  simp only [noetherReader,sourceVoltageUnitReader,sourceVoltageNoetherForm_momentum,finiteRiesz,
    Finset.smul_sum,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]
  rfl

/-- Only the fixed-Pi Noether contact vanishes; the raw moving-momentum contact has not been changed. -/
theorem sourceVoltageNoetherContactForm_zero (force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    noetherContactForm (fieldUnit 20) force p a b=0 := by
  rw [noetherContactForm]
  have zero : (fun z=>pairSample z (a z) (quantizer (noetherContactSymbol (fieldUnit 20) force (sourceState z) p) (b z)))=0 := by
    funext z
    by_cases inside : z∈tsupport a
    · rw [sourceVoltageNoetherContactSymbol force (⟨z,a.tsupport_subset inside⟩:physicalChart),map_zero,zero_apply]
      simp [pairSample]
    · simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,Pi.zero_apply]
  rw [zero]
  exact integral_zero _ _

theorem sourceVoltageNoetherReaderContact_zero (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReaderContact (fieldUnit 20) force p F=0 := by
  rw [noetherReaderContact_source]
  simp only [sourceVoltageNoetherContactForm_zero,finiteRiesz,zero_smul,Finset.sum_const_zero]

/-- Both original independent preparation legs keep their resolvents and physical clocks. -/
def sourceVoltageUnitPreparedCurrent (q : PhysicalResponsePoint) (age : ℝ) : ℂ :=
  preparedDual q 0 age (sourceVoltageUnitReader q.p q.F (preparedPrimal q 0 age))

def sourceVoltageUnitPreparedSlope (q : PhysicalResponsePoint) (force : Field289) (age : ℝ) : ℂ :=
  dualSlope q force age (sourceVoltageUnitReader q.p q.F (preparedPrimal q 0 age))+
    preparedDual q 0 age (sourceVoltageUnitReader q.p q.F (primalSlope q force age))

theorem sourceVoltageNoetherPreparedCurrent (q : PhysicalResponsePoint) (age : ℝ) :
    noetherPreparedCurrent q (fieldUnit 20) 0 age=
      (ActionNormalization.phaseMomentum:ℂ)*sourceVoltageUnitPreparedCurrent q age := by
  rw [noetherPreparedCurrent,sourceVoltageNoetherReader_momentum]
  simp only [sourceVoltageUnitPreparedCurrent,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_apply,map_smul,smul_eq_mul]
  rfl

/-- The two differentiated source legs are the complete voltage response after the proved Noether contact cancellation. -/
theorem sourceVoltageNoetherPreparedSlope (q : PhysicalResponsePoint) (force : Field289) (age : ℝ) :
    noetherPreparedSlope q (fieldUnit 20) force age=
      (ActionNormalization.phaseMomentum:ℂ)*sourceVoltageUnitPreparedSlope q force age := by
  rw [noetherPreparedSlope,sourceVoltageNoetherReaderContact_zero]
  simp only [zero_apply,map_zero,add_zero]
  rw [densitySlope]
  rw [←noetherReader_source,sourceVoltageNoetherReader_momentum]
  simp only [sourceVoltageUnitPreparedSlope,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_apply,map_smul,
    smul_eq_mul,mul_add]
  change (ActionNormalization.phaseMomentum:ℂ)*
      dualSlope q force age (sourceVoltageUnitReader q.p q.F (preparedPrimal q 0 age))+
      preparedDual q 0 age (rawReaderContact (fieldUnit 20) force q.p q.F (preparedPrimal q 0 age))+
      (ActionNormalization.phaseMomentum:ℂ)*
      preparedDual q 0 age (sourceVoltageUnitReader q.p q.F (primalSlope q force age))-
      preparedDual q 0 age (rawReaderContact (fieldUnit 20) force q.p q.F (preparedPrimal q 0 age))=
      (ActionNormalization.phaseMomentum:ℂ)*
      dualSlope q force age (sourceVoltageUnitReader q.p q.F (preparedPrimal q 0 age))+
      (ActionNormalization.phaseMomentum:ℂ)*
      preparedDual q 0 age (sourceVoltageUnitReader q.p q.F (primalSlope q force age))
  ring

end LowEnergy.PreparationPhysicalVoltageNoetherChargeReturn
