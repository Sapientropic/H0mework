import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedVoltageCurrent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedYJoint
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 Stage10.TemporalGauge CanonicalGradedSpatialSource SourceQuantumScalarChart
open SourceQuantumFockGauge SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussComposite GaussComposite.SourceGraph
open CanonicalScalarPreparation GaussDensityCore
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent CanonicalGradedCharge
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldConstraintResponse
open PreparationPhysicalDressedSpinChargeReturn PreparationPhysicalJointEMCouplingUnitReturn
open PreparationPhysicalVoltageNoether PreparationVacuumStaticVoltageSource PreparationPhysicalPhaseGaugeRealization
open ActualDressedSourcePreparation ActualDressedSourceResponse ActualDressedJointWard
open ActualDressedActionPhase ActualDressedFullCoulomb ActualDressedVoltagePhase
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse
  dressedJointInput chargeReader

open ActualDressedVoltagePreparation ActualDressedVoltageCurrent
open PreparationVacuumNativeFieldInjection GaussNativeMatter
open StageNineHolonomicField StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction

/-- Literal source exterior Y weights annihilate every selected scalar-letter coefficient, for all scalar configurations. -/
theorem creation_scalar_Y_neutral (channel : Fin 2) (phi : Scalar) :
    fiberCreation channel 0 (scalarMotherLieAction
      (p286LieBlockEmbed HyperchargeResponse.chargeDirection) phi)=0 := by
  have zero (c : Fin 3) : (0:ℂ) • GaussCARHistory.createFiber (mode 0 c)=0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply PiLp.ext
    intro word
    change (0:ℂ)*(GaussCARHistory.createFiber (mode 0 c) v) word=0
    exact zero_mul _
  simp only [fiberCreation,scalar_coefficient_native_neutral,star_zero,zero,Finset.sum_const_zero]

/-- The original Y Cauchy scalar tangent has zero restriction on this creation letter. -/
theorem voltage_scalar_preparation_zero (slope : ℝ) : voltageScalarPreparation slope=0 := by
  have coefficient (c : Fin 3) :
      scalarCoefficient 1 c (slope • scalarCharge HyperchargeResponse.chargeDirection)=0 := by
    have source : scalarCharge HyperchargeResponse.chargeDirection=
        scalarMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
          (sourceGeneratedVacuumCoordinates Runtime.source) := rfl
    rw [source]
    have linear:=((scalarCoefficient 1 c).restrictScalars ℝ).map_smul slope
      (scalarMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
        (sourceGeneratedVacuumCoordinates Runtime.source))
    change scalarCoefficient 1 c (slope • _)=slope • scalarCoefficient 1 c _ at linear
    rw [linear,scalar_coefficient_native_neutral,_root_.smul_zero]
  apply ContinuousLinearMap.ext
  intro profile
  change voltageScalarPreparation slope profile=0
  rw [voltage_scalar_preparation_original]
  simp only [coefficient,star_zero,_root_.zero_smul,Finset.sum_const_zero]

theorem actual_voltage_scalar_input_zero (event : DressedEvent) (slope : ℝ) :
    dressedVoltageScalarInput event slope=0 := by
  rw [dressedVoltageScalarInput,voltage_scalar_preparation_zero,zero_apply,smul_zero]

/-- This same Y orbit is the original scalar action, not an EM generator renamed as Y. -/
theorem original_Y_scalar_letter (channel : Fin 2) (phi : Scalar) :
    fiberCreation channel 0 (action phi nativeY)=0 := by
  have same : action phi nativeY=scalarMotherLieAction
      (p286LieBlockEmbed HyperchargeResponse.chargeDirection) phi := by
    apply scalarCoordinateEquiv.symm.injective
    rw [scalarAction_mother,scalarMotherLieAction,LinearEquiv.symm_apply_apply]
    simp only [nativeMother,nativeY,p286CoordinateEquiv.symm_apply_apply]
  rw [same]
  exact creation_scalar_Y_neutral channel phi

/-- The original Y preparation input is the charged seed response on the unchanged profile. -/
def sourceYInputCompleted : Profile→L[ℂ]H := -completedLeg true 1 0

theorem source_Y_input_core (f : ScalarTest) :
    sourceYInputCompleted (core f)=creationSource 1 0 (chargeAction nativeY (seedSection f)) := by
  rw [sourceYInputCompleted,neg_apply,completedLeg_core,source_section_charge (seedSection f) f (fun _=>rfl),map_neg]
  rfl

/-- Completion retains the actual charged input; the scalar-letter Y contribution is already generated as zero. -/
theorem source_Y_completed_charge (profile : Profile) :
    chargeReader nativeY (completedLeg true 1 0 profile)=
      (-1:ℂ) • completedLeg true 1 0 profile+sourceYInputCompleted profile := by
  refine core_dense.induction_on profile (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [completedLeg_core,source_Y_input_core]
  change chargeReader nativeY (creationSource 1 0 (seedSection f))=
    (-1:ℂ) • creationSource 1 0 (seedSection f)+creationSource 1 0 (chargeAction nativeY (seedSection f))
  rw [←embed_creation_test,chargeReader_core,
    created_core_charge 1 0 (seedSection f) f (fun _=>rfl),map_smul,embed_creation_test,
    source_section_charge (seedSection f) f (fun _=>rfl),map_neg]
  module

/-- The source-normalized relative creation return retains its actual same-profile input. -/
def dressedYInput (event : DressedEvent) : H :=
  ((‖sourceDressedExcitation event.epsilon event.precision‖:ℂ)⁻¹*
    PhysicalEMDressedCharacter.emDressedCharacter true) •
      sourceYInputCompleted (sourceProfile event.epsilon event.precision)

theorem dressed_Y_joint_return (event : DressedEvent) :
    chargeReader nativeY (sourceDressedUnit event.epsilon event.precision)=
      (-1:ℂ) • sourceDressedUnit event.epsilon event.precision+dressedYInput event := by
  rw [source_dressed_unit_original,sourceDressedAddition,map_smul,source_Y_completed_charge]
  simp only [smul_add,smul_smul,dressedYInput]
  module

end LowEnergy.GaussComposite.ActualDressedYJoint
