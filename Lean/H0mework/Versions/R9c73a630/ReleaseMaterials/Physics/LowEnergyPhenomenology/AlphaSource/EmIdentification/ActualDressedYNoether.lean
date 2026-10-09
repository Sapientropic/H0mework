import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedYJoint

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedYNoether
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

open ActualDressedYJoint PreparationVacuumActionDecomposition PreparationVacuumFullElectricWard CanonicalPhysicalWardCore
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumSourceActionJets FullQuantum.StateGreen FullQuantum.CoframeResponse

/-- The actual core returns the same Y input and the original half-density scalar correction, which the source letter annihilates. -/
theorem original_Y_joint_core (f : QuantumTest) (z : physicalChart) :
    chargeAction nativeY (creationTest 1 0 f) z-creationTest 1 0 (chargeAction nativeY f) z-
      Complex.I • ((rootVolume z:ℂ)⁻¹ •
        (fiberCreation 1 0 (action (GaussNativePotential.scalarField z) nativeY) (f z)))=
      -(creationTest 1 0 f z) := by
  have paid:=congrArg (fun g : QuantumTest=>g z) (creation_charge_core 1 0 f)
  change chargeAction nativeY (creationTest 1 0 f) z-creationTest 1 0 (chargeAction nativeY f) z=
    -(creationTest 1 0 f z) at paid
  simpa only [original_Y_scalar_letter,zero_apply,smul_zero,sub_zero,sub_apply,neg_apply] using paid

/-- The selected actual creation is unchanged along the original Y Cauchy scalar direction; the profile is unchanged. -/
theorem actual_Y_scalar_family (event : DressedEvent) (slope scale : ℝ) :
    dressedVoltageFamily event slope scale=sourceDressedUnit event.epsilon event.precision := by
  rw [dressedVoltageFamily,voltage_scalar_preparation_zero,zero_apply,smul_zero,add_zero,
    source_dressed_unit_original,sourceDressedAddition]

/-- The background input is charged and remains in the completed same-Lie return. -/
theorem actual_Y_input_return (event : DressedEvent) :
    dressedYInput event= -sourceDressedUnit event.epsilon event.precision := by
  rw [dressedYInput,sourceYInputCompleted,neg_apply,smul_neg,source_dressed_unit_original,sourceDressedAddition]

private theorem inverse_charge_return {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R B Q : V→ₗ[ℂ]V) (v b d : V) (q : ℂ)
    (left : R (B (Q v))=Q v) (input : B v=b) (charge : Q b=q • b+d) (back : R b=v) :
    Q v=q • v+R (d+B (Q v)-Q (B v)) := by
  rw [map_sub,map_add,left,input,charge,map_add,map_smul,back]
  abel

/-- The actual propagated relative Y return keeps its same charged input and complete cutoff/compression commutator. -/
theorem actual_Y_propagated_return (event : DressedEvent) :
    chargeReader nativeY (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)=
      (-1:ℂ) • sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy+
        finiteFull event.momentum event.frame event.cut event.energy
          (dressedYInput event+
            (CanonicalPhysicalSpatial.compression event.momentum event.frame+FullYSourceCutoffVolterra.cutoff event.cut-event.energy • 1)
              (chargeReader nativeY (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))-
            chargeReader nativeY
              ((CanonicalPhysicalSpatial.compression event.momentum event.frame+FullYSourceCutoffVolterra.cutoff event.cut-event.energy • 1)
                (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))) := by
  exact inverse_charge_return (finiteFull event.momentum event.frame event.cut event.energy).toLinearMap
    (CanonicalPhysicalSpatial.compression event.momentum event.frame+FullYSourceCutoffVolterra.cutoff event.cut-event.energy • 1).toLinearMap
    (chargeReader nativeY).toLinearMap (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)
    (sourceDressedUnit event.epsilon event.precision) (dressedYInput event) (-1:ℂ)
    (congrArg (fun A : H→L[ℂ]H=>A (chargeReader nativeY
      (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)))
      (finiteFull_left event.momentum event.frame event.cut event.energy event.nonreal))
    (source_dressed_response_equation event.epsilon event.precision event.momentum event.frame event.cut event.energy event.nonreal)
    (dressed_Y_joint_return event) (by unfold sourceDressedResponse; rfl)

/-- Full original Y action, configuration/profile torque, current, pair and scalar Yukawa return use this same propagated actual preparation. -/
theorem actual_Y_original_action (event : DressedEvent) (k : PhysicalMomentum) :
    (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore (event.momentum+k)-retainedCore)
        (chargeAction nativeY (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)))-
      chargeAction nativeY
        ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore event.momentum-retainedCore)
          (sourceTestApprox event.frame
            (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)))=
      configurationTorque nativeY (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))+
        CanonicalPhysicalWardCore.currentAction k nativeY (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))+
        pairCurrent k nativeY (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))+
        yukawaTorque nativeY (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)) := by
  exact original_action_components event.momentum k nativeY _

/-- All original twelve-Lie action restrictions, configuration/profile torque, current, pair and scalar Yukawa return use this same propagated actual preparation. -/
theorem actual_native_original_action (event : DressedEvent) (k : PhysicalMomentum) (q : NativeLie) :
    (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore (event.momentum+k)-retainedCore)
        (chargeAction q (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)))-
      chargeAction q
        ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore event.momentum-retainedCore)
          (sourceTestApprox event.frame
            (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)))=
      configurationTorque q (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))+
        CanonicalPhysicalWardCore.currentAction k q (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))+
        pairCurrent k q (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))+
        yukawaTorque q (sourceTestApprox event.frame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)) := by
  exact original_action_components event.momentum k q _

end LowEnergy.GaussComposite.ActualDressedYNoether
