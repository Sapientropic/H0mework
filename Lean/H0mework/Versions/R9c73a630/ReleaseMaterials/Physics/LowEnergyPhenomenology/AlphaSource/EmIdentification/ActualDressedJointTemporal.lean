import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedJointOrbitCurrent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedJointTemporal
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

open PreparationVacuumElectricConstraint PreparationVacuumTemporalCharge PreparationVacuumSourcePreparedState
open Filter Set MeasureTheory
open PreparationChartGuard PreparationVacuumLowerClassical GaussFockPair

open ActualDressedJointGraph

open ActualDressedJointOrbitCurrent

/-- The original normalized temporal action column reads exactly the same actual response pairs. -/
def dressedTemporalActionRead (event : DressedEvent) (transfer : PhysicalMomentum)
    (a : Fin 12) (readFrame : GaussUnitaryHistory.Index) : ℂ :=
  sourcePair
    (sourceTestApprox readFrame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (sourceDressedUnit event.epsilon event.precision)))
    (familyCore (temporalField a) event.momentum (sourceTestApprox readFrame
      (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)))-
  sourcePair
    (sourceTestApprox readFrame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (prepared (sourceProfile event.epsilon event.precision))))
    (familyCore (temporalField a) event.momentum (sourceTestApprox readFrame
      (finiteFull event.momentum event.frame event.cut event.energy (prepared (sourceProfile event.epsilon event.precision)))))

private theorem original_orbit_temporal (a : Fin 12) (p : PhysicalMomentum) (f g : QuantumTest) :
    sourcePair f (orbitAction (originalUnit a) g)= -sourcePair f (familyCore (temporalField a) p g) := by
  rw [temporal_core,original_gauss_constraint]
  simp only [LinearMap.neg_apply,sourcePair,map_neg,inner_neg_right]

private theorem temporal_orbit_pair (a : Fin 12) (p : PhysicalMomentum) (l r bl br : QuantumTest) :
    sourcePair l (familyCore (temporalField a) p r)-sourcePair bl (familyCore (temporalField a) p br)=
      -(sourcePair l (orbitAction (originalUnit a) r)-sourcePair bl (orbitAction (originalUnit a) br)) := by
  rw [original_orbit_temporal a p l r,original_orbit_temporal a p bl br]
  ring

attribute [local irreducible] dressedJointOrbitRead dressedJointOrbitResponse dressedTemporalActionRead

/-- The original weighted complete configuration orbit is the negative of the original normalized temporal action current, on this same event. -/
theorem dressed_joint_original_temporal (event : DressedEvent) (transfer : PhysicalMomentum)
    (a : Fin 12) (readFrame : GaussUnitaryHistory.Index) :
    dressedJointOrbitRead event transfer a readFrame= -dressedTemporalActionRead event transfer a readFrame := by
  have paid:=temporal_orbit_pair a event.momentum
    (sourceTestApprox readFrame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (sourceDressedUnit event.epsilon event.precision)))
    (sourceTestApprox readFrame (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))
    (sourceTestApprox readFrame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (prepared (sourceProfile event.epsilon event.precision))))
    (sourceTestApprox readFrame (finiteFull event.momentum event.frame event.cut event.energy (prepared (sourceProfile event.epsilon event.precision))))
  have same : dressedTemporalActionRead event transfer a readFrame= -dressedJointOrbitRead event transfer a readFrame := by
    simpa only [dressedTemporalActionRead,dressedJointOrbitRead] using paid
  simpa only [neg_neg] using (congrArg Neg.neg same).symm

/-- The same-source normalized temporal action response consumes the complete original joint graph domain. -/
theorem dressed_temporal_response_limit (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12) :
    Tendsto (dressedTemporalActionRead event transfer a) GaussUnitaryHistory.sourceFilter
      (𝓝 (-dressedJointOrbitResponse event transfer a)) := by
  have paid:=(dressed_joint_orbit_response_limit event transfer a).neg
  have same : dressedTemporalActionRead event transfer a=
      fun readFrame=> -dressedJointOrbitRead event transfer a readFrame := by
    funext readFrame
    have equality:=dressed_joint_original_temporal event transfer a readFrame
    linear_combination equality
  rw [same]
  exact paid

/-- Original temporal Y columns on the same actual unit/background pair recover the relative source value through the source graph. -/
theorem actual_temporal_Y_source_limit (event : DressedEvent) :
    Tendsto (fun readFrame : GaussUnitaryHistory.Index=>
      sourcePair (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision))
        (familyCore (temporalField 11) event.momentum (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision)))-
      sourcePair (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision)))
        (familyCore (temporalField 11) event.momentum (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision)))))
      GaussUnitaryHistory.sourceFilter (𝓝 (-1:ℂ)) := by
  have paid:=(actual_joint_Y_source_limit event).neg
  convert paid using 1
  funext readFrame
  exact temporal_orbit_pair 11 event.momentum
    (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision))
    (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision))
    (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision)))
    (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision)))

end LowEnergy.GaussComposite.ActualDressedJointTemporal
