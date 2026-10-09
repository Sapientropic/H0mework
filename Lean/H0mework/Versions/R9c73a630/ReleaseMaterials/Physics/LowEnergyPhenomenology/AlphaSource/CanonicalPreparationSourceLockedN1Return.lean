import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedN1Pair

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalLockedN1Balance
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open CanonicalGradedSpatialSource PreparationVacuumPhysicalLockedGaussBalance
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFieldConstraintResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumNoetherChart
open PreparationVacuumPhysicalElectromagneticDirection
open scoped BigOperators Topology InnerProductSpace

theorem sourceLockedActualN1_rawCharge (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceLockedRawChargeCore (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
      weightCore (sourceLockedChargeCore (sourceTestApprox q.F (sourceActualN1Primal q p state z t))) := by
  rw [sourceLockedRawCore_generated,LinearMap.sub_apply,LinearMap.comp_apply,
    sourceLockedActualN1_pair_zero q p state z t nonreal,sub_zero]

theorem sourceLockedActualN1_rawDefect (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP : PhysicalMomentum) :
    sourceLockedRawChargeCore (rightCompressionDefect actualP q.F (sourceActualN1Primal q p state z t)+
      rightUncutDefect actualP q.F (sourceActualN1Primal q p state z t))=
      weightCore (sourceLockedChargeCore (rightCompressionDefect actualP q.F (sourceActualN1Primal q p state z t)+
        rightUncutDefect actualP q.F (sourceActualN1Primal q p state z t))) := by
  rw [sourceLockedRawCore_generated,LinearMap.sub_apply,LinearMap.comp_apply,
    sourceLockedActualN1_rightDefect_pair_zero q p state z t nonreal,sub_zero]

/-- All source torque terms remain; only the already generated CAR pair torque is removed. -/
theorem sourceLockedActualN1_weightedWard (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP k : PhysicalMomentum) :
    sourceLockedWeightedWard actualP k (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
      weightCore (sourceLockedWardCore actualP k (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))+
        weightActionTorque (actualP+k) (sourceLockedChargeCore
          (sourceTestApprox q.F (sourceActualN1Primal q p state z t))) := by
  unfold sourceLockedWeightedWard
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,
    sourceLockedActualN1_pairTorque_zero q p state z t nonreal,sub_zero]

def sourceLockedN1WardReturn (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (y : H) : H:=
  let f:=sourceTestApprox q.F y
  let d:=rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y
  sourceApprox q.F (embed (weightCore (sourceLockedWardCore pR (pL-pR) f)+
    weightActionTorque pL (sourceLockedChargeCore f)))+
    leftCompressionDefect pL q.F (weightCore (sourceLockedChargeCore f))+
    leftUncutDefect pL q.F (weightCore (sourceLockedChargeCore f))-
    sourceApprox q.F (embed (weightCore (sourceLockedChargeCore d)))

/-- The actual original full Hamiltonian insertion consumes N1 pair collapse on its same pole state and q.F. -/
theorem sourceLockedActualN1_insertion (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    noetherTimeInsertion (sourcePhysicalMaterialPoint q pL pR) (sourceLockedField 0 2)
      (sourceActualN1Primal q pR state z t)=
        sourceLockedN1WardReturn q pL pR (sourceActualN1Primal q pR state z t) := by
  rw [sourceLockedInsertion_generated]
  change sourceApprox q.F (embed (sourceLockedWeightedWard pR (pL-pR)
    (sourceTestApprox q.F (sourceActualN1Primal q pR state z t))))+
      leftCompressionDefect (pR+(pL-pR)) q.F (sourceLockedRawChargeCore
        (sourceTestApprox q.F (sourceActualN1Primal q pR state z t)))+
      leftUncutDefect (pR+(pL-pR)) q.F (sourceLockedRawChargeCore
        (sourceTestApprox q.F (sourceActualN1Primal q pR state z t)))-
      sourceApprox q.F (embed (sourceLockedRawChargeCore
        (rightCompressionDefect pR q.F (sourceActualN1Primal q pR state z t)+
          rightUncutDefect pR q.F (sourceActualN1Primal q pR state z t))))=_
  have momentum : pR+(pL-pR)=pL:=by ext i;simp
  have ward:=sourceLockedActualN1_weightedWard q pR state z t nonreal pR (pL-pR)
  rw [momentum] at ward
  rw [momentum,ward,sourceLockedActualN1_rawCharge q pR state z t nonreal,
    sourceLockedActualN1_rawDefect q pR state z t nonreal pR]
  rfl

end LowEnergy.PreparationVacuumPhysicalLockedN1Balance
