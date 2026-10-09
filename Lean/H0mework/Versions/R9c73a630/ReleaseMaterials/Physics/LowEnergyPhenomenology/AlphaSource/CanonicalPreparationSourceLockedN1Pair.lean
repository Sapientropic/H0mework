import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedPreparedBalance
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceN1NormalWard

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalLockedN1Balance
open GaussCoreHilbert GaussCoreDifferential GaussCoreLabel GaussHistoryHilbert GaussFockPair
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates GaussQuantumMultiplier
open CanonicalGradedSpatialSource CanonicalGradedCurrent NativeHistoryGrade
open PreparationVacuumPhysicalLockedGaussBalance PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumFieldConstraintResponse PreparationVacuumWeightedChargeActionWard
open PreparationVacuumPhysicalColorCharge PreparationVacuumPhysicalColorWard
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalZeroRead
open PreparationVacuumFullElectricWard PreparationVacuumPhysicalGradeZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumRawJointFeedback
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumNoetherChart
open Filter
open scoped BigOperators Topology InnerProductSpace
attribute [local irreducible] sourceLockedPairFiber
  sourceTestApprox sourceApprox sourcePolePrepared physicalTime sourceProjection
  jointResolvent sourceHamiltonian

/-- The paid generic CAR law applies to the actual fixed locked charge on every Number-one grade. -/
theorem sourceLockedPair_label_zero (g : Label) (one : g.1.val=1) (f : QuantumTest) :
    sourceLockedPairCore (GaussCoreLabel.project g f)=0 := by
  apply DFunLike.ext
  intro z
  change sourceLockedPairFiber z (fiberPiece g (f z))=0
  unfold sourceLockedPairFiber
  exact congrArg (fun A : FockFiber→L[ℂ] FockFiber=>A (f z))
    (sourceNumberOne_pairFiber_zero g one (sourceWeightSymbol z) sourceLockedChargeMatrix)

theorem sourceLockedPair_sourceN1_zero (f : QuantumTest) :
    sourceLockedPairCore (sourceN1Core f)=0 := by
  unfold sourceN1Core
  simp only [map_add,sourceLockedPair_label_zero CanonicalGradedCurrent.sourceLabel rfl,
    sourceLockedPair_label_zero sourceExcitedLabel rfl,zero_add]

/-- The full physical action and actual G0-to-G1 Yukawa map generate the same pair-free range. -/
theorem sourceLockedPair_fullSource_N1_zero (p : PhysicalMomentum) (f : QuantumTest) :
    sourceLockedPairCore (fullSourceAction p (sourceN1Core f))=0 := by
  have h0:=CanonicalPhysicalSpatial.physicalAction_blocks p CanonicalGradedCurrent.sourceLabel f
  have h1:=CanonicalPhysicalSpatial.physicalAction_blocks p sourceExcitedLabel f
  have hY : sourceLockedPairCore (GaussYukawaOperator.originalAction
      (GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel f))=0 :=
    (congrArg sourceLockedPairCore (originalY_sourceZero_range f)).symm.trans
      (sourceLockedPair_label_zero sourceExcitedLabel rfl _)
  unfold sourceN1Core fullSourceAction
  simp only [LinearMap.add_apply,map_add]
  rw [←h0,←h1,sourceLockedPair_label_zero CanonicalGradedCurrent.sourceLabel rfl,sourceLockedPair_label_zero sourceExcitedLabel rfl,
    hY,originalY_sourceOne_zero,map_zero]
  simp only [zero_add]

theorem sourceLockedActualN1_pair_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceLockedPairCore (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=0 := by
  have fixed:=sourceActualN1Primal_core q p state z t nonreal
  change sourceN1Core (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
    sourceTestApprox q.F (sourceActualN1Primal q p state z t) at fixed
  exact (congrArg sourceLockedPairCore fixed).symm.trans (sourceLockedPair_sourceN1_zero _)

theorem sourceLockedActualN1_fullSource_pair_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP : PhysicalMomentum) :
    sourceLockedPairCore (fullSourceAction actualP
      (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))=0 := by
  have fixed:=sourceActualN1Primal_core q p state z t nonreal
  change sourceN1Core (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
    sourceTestApprox q.F (sourceActualN1Primal q p state z t) at fixed
  exact (congrArg (fun f : QuantumTest=>sourceLockedPairCore (fullSourceAction actualP f)) fixed).symm.trans
    (sourceLockedPair_fullSource_N1_zero actualP _)

/-- Pair torque is actually eliminated on the original full-time/resolvent-generated pole state. -/
theorem sourceLockedActualN1_pairTorque_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP k : PhysicalMomentum) :
    sourceLockedPairTorque actualP k (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=0 := by
  unfold sourceLockedPairTorque
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,sourceLockedActualN1_pair_zero q p state z t nonreal,
    map_zero,sourceLockedActualN1_fullSource_pair_zero q p state z t nonreal,sub_zero]

private theorem sourceLocked_testApprox_pair_zero (F : GaussUnitaryHistory.Index) (y : H)
    (fixed : sourceN1Projection y=y) : sourceLockedPairCore (sourceTestApprox F y)=0 := by
  have h:=congrArg (sourceTestApprox F) fixed
  unfold sourceN1Projection at h
  rw [add_apply,sourceTestApprox_add] at h
  simp only [sourceProjection,sourceExcitedProjection,sourceTestApprox_projection] at h
  have zero:=congrArg sourceLockedPairCore h
  simp only [map_add,sourceLockedPair_label_zero CanonicalGradedCurrent.sourceLabel rfl,sourceLockedPair_label_zero sourceExcitedLabel rfl,zero_add] at zero
  exact zero.symm

/-- The actual full Hamiltonian and original CF/uncut defects generate pair-free right-leg errors. -/
theorem sourceLockedActualN1_rightDefect_pair_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP : PhysicalMomentum) :
    sourceLockedPairCore (rightCompressionDefect actualP q.F (sourceActualN1Primal q p state z t)+
      rightUncutDefect actualP q.F (sourceActualN1Primal q p state z t))=0 := by
  let y:=sourceActualN1Primal q p state z t
  have fixed:=sourceActualN1Primal_generated q p state z t nonreal
  change sourceN1Projection y=y at fixed
  have h:=congrArg (fun A : H→L[ℂ] H=>A y) (actualGenerator_sourceN1_range actualP q.F)
  simp only [mul_apply_eq_comp,fixed] at h
  have zero:=sourceLocked_testApprox_pair_zero q.F (sourceHamiltonian actualP q.F y) h
  have action:=congrArg sourceLockedPairCore (rightAction_source actualP q.F y)
  have full : sourceLockedPairCore (fullSourceAction actualP (sourceTestApprox q.F y))=0:=
    sourceLockedActualN1_fullSource_pair_zero q p state z t nonreal actualP
  simp only [map_add] at action
  rw [zero,full,zero_add] at action
  simpa only [map_add] using action.symm

end LowEnergy.PreparationVacuumPhysicalLockedN1Balance
