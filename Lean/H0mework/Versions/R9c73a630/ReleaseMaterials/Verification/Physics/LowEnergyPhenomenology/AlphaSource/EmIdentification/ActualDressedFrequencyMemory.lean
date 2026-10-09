import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedDampedFourier
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedClockKernel
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationInverse
import Mathlib.Analysis.Convolution

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFrequencyInverse
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil PreparationVacuumFieldPerturbation
open SourcePropagationNoetherTime SourcePropagationResolvent
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedHistoryKernel ActualDressedClockMoment ActualDressedFrequencyHalf
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
local instance : NormedAlgebra ℝ ResponseOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ ResponseOp:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] noetherMemoryMap rawInitial jointGenerator jointCurrent physicalTime
  leftCurrent rightCurrent twoTimeMap driveOperator sourceInverse

private theorem physical_time_add (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t s : ℝ) :
    physicalTime p F t 0*physicalTime p F s 0=physicalTime p F (t+s) 0 := by
  unfold physicalTime
  exact (SourceFiniteUnitary.time_add (jointGenerator p F 0 0) t s).symm

private theorem memory_algebra {R : Type*} [Ring R]
    (Ls Ln Lt Lr Rs Rn Rt Rr JL JR A : R)
    (leftInner : Ln*Lt=Lr) (rightInner : Rt*Rn=Rr)
    (leftOuter : Ls*Lr=Lt) (rightOuter : Rr*Rs=Rt) :
    (Ls*(-JL)*Ln)*(Lt*A*Rt)+(Lt*A*Rt)*(Rn*JR*Rs)=
      Ls*(-(JL*(Lr*A*Rr))+(Lr*A*Rr)*JR)*Rs := by
  have left : (Ls*(-JL)*Ln)*(Lt*A*Rt)=Ls*(-(JL*(Lr*A*Rr)))*Rs := by
    calc
      _=Ls*(-JL)*(Ln*Lt)*A*Rt := by noncomm_ring
      _=Ls*(-JL)*Lr*A*(Rr*Rs) := by rw [leftInner,rightOuter]
      _=_ := by noncomm_ring
  have right : (Lt*A*Rt)*(Rn*JR*Rs)=Ls*((Lr*A*Rr)*JR)*Rs := by
    calc
      _=Lt*A*(Rt*Rn)*JR*Rs := by noncomm_ring
      _=(Ls*Lr)*A*Rr*JR*Rs := by rw [rightInner,leftOuter]
      _=_ := by noncomm_ring
  rw [left,right]
  noncomm_ring

/-- The original two ordered memories are one forward source convolution, with their order unchanged. -/
theorem noether_memory_convolution (q : PhysicalResponsePoint) (reader force : Field289) (t s : ℝ) :
    noetherMemoryMap q reader t s force=
      twoTimeMap q s (driveOperator q force (twoTimeMap q (t-s) (rawInitial q reader))) := by
  let L : ℝ→ResponseOp:=fun r=>physicalTime (q.p+q.k) q.F (-r) 0
  let R : ℝ→ResponseOp:=fun r=>physicalTime q.p q.F r 0
  have leftInner : L (-s)*L t=L (t-s) := by
    dsimp only [L]
    rw [physical_time_add]
    congr 1
    ring
  have rightInner : R t*R (-s)=R (t-s) := by
    dsimp only [R]
    rw [physical_time_add]
    rfl
  have leftOuter : L s*L (t-s)=L t := by
    dsimp only [L]
    rw [physical_time_add]
    congr 1
    ring
  have rightOuter : R (t-s)*R s=R t := by
    dsimp only [R]
    rw [physical_time_add]
    congr 1
    ring
  have source:=memory_algebra (L s) (L (-s)) (L t) (L (t-s))
    (R s) (R (-s)) (R t) (R (t-s)) (leftCurrent q force) (rightCurrent q force)
    (rawInitial q reader) leftInner rightInner leftOuter rightOuter
  unfold leftCurrent rightCurrent at source
  simpa only [noetherMemoryMap,L,R,physicalTime,neg_neg,leftCurrent,rightCurrent,
    twoTimeMap_apply,driveOperator_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply,one_mul,mul_one] using! source

end LowEnergy.GaussComposite.ActualDressedFrequencyInverse
