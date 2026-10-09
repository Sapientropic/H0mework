import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceOffgapInverse

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPinnedVelocity
open GaussCoreHilbert GaussUnitaryHistory SourceJointResidualEnergy SourceRetardedIncrement
open PreparationVacuumPhysicalSlowBlock PreparationVacuumPhysicalHalfAxis
open PreparationVacuumSharedPoleCarrier PreparationVacuumPhysicalFeedback CanonicalPhysicalSpatial
open CanonicalGradedSpatialSource
open scoped BigOperators InnerProductSpace Topology
attribute [local irreducible] actualC sourceVelocityLinear sourceChannelOp channelValue

private theorem adjoint_false (p : Prop) [Decidable p] (A : SourceOp) (no : ¬p) :
    ContinuousLinearMap.adjoint (if p then A else (0 : SourceOp))=0 := by
  have zero : ContinuousLinearMap.adjoint (0 : SourceOp)=(0 : SourceOp) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=H) (F:=H)).map_zero
  exact (congrArg (fun X : SourceOp=>ContinuousLinearMap.adjoint X) (if_neg no)).trans zero

theorem sourceChannel_selfAdjoint (F : GaussUnitaryHistory.Index) (i : Channel F) :
    IsSelfAdjoint (sourceChannelOp F i) := by
  cases i with
  | none =>
    rw [sourceChannelOp]
    change ContinuousLinearMap.adjoint (1-(supportSpan F).starProjection)=_
    have projection:=isSelfAdjoint_starProjection (supportSpan F)
    change ContinuousLinearMap.adjoint (supportSpan F).starProjection=(supportSpan F).starProjection at projection
    rw [map_sub,ContinuousLinearMap.adjoint_one,projection]
    rfl
  | some i =>
    rw [sourceChannelOp]
    change ContinuousLinearMap.adjoint (InnerProductSpace.rankOne ℂ ((sourceBasis F) i : H) ((sourceBasis F) i : H))=_
    exact InnerProductSpace.adjoint_rankOne _ _

theorem sourceVelocity_selfAdjoint (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    IsSelfAdjoint (sourceVelocityLinear F n) := by
  have difference : sourceVelocityLinear F n=actualC n F-actualC 0 F := by
    rw [actualC_affine]
    abel
  rw [difference]
  change ContinuousLinearMap.adjoint (actualC n F-actualC 0 F)=_
  have left:=actualC_symmetric n F
  have right:=actualC_symmetric 0 F
  change ContinuousLinearMap.adjoint (actualC n F)=actualC n F at left
  change ContinuousLinearMap.adjoint (actualC 0 F)=actualC 0 F at right
  rw [map_sub,left,right]

def sourcePinnedVelocity (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) : SourceOp :=
  sourceEqualProjection F (sourceVelocityLinear F n)

theorem sourcePinnedVelocity_generated (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourcePinnedVelocity F n=∑i : Channel F,∑j : Channel F,
      if channelValue F i=channelValue F j then
        sourceChannelOp F i*sourceVelocityLinear F n*sourceChannelOp F j else 0 := by
  rw [sourcePinnedVelocity,sourceEqualProjection_apply]
  simp only [sourcePairProjection_apply]

theorem sourcePinnedVelocity_selfAdjoint (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    IsSelfAdjoint (sourcePinnedVelocity F n) := by
  classical
  change ContinuousLinearMap.adjoint (sourcePinnedVelocity F n)=sourcePinnedVelocity F n
  rw [sourcePinnedVelocity_generated]
  simp only [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases same : channelValue F i=channelValue F j
  · rw [if_pos same,if_pos same.symm]
    have left:=sourceChannel_selfAdjoint F i
    have right:=sourceChannel_selfAdjoint F j
    have velocity:=sourceVelocity_selfAdjoint F n
    change ContinuousLinearMap.adjoint (sourceChannelOp F i)=sourceChannelOp F i at left
    change ContinuousLinearMap.adjoint (sourceChannelOp F j)=sourceChannelOp F j at right
    change ContinuousLinearMap.adjoint (sourceVelocityLinear F n)=sourceVelocityLinear F n at velocity
    simp only [ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp,left,right,velocity,
      ContinuousLinearMap.comp_assoc]
  · exact (adjoint_false _ _ (Ne.symm same)).trans (if_neg same).symm

theorem sourcePinnedVelocity_equal (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourceEqualProjection F (sourcePinnedVelocity F n)=sourcePinnedVelocity F n := by
  unfold sourcePinnedVelocity
  have h:=congrArg (fun T : SourceSuperOp=>T (sourceVelocityLinear F n))
    (sourceEqualProjection_idempotent F)
  simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_apply] using h

theorem sourcePinnedVelocity_commute (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    Commute (actualC 0 F) (sourcePinnedVelocity F n) := by
  have zero:=congrArg (fun T : SourceSuperOp=>T (sourceVelocityLinear F n))
    (sourceStatic_equal_zero F)
  change sourceStaticLiouvillian F (sourcePinnedVelocity F n)=0 at zero
  rw [sourceStaticLiouvillian_apply] at zero
  have commutator : actualC 0 F*sourcePinnedVelocity F n-sourcePinnedVelocity F n*actualC 0 F=0 := by
    apply ContinuousLinearMap.ext
    intro x
    have point:=congrArg (fun T : SourceOp=>T x) zero
    change (-Complex.I) • ((actualC 0 F*sourcePinnedVelocity F n-sourcePinnedVelocity F n*actualC 0 F) x)=0 at point
    have cancel:=congrArg (fun y : H=>(-Complex.I)⁻¹ • y) point
    simpa only [smul_smul,inv_mul_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero),one_smul,smul_zero,zero_apply] using cancel
  exact sub_eq_zero.mp commutator

end LowEnergy.PreparationVacuumPhysicalPinnedVelocity
