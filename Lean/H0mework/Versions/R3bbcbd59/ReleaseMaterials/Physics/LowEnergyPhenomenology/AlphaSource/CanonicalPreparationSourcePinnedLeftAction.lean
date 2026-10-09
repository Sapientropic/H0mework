import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedVelocity

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
attribute [local irreducible] channelValue sourceChannelOp sourceEqualProjection

private theorem zero_products {R : Type*} [Ring R] (A X B : R) :
    (0 : R)*X*B=A*X*(0 : R) := by rw [zero_mul,zero_mul,mul_zero]

private theorem zero_commute {R : Type*} [Ring R] (A : R) : A*0=0*A := by rw [mul_zero,zero_mul]

def sourceEnergyWindow (F : GaussUnitaryHistory.Index) (i : Channel F) : SourceOp :=
  ∑j : Channel F,if channelValue F i=channelValue F j then sourceChannelOp F j else 0

theorem sourceEnergyWindow_left (F : GaussUnitaryHistory.Index) (i j : Channel F) :
    sourceEnergyWindow F i*sourceChannelOp F j=
      if channelValue F i=channelValue F j then sourceChannelOp F j else 0 := by
  classical
  unfold sourceEnergyWindow
  rw [Finset.sum_mul]
  calc
    _=(if channelValue F i=channelValue F j then sourceChannelOp F j else 0)*sourceChannelOp F j := by
      apply Finset.sum_eq_single j
      · intro k _ different
        split_ifs <;> simp only [zero_mul,sourceChannelOp_product,if_neg different]
      · exact fun missing=>(missing (Finset.mem_univ j)).elim
    _=_ := by split_ifs <;> simp only [zero_mul,sourceChannelOp_product,if_true]

theorem sourceEnergyWindow_right (F : GaussUnitaryHistory.Index) (i j : Channel F) :
    sourceChannelOp F j*sourceEnergyWindow F i=
      if channelValue F i=channelValue F j then sourceChannelOp F j else 0 := by
  classical
  unfold sourceEnergyWindow
  rw [Finset.mul_sum]
  calc
    _=sourceChannelOp F j*(if channelValue F i=channelValue F j then sourceChannelOp F j else 0) := by
      apply Finset.sum_eq_single j
      · intro k _ different
        split_ifs <;> simp only [mul_zero,sourceChannelOp_product,if_neg (Ne.symm different)]
      · exact fun missing=>(missing (Finset.mem_univ j)).elim
    _=_ := by split_ifs <;> simp only [mul_zero,sourceChannelOp_product,if_true]

theorem sourceEqualProjection_grouped (F : GaussUnitaryHistory.Index) (A : SourceOp) :
    sourceEqualProjection F A=∑i : Channel F,sourceChannelOp F i*A*sourceEnergyWindow F i := by
  classical
  rw [sourceEqualProjection_apply]
  apply Finset.sum_congr rfl
  intro i _
  unfold sourceEnergyWindow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [sourcePairProjection_apply,mul_zero]

theorem sourceEnergyWindow_commute_equal (F : GaussUnitaryHistory.Index) (i : Channel F) (X : SourceOp) :
    Commute (sourceEnergyWindow F i) (sourceEqualProjection F X) := by
  classical
  change sourceEnergyWindow F i*sourceEqualProjection F X=
    sourceEqualProjection F X*sourceEnergyWindow F i
  rw [sourceEqualProjection_apply,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases equalEnergy : channelValue F j=channelValue F k
  · rw [if_pos equalEnergy,sourcePairProjection_apply]
    calc
      _=(sourceEnergyWindow F i*sourceChannelOp F j)*X*sourceChannelOp F k := by noncomm_ring
      _=sourceChannelOp F j*X*(sourceChannelOp F k*sourceEnergyWindow F i) := by
        rw [sourceEnergyWindow_left,sourceEnergyWindow_right]
        by_cases same : channelValue F i=channelValue F j
        · rw [if_pos same,if_pos (same.trans equalEnergy)]
        · have other : channelValue F i≠channelValue F k := fun h=>same (h.trans equalEnergy.symm)
          exact (congrArg (fun Y : SourceOp=>Y*X*sourceChannelOp F k) (if_neg same)).trans
            ((zero_products (sourceChannelOp F j) X (sourceChannelOp F k)).trans
              (congrArg (fun Y : SourceOp=>sourceChannelOp F j*X*Y) (if_neg other)).symm)
      _=_ := by noncomm_ring
  · exact (congrArg (fun Y : SourceOp=>sourceEnergyWindow F i*Y) (if_neg equalEnergy)).trans
      ((zero_commute (sourceEnergyWindow F i)).trans
        (congrArg (fun Y : SourceOp=>Y*sourceEnergyWindow F i) (if_neg equalEnergy)).symm)

theorem sourceEqualProjection_right_module (F : GaussUnitaryHistory.Index) (A X : SourceOp) :
    sourceEqualProjection F (A*sourceEqualProjection F X)=
      sourceEqualProjection F A*sourceEqualProjection F X := by
  conv_lhs => rw [sourceEqualProjection_grouped]
  conv_rhs =>
    lhs
    rw [sourceEqualProjection_grouped]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=sourceChannelOp F i*A*(sourceEqualProjection F X*sourceEnergyWindow F i) := by noncomm_ring
    _=sourceChannelOp F i*A*(sourceEnergyWindow F i*sourceEqualProjection F X) := by
      rw [(sourceEnergyWindow_commute_equal F i X).eq]
    _=_ := by noncomm_ring

theorem sourcePinnedVelocity_left_action (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (X : SourceOp) :
    sourceEqualProjection F (sourceVelocityLinear F n*sourceEqualProjection F X)=
      sourcePinnedVelocity F n*sourceEqualProjection F X :=
  sourceEqualProjection_right_module F (sourceVelocityLinear F n) X

end LowEnergy.PreparationVacuumPhysicalPinnedVelocity
