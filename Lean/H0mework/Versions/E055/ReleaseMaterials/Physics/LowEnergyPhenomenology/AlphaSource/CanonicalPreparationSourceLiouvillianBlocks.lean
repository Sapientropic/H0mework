import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChannelOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalSlowBlock
open GaussCoreHilbert GaussUnitaryHistory SourceJointResidualEnergy SourceRetardedIncrement
open PreparationVacuumPhysicalAbelZeroRead PreparationVacuumPhysicalCausalZeroRead
open PreparationVacuumPhysicalFeedback CanonicalPhysicalSpatial
open PreparationVacuumPhysicalHalfAxis
open scoped BigOperators InnerProductSpace Topology
attribute [local irreducible] actualC

abbrev SourceOp := H→L[ℂ] H
abbrev SourceSuperOp := SourceOp→L[ℂ] SourceOp

def sourcePairProjection (F : GaussUnitaryHistory.Index) (i j : Channel F) : SourceSuperOp :=
  ContinuousLinearMap.mulLeftRight ℂ SourceOp (sourceChannelOp F i) (sourceChannelOp F j)

theorem sourcePairProjection_apply (F : GaussUnitaryHistory.Index) (i j : Channel F) (X : SourceOp) :
    sourcePairProjection F i j X=sourceChannelOp F i*X*sourceChannelOp F j := rfl

theorem sourcePairProjection_price (F : GaussUnitaryHistory.Index) (i j : Channel F) :
    ‖sourcePairProjection F i j‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ SourceOp _ _).trans
    ((mul_le_mul (sourceChannelOp_price F i) (sourceChannelOp_price F j) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem sourcePairProjection_product (F : GaussUnitaryHistory.Index) (i j k l : Channel F) :
    sourcePairProjection F i j*sourcePairProjection F k l=
      if i=k∧j=l then sourcePairProjection F i j else 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro X
  by_cases matchIndex:i=k∧j=l
  · rcases matchIndex with ⟨rfl,rfl⟩
    simp only [mul_apply_eq_comp,sourcePairProjection_apply]
    calc
      _=(sourceChannelOp F i*sourceChannelOp F i)*X*(sourceChannelOp F j*sourceChannelOp F j) := by noncomm_ring
      _=sourceChannelOp F i*X*sourceChannelOp F j := by rw [sourceChannelOp_product,sourceChannelOp_product];simp
  · rw [if_neg matchIndex]
    simp only [mul_apply_eq_comp,sourcePairProjection_apply,zero_apply]
    calc
      _=(sourceChannelOp F i*sourceChannelOp F k)*X*(sourceChannelOp F l*sourceChannelOp F j) := by noncomm_ring
      _=0 := by
        rw [sourceChannelOp_product,sourceChannelOp_product]
        rcases not_and_or.mp matchIndex with left|right
        · simp [left]
        · simp [Ne.symm right]

private theorem masked_selection {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (mask : ι→ι→Prop) [DecidableRel mask] (v : M) (i j : ι) :
    (∑k : ι,∑l : ι,if mask k l then if i=k∧j=l then v else 0 else 0)=
      if mask i j then v else 0 := by
  classical
  calc
    _=∑k : ι,∑l : ι,if k=i then if l=j then if mask k l then v else 0 else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      by_cases left:k=i
      · subst k
        by_cases right:l=j
        · subst l
          simp
        · simp [right,eq_comm]
          intro _ equal
          exact (right equal.symm).elim
      · simp [left,eq_comm]
        intro _ equal _
        exact (left equal.symm).elim
    _=if mask i j then v else 0 := by simp

def sourceEqualProjection (F : GaussUnitaryHistory.Index) : SourceSuperOp :=
  ∑i : Channel F,∑j : Channel F,
    if channelValue F i=channelValue F j then sourcePairProjection F i j else 0

def sourceOffProjection (F : GaussUnitaryHistory.Index) : SourceSuperOp := 1-sourceEqualProjection F

theorem sourceEqualProjection_apply (F : GaussUnitaryHistory.Index) (X : SourceOp) :
    sourceEqualProjection F X=∑i : Channel F,∑j : Channel F,
      if channelValue F i=channelValue F j then sourcePairProjection F i j X else 0 := by
  classical
  unfold sourceEqualProjection
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [zero_apply]

theorem sourcePairProjection_equal (F : GaussUnitaryHistory.Index) (i j : Channel F) (X : SourceOp) :
    sourcePairProjection F i j (sourceEqualProjection F X)=
      if channelValue F i=channelValue F j then sourcePairProjection F i j X else 0 := by
  classical
  have component (k l : Channel F) :
      sourcePairProjection F i j ((if channelValue F k=channelValue F l then sourcePairProjection F k l else 0) X)=
      if channelValue F k=channelValue F l then if i=k∧j=l then sourcePairProjection F i j X else 0 else 0 := by
    by_cases same:channelValue F k=channelValue F l
    · rw [if_pos same,if_pos same,←mul_apply_eq_comp,sourcePairProjection_product]
      split_ifs <;> simp only [zero_apply]
    · simp only [if_neg same,zero_apply,map_zero]
  unfold sourceEqualProjection
  simp only [sum_apply,map_sum]
  simp_rw [component]
  exact masked_selection (fun k l=>channelValue F k=channelValue F l) (sourcePairProjection F i j X) i j

theorem sourcePairProjection_resolution (F : GaussUnitaryHistory.Index) :
    ∑i : Channel F,∑j : Channel F,sourcePairProjection F i j=1 := by
  apply ContinuousLinearMap.ext
  intro X
  change (∑i : Channel F,∑j : Channel F,sourcePairProjection F i j) X=X
  simp only [sum_apply,sourcePairProjection_apply]
  simp_rw [←Finset.mul_sum,sourceChannelOp_resolution,mul_one]
  rw [←Finset.sum_mul,sourceChannelOp_resolution,one_mul]

theorem sourceEqualProjection_idempotent (F : GaussUnitaryHistory.Index) :
    sourceEqualProjection F*sourceEqualProjection F=sourceEqualProjection F := by
  classical
  apply ContinuousLinearMap.ext
  intro X
  change sourceEqualProjection F (sourceEqualProjection F X)=sourceEqualProjection F X
  rw [sourceEqualProjection_apply F (sourceEqualProjection F X)]
  conv_rhs => rw [sourceEqualProjection_apply F X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with same
  · rw [sourcePairProjection_equal,if_pos same]
  · rfl

def sourceStaticLiouvillian (F : GaussUnitaryHistory.Index) : SourceSuperOp :=
  (-Complex.I) • (ContinuousLinearMap.mul ℂ SourceOp (actualC 0 F)-
    (ContinuousLinearMap.mul ℂ SourceOp).flip (actualC 0 F))

theorem sourceStaticLiouvillian_apply (F : GaussUnitaryHistory.Index) (X : SourceOp) :
    sourceStaticLiouvillian F X=(-Complex.I) • (actualC 0 F*X-X*actualC 0 F) := rfl

private theorem collapse_frequency {M : Type*} [AddCommGroup M] [Module ℂ M]
    (a b : ℂ) (X : M) :
    (-Complex.I) • (a • X-b • X)=(-Complex.I*(a-b)) • X := by
  rw [←sub_smul,smul_smul]

theorem sourcePairProjection_static_left (F : GaussUnitaryHistory.Index) (i j : Channel F) :
    sourceStaticLiouvillian F*sourcePairProjection F i j=
      (-Complex.I*(sourceStaticGap F i j : ℂ)) • sourcePairProjection F i j := by
  apply ContinuousLinearMap.ext
  intro X
  simp only [mul_apply_eq_comp,sourcePairProjection_apply,sourceStaticLiouvillian_apply,smul_apply]
  have left:actualC 0 F*(sourceChannelOp F i*X*sourceChannelOp F j)=
      (channelValue F i : ℂ) • (sourceChannelOp F i*X*sourceChannelOp F j) := by
    calc
      _=(actualC 0 F*sourceChannelOp F i)*X*sourceChannelOp F j := by noncomm_ring
      _= _ := by rw [sourceChannelOp_left];simp only [smul_mul_assoc]
  have right:(sourceChannelOp F i*X*sourceChannelOp F j)*actualC 0 F=
      (channelValue F j : ℂ) • (sourceChannelOp F i*X*sourceChannelOp F j) := by
    calc
      _=sourceChannelOp F i*X*(sourceChannelOp F j*actualC 0 F) := by noncomm_ring
      _= _ := by rw [sourceChannelOp_right];simp only [mul_smul_comm]
  rw [left,right]
  simpa only [sourceStaticGap,Complex.ofReal_sub] using
    collapse_frequency (channelValue F i : ℂ) (channelValue F j : ℂ)
      (sourceChannelOp F i*X*sourceChannelOp F j)

theorem sourceStatic_equal_zero (F : GaussUnitaryHistory.Index) :
    sourceStaticLiouvillian F*sourceEqualProjection F=0 := by
  classical
  apply ContinuousLinearMap.ext
  intro X
  change sourceStaticLiouvillian F (sourceEqualProjection F X)=0
  rw [sourceEqualProjection_apply]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with same
  · have h:=congrArg (fun T : SourceSuperOp=>T X) (sourcePairProjection_static_left F i j)
    simp only [mul_apply_eq_comp,smul_apply,sourceStaticGap,same,sub_self,
      Complex.ofReal_zero,mul_zero] at h
    exact h.trans (zero_smul ℂ (sourcePairProjection F i j X))
  · exact map_zero _

theorem sourcePairProjection_static_right (F : GaussUnitaryHistory.Index) (i j : Channel F) :
    sourcePairProjection F i j*sourceStaticLiouvillian F=
      (-Complex.I*(sourceStaticGap F i j : ℂ)) • sourcePairProjection F i j := by
  apply ContinuousLinearMap.ext
  intro X
  simp only [mul_apply_eq_comp,sourceStaticLiouvillian_apply,smul_apply,map_smul,map_sub]
  simp only [sourcePairProjection_apply]
  have left:sourceChannelOp F i*(actualC 0 F*X)*sourceChannelOp F j=
      (channelValue F i : ℂ) • (sourceChannelOp F i*X*sourceChannelOp F j) := by
    calc
      _=(sourceChannelOp F i*actualC 0 F)*X*sourceChannelOp F j := by noncomm_ring
      _= _ := by rw [sourceChannelOp_right];simp only [smul_mul_assoc]
  have right:sourceChannelOp F i*(X*actualC 0 F)*sourceChannelOp F j=
      (channelValue F j : ℂ) • (sourceChannelOp F i*X*sourceChannelOp F j) := by
    calc
      _=sourceChannelOp F i*X*(actualC 0 F*sourceChannelOp F j) := by noncomm_ring
      _= _ := by rw [sourceChannelOp_left];simp only [mul_smul_comm]
  rw [left,right]
  simpa only [sourceStaticGap,Complex.ofReal_sub] using
    collapse_frequency (channelValue F i : ℂ) (channelValue F j : ℂ)
      (sourceChannelOp F i*X*sourceChannelOp F j)

theorem sourceEqual_static_zero (F : GaussUnitaryHistory.Index) :
    sourceEqualProjection F*sourceStaticLiouvillian F=0 := by
  classical
  apply ContinuousLinearMap.ext
  intro X
  change sourceEqualProjection F (sourceStaticLiouvillian F X)=0
  rw [sourceEqualProjection_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with same
  · have h:=congrArg (fun T : SourceSuperOp=>T X) (sourcePairProjection_static_right F i j)
    simp only [mul_apply_eq_comp,smul_apply,sourceStaticGap,same,sub_self,
      Complex.ofReal_zero,mul_zero] at h
    exact h.trans (zero_smul ℂ (sourcePairProjection F i j X))
  · rfl

end LowEnergy.PreparationVacuumPhysicalSlowBlock
