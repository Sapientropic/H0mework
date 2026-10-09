import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLiouvillianBlocks
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceFullN1Sylvester

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
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumGaugeSlowFrequency PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalGradeZeroRead CanonicalGradedCurrent
attribute [local irreducible] actualC

def sourceOffgapInverse (F : GaussUnitaryHistory.Index) : SourceSuperOp :=
  ∑i : Channel F,∑j : Channel F,if channelValue F i=channelValue F j then 0 else
    (-Complex.I*(sourceStaticGap F i j : ℂ))⁻¹ • sourcePairProjection F i j

def sourceOffgapPrice (F : GaussUnitaryHistory.Index) : ℝ :=
  ∑i : Channel F,∑j : Channel F,
    if channelValue F i=channelValue F j then 0 else |sourceStaticGap F i j|⁻¹

theorem sourceOffgapInverse_apply (F : GaussUnitaryHistory.Index) (X : SourceOp) :
    sourceOffgapInverse F X=∑i : Channel F,∑j : Channel F,
      if channelValue F i=channelValue F j then 0 else
        (-Complex.I*(sourceStaticGap F i j : ℂ))⁻¹ • sourcePairProjection F i j X := by
  classical
  unfold sourceOffgapInverse
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [smul_apply,zero_apply]

theorem sourceOffProjection_apply (F : GaussUnitaryHistory.Index) (X : SourceOp) :
    sourceOffProjection F X=∑i : Channel F,∑j : Channel F,
      if channelValue F i=channelValue F j then 0 else sourcePairProjection F i j X := by
  classical
  have total : (∑i : Channel F,∑j : Channel F,sourcePairProjection F i j X)=X := by
    have h:=congrArg (fun T : SourceSuperOp=>T X) (sourcePairProjection_resolution F)
    change (∑i : Channel F,∑j : Channel F,sourcePairProjection F i j) X=X at h
    simpa only [sum_apply] using h
  change X-sourceEqualProjection F X=_
  conv_lhs =>
    lhs
    rw [←total]
  rw [sourceEqualProjection_apply,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [sub_self,sub_zero]

private theorem actual_frequency_ne (F : GaussUnitaryHistory.Index) (i j : Channel F)
    (different : channelValue F i≠channelValue F j) : -Complex.I*(sourceStaticGap F i j : ℂ)≠0 :=
  mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr different))

theorem sourceOffgapInverse_left (F : GaussUnitaryHistory.Index) :
    sourceStaticLiouvillian F*sourceOffgapInverse F=sourceOffProjection F := by
  classical
  apply ContinuousLinearMap.ext
  intro X
  change sourceStaticLiouvillian F (sourceOffgapInverse F X)=sourceOffProjection F X
  rw [sourceOffgapInverse_apply,sourceOffProjection_apply]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with equalEnergy
  · exact map_zero _
  · rw [map_smul]
    have eigen:=congrArg (fun T : SourceSuperOp=>T X) (sourcePairProjection_static_left F i j)
    change sourceStaticLiouvillian F (sourcePairProjection F i j X)=
      (-Complex.I*(sourceStaticGap F i j : ℂ)) • sourcePairProjection F i j X at eigen
    rw [eigen,smul_smul,inv_mul_cancel₀ (actual_frequency_ne F i j equalEnergy),one_smul]

theorem sourceOffgapInverse_right (F : GaussUnitaryHistory.Index) :
    sourceOffgapInverse F*sourceStaticLiouvillian F=sourceOffProjection F := by
  classical
  apply ContinuousLinearMap.ext
  intro X
  change sourceOffgapInverse F (sourceStaticLiouvillian F X)=sourceOffProjection F X
  rw [sourceOffgapInverse_apply,sourceOffProjection_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with equalEnergy
  · rfl
  · have eigen:=congrArg (fun T : SourceSuperOp=>T X) (sourcePairProjection_static_right F i j)
    change sourcePairProjection F i j (sourceStaticLiouvillian F X)=
      (-Complex.I*(sourceStaticGap F i j : ℂ)) • sourcePairProjection F i j X at eigen
    rw [eigen,smul_smul,inv_mul_cancel₀ (actual_frequency_ne F i j equalEnergy),one_smul]

theorem sourceOffgapInverse_price (F : GaussUnitaryHistory.Index) :
    ‖sourceOffgapInverse F‖ ≤ sourceOffgapPrice F := by
  classical
  unfold sourceOffgapInverse sourceOffgapPrice
  apply (norm_sum_le Finset.univ (fun i : Channel F=>
    ∑j : Channel F,if channelValue F i=channelValue F j then (0 : SourceSuperOp) else
      (-Complex.I*(sourceStaticGap F i j : ℂ))⁻¹ • sourcePairProjection F i j)).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le Finset.univ (fun j : Channel F=>
    if channelValue F i=channelValue F j then (0 : SourceSuperOp) else
      (-Complex.I*(sourceStaticGap F i j : ℂ))⁻¹ • sourcePairProjection F i j)).trans
  apply Finset.sum_le_sum
  intro j _
  split_ifs with equalEnergy
  · exact le_of_eq (ContinuousLinearMap.opNorm_zero : ‖(0 : SourceSuperOp)‖=0)
  · apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [norm_inv,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (sourcePairProjection_price F i j) (inv_nonneg.mpr (abs_nonneg _))).trans_eq (mul_one _)

theorem sourceOffgapPrice_radius (F : GaussUnitaryHistory.Index) :
    sourceOffgapPrice F ≤ (Fintype.card (Channel F) : ℝ)^2/(2*sourceGapRadius F) := by
  classical
  unfold sourceOffgapPrice
  have each (i j : Channel F) :
      (if channelValue F i=channelValue F j then 0 else |sourceStaticGap F i j|⁻¹) ≤ (2*sourceGapRadius F)⁻¹ := by
    split_ifs with equalEnergy
    · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (sourceGapRadius_positive F).le)
    · exact inv_anti₀ (mul_pos (by norm_num) (sourceGapRadius_positive F))
        (sourceGapRadius_gap F i j (sub_ne_zero.mpr equalEnergy))
  calc
    _≤∑i : Channel F,∑j : Channel F,(2*sourceGapRadius F)⁻¹ :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>each i j))
    _=(Fintype.card (Channel F) : ℝ)^2/(2*sourceGapRadius F) := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

private theorem minus_i_smul (X : SourceOp) :
    (-Complex.I) • X=-(Complex.I • X) := by
  apply ContinuousLinearMap.ext
  intro x
  change (-Complex.I) • (X x)=-(Complex.I • (X x))
  exact neg_smul Complex.I (X x)

private theorem slow_equal_return (F : GaussUnitaryHistory.Index) (V X B : SourceOp) (delta zeta : ℂ)
    (source : delta • (zeta • X+Complex.I • (V*X))+sourceStaticLiouvillian F X=B) :
    delta • (zeta • sourceEqualProjection F X+
      Complex.I • sourceEqualProjection F (V*sourceEqualProjection F X)+
      Complex.I • sourceEqualProjection F (V*sourceOffProjection F X))=sourceEqualProjection F B := by
  have h:=congrArg (sourceEqualProjection F) source
  have zero:=congrArg (fun T : SourceSuperOp=>T X) (sourceEqual_static_zero F)
  change sourceEqualProjection F (sourceStaticLiouvillian F X)=0 at zero
  simp only [map_add,map_smul] at h
  rw [zero,add_zero] at h
  have split : X=sourceEqualProjection F X+sourceOffProjection F X := by
    change X=sourceEqualProjection F X+(X-sourceEqualProjection F X)
    abel
  have velocity:=congrArg (fun Y : SourceOp=>sourceEqualProjection F (V*Y)) split
  rw [mul_add,map_add] at velocity
  rw [velocity] at h
  simpa only [smul_add,add_assoc] using h

private theorem slow_off_return (F : GaussUnitaryHistory.Index) (V X B : SourceOp) (delta zeta : ℂ)
    (source : delta • (zeta • X+Complex.I • (V*X))+sourceStaticLiouvillian F X=B) :
    sourceOffProjection F X=sourceOffgapInverse F B-
      delta • sourceOffgapInverse F (zeta • X+Complex.I • (V*X)) := by
  have h:=congrArg (sourceOffgapInverse F) source
  have inverse:=congrArg (fun T : SourceSuperOp=>T X) (sourceOffgapInverse_right F)
  change sourceOffgapInverse F (sourceStaticLiouvillian F X)=sourceOffProjection F X at inverse
  simp only [map_add,map_smul] at h
  rw [inverse] at h
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  simpa only [map_add,map_smul] using h

theorem sourceActualN1Slow_equal (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289) :
    let X1:=sourceFullHalfUpper q (-(delta • n)) 0 i ((delta : ℂ)*zeta)
    let X0:=sourceFullHalfBase q (-(delta • n)) 0 i ((delta : ℂ)*zeta)
    ((delta : ℂ) • (zeta • sourceEqualProjection q.F X1+
      Complex.I • sourceEqualProjection q.F (sourceVelocityLinear q.F n*sourceEqualProjection q.F X1)+
      Complex.I • sourceEqualProjection q.F (sourceVelocityLinear q.F n*sourceOffProjection q.F X1))=
        sourceEqualProjection q.F (sourceFullInitialUpper q (-(delta • n)) 0 i)) ∧
    ((delta : ℂ) • (zeta • sourceEqualProjection q.F X0+
      Complex.I • sourceEqualProjection q.F (sourceVelocityLinear q.F n*sourceEqualProjection q.F X0)+
      Complex.I • sourceEqualProjection q.F (sourceVelocityLinear q.F n*sourceOffProjection q.F X0))=
        sourceEqualProjection q.F (sourceFullInitialBase q (-(delta • n)) 0 i-
          Complex.I • (X1*(actualA 0 q.F*sourceProjection)))) := by
  have source:=sourceFullHalf_slow_system q n delta positiveDelta zeta positiveZeta i
  exact ⟨slow_equal_return q.F _ _ _ _ _ (by
    simpa only [sourceStaticLiouvillian_apply,minus_i_smul,sub_eq_add_neg] using source.1),
    slow_equal_return q.F _ _ _ _ _ (by
    simpa only [sourceStaticLiouvillian_apply,minus_i_smul,sub_eq_add_neg] using source.2)⟩

theorem sourceActualN1Slow_off (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289) :
    let X1:=sourceFullHalfUpper q (-(delta • n)) 0 i ((delta : ℂ)*zeta)
    let X0:=sourceFullHalfBase q (-(delta • n)) 0 i ((delta : ℂ)*zeta)
    (sourceOffProjection q.F X1=sourceOffgapInverse q.F (sourceFullInitialUpper q (-(delta • n)) 0 i)-
      (delta : ℂ) • sourceOffgapInverse q.F (zeta • X1+Complex.I • (sourceVelocityLinear q.F n*X1))) ∧
    (sourceOffProjection q.F X0=sourceOffgapInverse q.F (sourceFullInitialBase q (-(delta • n)) 0 i-
        Complex.I • (X1*(actualA 0 q.F*sourceProjection)))-
      (delta : ℂ) • sourceOffgapInverse q.F (zeta • X0+Complex.I • (sourceVelocityLinear q.F n*X0))) := by
  have source:=sourceFullHalf_slow_system q n delta positiveDelta zeta positiveZeta i
  exact ⟨slow_off_return q.F _ _ _ _ _ (by
    simpa only [sourceStaticLiouvillian_apply,minus_i_smul,sub_eq_add_neg] using source.1),
    slow_off_return q.F _ _ _ _ _ (by
    simpa only [sourceStaticLiouvillian_apply,minus_i_smul,sub_eq_add_neg] using source.2)⟩

end LowEnergy.PreparationVacuumPhysicalSlowBlock
