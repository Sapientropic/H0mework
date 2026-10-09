import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedLeftAction
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSlowCurrentReturn

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPinnedVelocity
open GaussCoreHilbert GaussUnitaryHistory PreparationVacuumPhysicalSlowBlock
open PreparationVacuumPhysicalHalfAxis PreparationVacuumSharedPoleCarrier PreparationVacuumPhysicalFeedback
open FullYSourceResolventGraphSplice
open CanonicalGradedSpatialSource
open scoped BigOperators InnerProductSpace Topology
attribute [local irreducible] actualC sourcePinnedVelocity

def sourcePinnedPencil (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : SourceOp :=
  zeta • (1 : SourceOp)+Complex.I • sourcePinnedVelocity F n

def sourcePinnedResolvent (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : SourceOp :=
  (-Complex.I) • FullYSourceResolventGraphSplice.resolvent (sourcePinnedVelocity F n) (Complex.I*zeta)

private theorem source_nonreal (zeta : ℂ) (positive : 0<zeta.re) : (Complex.I*zeta).im≠0 := by
  simpa only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] using positive.ne'

theorem sourcePinnedPencil_factor (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    sourcePinnedPencil F n zeta=
      Complex.I • (sourcePinnedVelocity F n-(Complex.I*zeta) • (1 : SourceOp)) := by
  apply ContinuousLinearMap.ext
  intro x
  change zeta • x+Complex.I • sourcePinnedVelocity F n x=
    Complex.I • (sourcePinnedVelocity F n x-(Complex.I*zeta) • x)
  have coefficient : Complex.I*(Complex.I*zeta)=-zeta := by rw [←mul_assoc,Complex.I_mul_I,neg_one_mul]
  rw [smul_sub,smul_smul,coefficient,neg_smul,sub_neg_eq_add,add_comm]

theorem sourcePinnedResolvent_left (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) : sourcePinnedResolvent F n zeta*sourcePinnedPencil F n zeta=1 := by
  rw [sourcePinnedResolvent,sourcePinnedPencil_factor,smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [show (-Complex.I)*Complex.I=1 by simp only [neg_mul,Complex.I_mul_I,neg_neg],one_smul]
  exact FullYSourceResolventGraphSplice.resolvent_left _ (sourcePinnedVelocity_selfAdjoint F n) _ (source_nonreal zeta positive)

theorem sourcePinnedResolvent_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) : sourcePinnedPencil F n zeta*sourcePinnedResolvent F n zeta=1 := by
  rw [sourcePinnedPencil_factor,sourcePinnedResolvent,smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [show Complex.I*(-Complex.I)=1 by simp only [mul_neg,Complex.I_mul_I,neg_neg],one_smul]
  exact FullYSourceResolventGraphSplice.resolvent_right _ (sourcePinnedVelocity_selfAdjoint F n) _ (source_nonreal zeta positive)

theorem sourcePinnedResolvent_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) : ‖sourcePinnedResolvent F n zeta‖ ≤ 1/zeta.re := by
  unfold sourcePinnedResolvent
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [norm_neg,Complex.norm_I,one_mul]
  have price:=FullYSourceResolventGraphSplice.resolvent_norm _ (sourcePinnedVelocity_selfAdjoint F n) _ (source_nonreal zeta positive)
  simpa only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,abs_of_pos positive] using price

private theorem equal_of_commute (F : GaussUnitaryHistory.Index) (X : SourceOp)
    (commute : Commute (actualC 0 F) X) : sourceEqualProjection F X=X := by
  have zero : sourceStaticLiouvillian F X=0 := by
    rw [sourceStaticLiouvillian_apply,sub_eq_zero.mpr commute.eq]
    apply ContinuousLinearMap.ext
    intro x
    change (-Complex.I) • (0 : H)=0
    exact smul_zero (-Complex.I)
  have inverse:=congrArg (fun T : SourceSuperOp=>T X) (sourceOffgapInverse_right F)
  change sourceOffgapInverse F (sourceStaticLiouvillian F X)=sourceOffProjection F X at inverse
  rw [zero,map_zero] at inverse
  change 0=X-sourceEqualProjection F X at inverse
  exact (sub_eq_zero.mp inverse.symm).symm

theorem sourcePinnedPencil_commute (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    Commute (actualC 0 F) (sourcePinnedPencil F n zeta) := by
  unfold sourcePinnedPencil
  exact ((Commute.one_right (actualC 0 F)).smul_right zeta).add_right
    ((sourcePinnedVelocity_commute F n).smul_right Complex.I)

theorem sourcePinnedResolvent_commute (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) : Commute (actualC 0 F) (sourcePinnedResolvent F n zeta) := by
  have left:=sourcePinnedResolvent_left F n zeta positive
  have right:=sourcePinnedResolvent_right F n zeta positive
  have commute:=(sourcePinnedPencil_commute F n zeta).eq
  change actualC 0 F*sourcePinnedResolvent F n zeta=sourcePinnedResolvent F n zeta*actualC 0 F
  calc
    _=sourcePinnedResolvent F n zeta*sourcePinnedPencil F n zeta*actualC 0 F*sourcePinnedResolvent F n zeta := by rw [left,one_mul]
    _=sourcePinnedResolvent F n zeta*actualC 0 F*sourcePinnedPencil F n zeta*sourcePinnedResolvent F n zeta := by
      simp only [mul_assoc]
      rw [←mul_assoc (sourcePinnedPencil F n zeta),←commute]
      simp only [mul_assoc]
    _=_ := by rw [mul_assoc (sourcePinnedResolvent F n zeta*actualC 0 F),right,mul_one]

def sourcePinnedLeading (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : SourceSuperOp :=
  ContinuousLinearMap.mul ℂ SourceOp (sourcePinnedPencil F n zeta)*sourceEqualProjection F

def sourcePinnedLeadingInverse (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) : SourceSuperOp :=
  ContinuousLinearMap.mul ℂ SourceOp (sourcePinnedResolvent F n zeta)*sourceEqualProjection F

theorem sourcePinnedLeading_apply (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (X : SourceOp) :
    sourcePinnedLeading F n zeta X=sourcePinnedPencil F n zeta*sourceEqualProjection F X := rfl

theorem sourcePinnedLeadingInverse_apply (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) (X : SourceOp) :
    sourcePinnedLeadingInverse F n zeta X=sourcePinnedResolvent F n zeta*sourceEqualProjection F X := rfl

theorem sourcePinnedLeading_generated (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    sourcePinnedLeading F n zeta=sourceEqualProjection F*
      (zeta • (1 : SourceSuperOp)+Complex.I • ContinuousLinearMap.mul ℂ SourceOp (sourceVelocityLinear F n))*
      sourceEqualProjection F := by
  apply ContinuousLinearMap.ext
  intro X
  change sourcePinnedPencil F n zeta*sourceEqualProjection F X=
    sourceEqualProjection F (zeta • sourceEqualProjection F X+
      Complex.I • (sourceVelocityLinear F n*sourceEqualProjection F X))
  rw [map_add,map_smul,map_smul,sourcePinnedVelocity_left_action]
  have fixed:=congrArg (fun T : SourceSuperOp=>T X) (sourceEqualProjection_idempotent F)
  change sourceEqualProjection F (sourceEqualProjection F X)=sourceEqualProjection F X at fixed
  rw [fixed]
  simp only [sourcePinnedPencil,add_mul,smul_mul_assoc,one_mul]

theorem sourcePinnedLeading_actual (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ) :
    sourcePinnedLeading F n zeta=PreparationVacuumQuantumSlowResponse.sourceSlowLeading F n zeta :=
  sourcePinnedLeading_generated F n zeta

theorem sourcePinnedLeadingInverse_left (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) : sourcePinnedLeadingInverse F n zeta*sourcePinnedLeading F n zeta=sourceEqualProjection F := by
  apply ContinuousLinearMap.ext
  intro X
  change sourcePinnedResolvent F n zeta*sourceEqualProjection F (sourcePinnedPencil F n zeta*sourceEqualProjection F X)=_
  rw [sourceEqualProjection_right_module,equal_of_commute _ _ (sourcePinnedPencil_commute F n zeta),
    ←mul_assoc,sourcePinnedResolvent_left F n zeta positive,one_mul]

theorem sourcePinnedLeadingInverse_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) : sourcePinnedLeading F n zeta*sourcePinnedLeadingInverse F n zeta=sourceEqualProjection F := by
  apply ContinuousLinearMap.ext
  intro X
  change sourcePinnedPencil F n zeta*sourceEqualProjection F (sourcePinnedResolvent F n zeta*sourceEqualProjection F X)=_
  rw [sourceEqualProjection_right_module,equal_of_commute _ _ (sourcePinnedResolvent_commute F n zeta positive),
    ←mul_assoc,sourcePinnedResolvent_right F n zeta positive,one_mul]

theorem sourcePinnedLeadingInverse_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) : ‖sourcePinnedLeadingInverse F n zeta‖ ≤ (1/zeta.re)*‖sourceEqualProjection F‖ := by
  unfold sourcePinnedLeadingInverse
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact mul_le_mul_of_nonneg_right
    ((ContinuousLinearMap.opNorm_mul_apply_le ℂ SourceOp _).trans (sourcePinnedResolvent_price F n zeta positive))
    (norm_nonneg (sourceEqualProjection F))

private theorem source_leading_left_support (F : GaussUnitaryHistory.Index) (A : SourceOp)
    (commute : Commute (actualC 0 F) A) :
    sourceEqualProjection F*(ContinuousLinearMap.mul ℂ SourceOp A*sourceEqualProjection F)=
      ContinuousLinearMap.mul ℂ SourceOp A*sourceEqualProjection F := by
  apply ContinuousLinearMap.ext
  intro X
  change sourceEqualProjection F (A*sourceEqualProjection F X)=A*sourceEqualProjection F X
  rw [sourceEqualProjection_right_module,equal_of_commute F A commute]

private theorem source_leading_right_support (F : GaussUnitaryHistory.Index) (A : SourceOp) :
    (ContinuousLinearMap.mul ℂ SourceOp A*sourceEqualProjection F)*sourceEqualProjection F=
      ContinuousLinearMap.mul ℂ SourceOp A*sourceEqualProjection F := by
  apply ContinuousLinearMap.ext
  intro X
  change A*sourceEqualProjection F (sourceEqualProjection F X)=A*sourceEqualProjection F X
  have fixed:=congrArg (fun T : SourceSuperOp=>T X) (sourceEqualProjection_idempotent F)
  change sourceEqualProjection F (sourceEqualProjection F X)=sourceEqualProjection F X at fixed
  rw [fixed]

private theorem complete_inverse {R : Type*} [Ring R] (P E G : R)
    (idempotent : P*P=P) (leftE : P*E=E) (rightG : G*P=G) (inverse : G*E=P) :
    (G+(1-P))*(E+(1-P))=1 := by
  have offE : (1-P)*E=0 := by rw [sub_mul,one_mul,leftE,sub_self]
  have offG : G*(1-P)=0 := by rw [mul_sub,mul_one,rightG,sub_self]
  have offSquared : (1-P)*(1-P)=1-P := by
    calc
      _=1-P-P+P*P := by noncomm_ring
      _=1-P := by rw [idempotent];abel
  rw [add_mul,mul_add,mul_add,inverse,offE,offG,offSquared]
  abel

theorem sourcePinnedCompleteInverse_left (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) :
    (sourcePinnedLeadingInverse F n zeta+sourceOffProjection F)*
      (PreparationVacuumQuantumSlowResponse.sourceSlowLeading F n zeta+sourceOffProjection F)=1 := by
  rw [←sourcePinnedLeading_actual]
  exact complete_inverse _ _ _ (sourceEqualProjection_idempotent F)
    (source_leading_left_support _ _ (sourcePinnedPencil_commute F n zeta))
    (source_leading_right_support _ _) (sourcePinnedLeadingInverse_left F n zeta positive)

theorem sourcePinnedCompleteInverse_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) :
    (PreparationVacuumQuantumSlowResponse.sourceSlowLeading F n zeta+sourceOffProjection F)*
      (sourcePinnedLeadingInverse F n zeta+sourceOffProjection F)=1 := by
  rw [←sourcePinnedLeading_actual]
  exact complete_inverse _ _ _ (sourceEqualProjection_idempotent F)
    (source_leading_left_support _ _ (sourcePinnedResolvent_commute F n zeta positive))
    (source_leading_right_support _ _) (sourcePinnedLeadingInverse_right F n zeta positive)

end LowEnergy.PreparationVacuumPhysicalPinnedVelocity
