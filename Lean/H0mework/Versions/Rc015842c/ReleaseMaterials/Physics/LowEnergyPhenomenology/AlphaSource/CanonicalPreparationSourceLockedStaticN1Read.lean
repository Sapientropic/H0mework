import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedN1Return
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticLaurentCurrent

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalLockedN1Balance
open GaussCoreHilbert GaussCoreDifferential GaussCoreLabel GaussHistoryHilbert GaussFockPair
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open CanonicalGradedSpatialSource CanonicalGradedCurrent
open PreparationVacuumPhysicalLockedGaussBalance PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumWeightedChargeActionWard PreparationVacuumFieldConstraintResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalGradeZeroRead
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalSlowBlock
open PreparationVacuumPhysicalPinnedVelocity PreparationVacuumObservedPoleTensor
open PreparationVacuumObservedStaticResidue PreparationVacuumStaticSimpleCoupling
open PreparationVacuumGaugeSlowFrequency PreparationVacuumQuantumSlowResponse
open PreparationVacuumQuantumSlowResidue PreparationVacuumNoetherOrdinaryWard
open GaussUnitaryHistory SourceJointResidualEnergy SourceRetardedIncrement
open NativeHistoryGrade PreparationVacuumPhysicalAbelZeroRead PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalColorWard
open Filter
open scoped BigOperators Topology InnerProductSpace
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : Ring SourceOp:=inferInstance
local instance : Algebra ℂ SourceOp:=inferInstance
local instance : Ring SourceSuperOp:=inferInstance
local instance : Algebra ℂ SourceSuperOp:=inferInstance
attribute [local irreducible] sourceProjection actualC sourceEqualProjection sourceRetainerReturn
  sourceResonanceProjection sourceOffPoleReturn sourceFullInitialUpper sourcePinnedVelocity sourceVelocityLinear
  sourcePinnedChannel sourceStaticBase sourceBaseCross

private theorem scalar_zero {R : Type*} [Ring R] [Algebra ℂ R] (X : R) : (0:ℂ) • X=0 := zero_smul ℂ X

private theorem negative_supported {R : Type*} [Ring R] (P X : R) (fixed : P*X=X) : P*(-X)=-X := by
  rw [mul_neg,fixed]

private theorem cross_supported {R : Type*} [Ring R] (P X Y : R) (hx : P*X=X) (hy : P*Y=Y) :
    P*(-X-Y)=-X-Y := by rw [mul_sub,mul_neg,hx,hy]

private theorem eigen_cross_zero {R : Type*} [Ring R] [Algebra ℂ R]
    (H P E D : R) (a b : ℂ) (same : Commute P H)
    (left : E*H=a • E) (right : H*D=b • D) (different : a≠b) : E*P*D=0 := by
  have paid : a • (E*P*D)=b • (E*P*D) := by
    calc
      _=(E*H)*P*D := by rw [left];simp only [smul_mul_assoc]
      _=E*(H*P)*D := by simp only [mul_assoc]
      _=E*(P*H)*D := by rw [←same.eq]
      _=E*P*(H*D) := by simp only [mul_assoc]
      _=_ := by rw [right];simp only [mul_smul_comm,mul_assoc]
  have zero : (a-b) • (E*P*D)=0 := by rw [sub_smul,paid,sub_self]
  exact (smul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr different)

private theorem weighted_resolution_commutes {ι R : Type*} [Fintype ι] [Ring R] [Algebra ℂ R]
    (H P : R) (E : ι→R) (v c : ι→ℂ) (same : Commute P H)
    (resolution : ∑i,E i=1) (left : ∀i,H*E i=v i • E i) (right : ∀i,E i*H=v i • E i)
    (weight : ∀i j,v i=v j→c i=c j) : Commute P (∑i,c i • E i) := by
  have lhs : P*(∑i,c i • E i)=∑i,∑j,c i • (E j*P*E i) := by
    calc
      _=(∑j,E j)*(P*(∑i,c i • E i)) := by rw [resolution,one_mul]
      _=∑j,∑i,c i • (E j*P*E i) := by
        simp only [Finset.sum_mul,Finset.mul_sum,mul_smul_comm,mul_assoc,Finset.smul_sum]
        exact Finset.sum_comm
      _=_ := Finset.sum_comm
  have rhs : (∑j,c j • E j)*P=∑i,∑j,c j • (E j*P*E i) := by
    calc
      _=((∑j,c j • E j)*P)*(∑i,E i) := by rw [resolution,mul_one]
      _=∑j,∑i,c j • (E j*P*E i) := by
        simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_assoc]
        exact Finset.sum_comm
      _=_ := Finset.sum_comm
  change P*(∑i,c i • E i)=(∑i,c i • E i)*P
  rw [lhs,rhs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases equal : v j=v i
  · rw [weight j i equal]
  · rw [eigen_cross_zero H P (E j) (E i) (v j) (v i) same (right j) (left i) equal,smul_zero,smul_zero]

private theorem equal_projection_formula (F : GaussUnitaryHistory.Index) :
    sourceEqualProjection F=∑k : Channel F×Channel F,
      (if (-Complex.I*(sourceStaticGap F k.1 k.2:ℂ))=0 then (1:ℂ) else 0) •
        sourcePairProjection F k.1 k.2 := by
  classical
  simp only [Fintype.sum_prod_type]
  unfold sourceEqualProjection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have gate : (-Complex.I*(sourceStaticGap F i j:ℂ))=0 ↔ channelValue F i=channelValue F j := by
    simp [sourceStaticGap,Complex.ofReal_sub,sub_eq_zero,Complex.ofReal_inj]
  by_cases equal : channelValue F i=channelValue F j
  · rw [if_pos equal,if_pos (gate.mpr equal),one_smul]
  · rw [if_neg equal,if_neg (fun h=>equal (gate.mp h))]
    change (0:SourceSuperOp)=(0:ℂ) • sourcePairProjection F i j
    exact (scalar_zero (sourcePairProjection F i j)).symm

private theorem equal_projection_left (F : GaussUnitaryHistory.Index) (X : SourceOp) :
    sourceProjection*sourceEqualProjection F X=sourceEqualProjection F (sourceProjection*X) := by
  let P : SourceSuperOp:=ContinuousLinearMap.mul ℂ SourceOp sourceProjection
  have commute : Commute P (sourceStaticLiouvillian F) := by
    apply ContinuousLinearMap.ext
    intro A
    apply ContinuousLinearMap.ext
    intro x
    change sourceProjection ((-Complex.I) • (actualC 0 F (A x)-A (actualC 0 F x)))=
      (-Complex.I) • (actualC 0 F (sourceProjection (A x))-sourceProjection (A (actualC 0 F x)))
    have commute (y : H) : sourceProjection (actualC 0 F y)=actualC 0 F (sourceProjection y) :=
      congrArg (fun T : SourceOp=>T y) (actualC_sourceProjection 0 F).eq
    rw [map_smul,map_sub,commute]
  have paid:=weighted_resolution_commutes (sourceStaticLiouvillian F) P
    (fun k : Channel F×Channel F=>sourcePairProjection F k.1 k.2)
    (fun k=>(-Complex.I*(sourceStaticGap F k.1 k.2:ℂ)))
    (fun k=>if (-Complex.I*(sourceStaticGap F k.1 k.2:ℂ))=0 then (1:ℂ) else 0) commute
    (by simpa only [Fintype.sum_prod_type] using sourcePairProjection_resolution F)
    (fun k=>sourcePairProjection_static_left F k.1 k.2)
    (fun k=>sourcePairProjection_static_right F k.1 k.2) (fun i j h=>by rw [h])
  rw [←equal_projection_formula] at paid
  exact congrArg (fun A : SourceSuperOp=>A X) paid.eq

private theorem equal_projection_right (F : GaussUnitaryHistory.Index) (X : SourceOp) :
    sourceEqualProjection F X*sourceProjection=sourceEqualProjection F (X*sourceProjection) := by
  let P : SourceSuperOp:=(ContinuousLinearMap.mul ℂ SourceOp).flip sourceProjection
  have commute : Commute P (sourceStaticLiouvillian F) := by
    apply ContinuousLinearMap.ext
    intro A
    apply ContinuousLinearMap.ext
    intro x
    change (-Complex.I) • (actualC 0 F (A (sourceProjection x))-A (actualC 0 F (sourceProjection x)))=
      (-Complex.I) • (actualC 0 F (A (sourceProjection x))-A (sourceProjection (actualC 0 F x)))
    have commute : sourceProjection (actualC 0 F x)=actualC 0 F (sourceProjection x) :=
      congrArg (fun T : SourceOp=>T x) (actualC_sourceProjection 0 F).eq
    rw [commute]
  have paid:=weighted_resolution_commutes (sourceStaticLiouvillian F) P
    (fun k : Channel F×Channel F=>sourcePairProjection F k.1 k.2)
    (fun k=>(-Complex.I*(sourceStaticGap F k.1 k.2:ℂ)))
    (fun k=>if (-Complex.I*(sourceStaticGap F k.1 k.2:ℂ))=0 then (1:ℂ) else 0) commute
    (by simpa only [Fintype.sum_prod_type] using sourcePairProjection_resolution F)
    (fun k=>sourcePairProjection_static_left F k.1 k.2)
    (fun k=>sourcePairProjection_static_right F k.1 k.2) (fun i j h=>by rw [h])
  rw [←equal_projection_formula] at paid
  exact congrArg (fun A : SourceSuperOp=>A X) paid.eq

private theorem pinned_projection_commute (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    Commute sourceProjection (sourcePinnedVelocity F n) := by
  have velocity : Commute sourceProjection (sourceVelocityLinear F n) := by
    have difference : sourceVelocityLinear F n=actualC n F-actualC 0 F := by rw [actualC_affine];abel
    rw [difference]
    exact (actualC_sourceProjection n F).sub_right (actualC_sourceProjection 0 F)
  unfold sourcePinnedVelocity
  change sourceProjection*sourceEqualProjection F (sourceVelocityLinear F n)=
    sourceEqualProjection F (sourceVelocityLinear F n)*sourceProjection
  rw [equal_projection_left,equal_projection_right,velocity.eq]

private theorem pinned_channel_selfAdjoint (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (i : Channel F) :
    IsSelfAdjoint (sourcePinnedChannel F n i) := by
  cases i with
  | none =>
    rw [sourcePinnedChannel]
    change ContinuousLinearMap.adjoint (1-(supportSpan F).starProjection)=_
    have projection:=isSelfAdjoint_starProjection (supportSpan F)
    change ContinuousLinearMap.adjoint (supportSpan F).starProjection=(supportSpan F).starProjection at projection
    rw [map_sub,ContinuousLinearMap.adjoint_one,projection]
    rfl
  | some i =>
    rw [sourcePinnedChannel]
    change ContinuousLinearMap.adjoint (InnerProductSpace.rankOne ℂ
      ((sourcePinnedBasis F n) i:H) ((sourcePinnedBasis F n) i:H))=_
    exact InnerProductSpace.adjoint_rankOne _ _

private theorem pinned_channel_right (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (i : Channel F) :
    sourcePinnedChannel F n i*sourcePinnedVelocity F n=(sourcePinnedValue F n i:ℂ) • sourcePinnedChannel F n i := by
  have paid:=congrArg (fun A : SourceOp=>star A) (sourcePinnedChannel_eigen F n i)
  have V : star (sourcePinnedVelocity F n)=sourcePinnedVelocity F n:=sourcePinnedVelocity_selfAdjoint F n
  have E : star (sourcePinnedChannel F n i)=sourcePinnedChannel F n i:=pinned_channel_selfAdjoint F n i
  simpa only [star_mul,star_smul,V,E,Complex.star_def,Complex.conj_ofReal] using paid

theorem sourceLockedResonance_projection (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    Commute sourceProjection (sourceResonanceProjection F n 0) := by
  have paid:=weighted_resolution_commutes (sourcePinnedVelocity F n) sourceProjection
    (sourcePinnedChannel F n) (fun i=>(sourcePinnedValue F n i:ℂ))
    (fun i=>if sourceVelocityGap F n 0 i=0 then (1:ℂ) else 0)
    (pinned_projection_commute F n) (sourcePinnedChannel_resolution F n)
    (sourcePinnedChannel_eigen F n) (pinned_channel_right F n)
    (fun i j h=>by have same:=Complex.ofReal_injective h;rw [sourceVelocityGap,sourceVelocityGap,same])
  simpa only [sourceResonanceProjection,ite_smul,one_smul,zero_smul] using paid

theorem sourceLockedOffPole_projection (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (eta : ℝ) :
    Commute sourceProjection (sourceOffPoleReturn F n 0 eta) := by
  have paid:=weighted_resolution_commutes (sourcePinnedVelocity F n) sourceProjection
    (sourcePinnedChannel F n) (fun i=>(sourcePinnedValue F n i:ℂ))
    (fun i=>if sourceVelocityGap F n 0 i=0 then (0:ℂ) else
      ((eta:ℂ)+Complex.I*(sourceVelocityGap F n 0 i:ℂ))⁻¹)
    (pinned_projection_commute F n) (sourcePinnedChannel_resolution F n)
    (sourcePinnedChannel_eigen F n) (pinned_channel_right F n)
    (fun i j h=>by have same:=Complex.ofReal_injective h;rw [sourceVelocityGap,sourceVelocityGap,same])
  simpa only [sourceOffPoleReturn,ite_smul,zero_smul] using paid

private theorem source_projection_product : sourceProjection*sourceProjection=sourceProjection := by
  simpa only [sourceProjection,if_true] using projection_product CanonicalGradedCurrent.sourceLabel CanonicalGradedCurrent.sourceLabel

private theorem initial_upper_projection (q : PhysicalResponsePoint) (i : Fin 289) :
    sourceProjection*sourceFullInitialUpper q 0 0 i=sourceFullInitialUpper q 0 0 i := by
  unfold sourceFullInitialUpper
  rw [←mul_assoc,←mul_assoc,source_projection_product]

private theorem equal_preserves_projection (F : GaussUnitaryHistory.Index) (X : SourceOp)
    (fixed : sourceProjection*X=X) : sourceProjection*sourceEqualProjection F X=sourceEqualProjection F X := by
  rw [equal_projection_left,fixed]

private theorem retainer_preserves_projection (F : GaussUnitaryHistory.Index) (X : SourceOp)
    (fixed : sourceProjection*X=X) : sourceProjection*sourceRetainerReturn F X=sourceRetainerReturn F X := by
  rw [sourceRetainerReturn_apply,mul_smul_comm,←mul_assoc,fixed]

private theorem multiply_preserves_projection (A X : SourceOp) (commute : Commute sourceProjection A)
    (fixed : sourceProjection*X=X) : sourceProjection*(A*X)=A*X := by rw [←mul_assoc,commute.eq,mul_assoc,fixed]

/-- The actual double pole retains its source-supported grade; the full R0 itself is not truncated. -/
theorem sourceLockedStaticBase_projection (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) :
    sourceProjection*sourceStaticBase q n i=sourceStaticBase q n i := by
  have fixed : sourceProjection*(sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
      (sourceRetainerReturn q.F (sourceResonanceProjection q.F n 0*
        sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))))=
    sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
      (sourceRetainerReturn q.F (sourceResonanceProjection q.F n 0*
        sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))) :=
    multiply_preserves_projection _ _ (sourceLockedResonance_projection q.F n)
    (equal_preserves_projection _ _ (retainer_preserves_projection _ _
      (multiply_preserves_projection _ _ (sourceLockedResonance_projection q.F n)
        (equal_preserves_projection _ _ (initial_upper_projection q i)))))
  unfold sourceStaticBase
  exact negative_supported sourceProjection _ fixed

/-- Both actual simple cross terms retain their source-supported grade, including the full uncut retainer. -/
theorem sourceLockedStaticCross_projection (q : PhysicalResponsePoint) (n : PhysicalMomentum) (eta : ℝ) (i : Fin 289) :
    sourceProjection*sourceBaseCross q n eta i=sourceBaseCross q n eta i := by
  have first : sourceProjection*(sourceOffPoleReturn q.F n 0 eta*sourceEqualProjection q.F
      (sourceRetainerReturn q.F (sourceResonanceProjection q.F n 0*
        sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))))=
    sourceOffPoleReturn q.F n 0 eta*sourceEqualProjection q.F
      (sourceRetainerReturn q.F (sourceResonanceProjection q.F n 0*
        sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))) :=
    multiply_preserves_projection _ _ (sourceLockedOffPole_projection q.F n eta)
    (equal_preserves_projection _ _ (retainer_preserves_projection _ _
      (multiply_preserves_projection _ _ (sourceLockedResonance_projection q.F n)
        (equal_preserves_projection _ _ (initial_upper_projection q i)))))
  have second : sourceProjection*(sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
      (sourceRetainerReturn q.F (sourceOffPoleReturn q.F n 0 eta*
        sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))))=
    sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
      (sourceRetainerReturn q.F (sourceOffPoleReturn q.F n 0 eta*
        sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))) :=
    multiply_preserves_projection _ _ (sourceLockedResonance_projection q.F n)
    (equal_preserves_projection _ _ (retainer_preserves_projection _ _
      (multiply_preserves_projection _ _ (sourceLockedOffPole_projection q.F n eta)
        (equal_preserves_projection _ _ (initial_upper_projection q i)))))
  unfold sourceBaseCross
  exact cross_supported sourceProjection _ _ first second

private theorem supported_N1_core (F : GaussUnitaryHistory.Index) (y : H) (fixed : sourceProjection y=y) :
    sourceN1Core (sourceTestApprox F y)=sourceTestApprox F y := by
  have all : sourceN1Projection y=y:=by rw [←fixed,sourceN1Projection_source,fixed]
  have paid:=congrArg (sourceTestApprox F) all
  unfold sourceN1Projection at paid
  rw [add_apply,sourceTestApprox_add] at paid
  simpa only [sourceN1Core,sourceProjection,sourceExcitedProjection,sourceTestApprox_projection] using paid

private theorem supported_pair (F : GaussUnitaryHistory.Index) (y : H) (fixed : sourceProjection y=y) :
    sourceLockedPairCore (sourceTestApprox F y)=0 :=
  (congrArg sourceLockedPairCore (supported_N1_core F y fixed)).symm.trans (sourceLockedPair_sourceN1_zero _)

private theorem supported_full_pair (F : GaussUnitaryHistory.Index) (y : H) (fixed : sourceProjection y=y) (p : PhysicalMomentum) :
    sourceLockedPairCore (fullSourceAction p (sourceTestApprox F y))=0 :=
  (congrArg (fun f : QuantumTest=>sourceLockedPairCore (fullSourceAction p f))
    (supported_N1_core F y fixed)).symm.trans (sourceLockedPair_fullSource_N1_zero p _)

/-- The exact nested double pole's actual state generates pair-free full action torque. -/
theorem sourceLockedStaticBase_pairTorque (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (i : Fin 289) (y : H) (p k : PhysicalMomentum) :
    sourceLockedPairTorque p k (sourceTestApprox q.F (sourceStaticBase q n i y))=0 := by
  have fixed : sourceProjection (sourceStaticBase q n i y)=sourceStaticBase q n i y :=
    congrArg (fun A : SourceOp=>A y) (sourceLockedStaticBase_projection q n i)
  unfold sourceLockedPairTorque
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,supported_pair q.F _ fixed,map_zero,
    supported_full_pair q.F _ fixed p,sub_zero]

/-- Both exact nested cross states generate the same pair-free full action torque. -/
theorem sourceLockedStaticCross_pairTorque (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (eta : ℝ) (i : Fin 289) (y : H) (p k : PhysicalMomentum) :
    sourceLockedPairTorque p k (sourceTestApprox q.F (sourceBaseCross q n eta i y))=0 := by
  have fixed : sourceProjection (sourceBaseCross q n eta i y)=sourceBaseCross q n eta i y :=
    congrArg (fun A : SourceOp=>A y) (sourceLockedStaticCross_projection q n eta i)
  unfold sourceLockedPairTorque
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,supported_pair q.F _ fixed,map_zero,
    supported_full_pair q.F _ fixed p,sub_zero]

end LowEnergy.PreparationVacuumPhysicalLockedN1Balance
