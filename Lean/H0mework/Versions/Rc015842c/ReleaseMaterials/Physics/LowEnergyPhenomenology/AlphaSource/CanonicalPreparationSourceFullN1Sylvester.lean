import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaugeHalfSylvester

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumGaugeSlowFrequency
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumSharedPoleCarrier CanonicalGradedCurrent
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumCausalPoleResponse PreparationVacuumOriginalGreenFeedback SourcePropagationNativeActionHessian
open SourceFiniteUnitary MeasureTheory Filter Set
open scoped Topology BigOperators InnerProductSpace Matrix
attribute [local irreducible] actualC actualA rawReader sourcePoleRead rawHalf rawInitial jointGenerator
  sourceProjection sourceExcitedProjection sourceSylvester sourceVelocityLinear

def sourceFullRawHalf (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (i : Fin 289) (lambda : ℂ) : H→L[ℂ] H:=
  rawHalf (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i) lambda

def sourceFullHalfBase (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (i : Fin 289) (lambda : ℂ) : H→L[ℂ] H:=
  sourceProjection*sourceFullRawHalf q pL pR i lambda*sourceProjection

def sourceFullHalfUpper (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (i : Fin 289) (lambda : ℂ) : H→L[ℂ] H:=
  sourceProjection*sourceFullRawHalf q pL pR i lambda*sourceExcitedProjection

def sourceFullInitialBase (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (i : Fin 289) : H→L[ℂ] H:=
  sourceProjection*rawInitial (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i)*sourceProjection

def sourceFullInitialUpper (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (i : Fin 289) : H→L[ℂ] H:=
  sourceProjection*rawInitial (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i)*sourceExcitedProjection

attribute [local irreducible] sourceFullRawHalf sourceFullHalfBase sourceFullHalfUpper sourceFullInitialBase sourceFullInitialUpper

private theorem fullRawHalf_pencil (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (i : Fin 289) (lambda : ℂ) (positive : 0<lambda.re) :
    lambda • sourceFullRawHalf q pL pR i lambda-
      Complex.I • (jointGenerator pL q.F 0 0*sourceFullRawHalf q pL pR i lambda)+
      Complex.I • (sourceFullRawHalf q pL pR i lambda*jointGenerator pR q.F 0 0)=
        rawInitial (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i):=by
  have source:=rawHalf_pencil (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i) lambda positive
  rw [propagationPencil_actual,leftGenerator,rightGenerator,sourcePhysicalMaterialPoint_left,sourcePhysicalMaterialPoint_right] at source
  unfold sourceFullRawHalf
  convert! source using 1
  apply ContinuousLinearMap.ext
  intro x
  simp only [sourcePhysicalMaterialPoint,add_apply,sub_apply,smul_apply,mul_apply_eq_comp,map_smul]
  module

private theorem project_pencil {R : Type*} [Ring R] [Algebra ℂ R]
    (P Q L R₀ C D X B E : R) (lambda : ℂ)
    (left : P*L=C*P) (right : R₀*Q=Q*D+E)
    (equation : lambda • X-Complex.I • (L*X)+Complex.I • (X*R₀)=B) :
    lambda • (P*X*Q)-Complex.I • (C*(P*X*Q))+Complex.I • ((P*X*Q)*D)=
      P*B*Q-Complex.I • (P*X*E):=by
  have projected:=congrArg (fun Z : R=>P*Z*Q) equation
  have leftTerm : P*(L*X)*Q=C*(P*X*Q):=by
    calc
      _=(P*L)*X*Q:=by noncomm_ring
      _= _:=by rw [left];noncomm_ring
  have rightTerm : P*(X*R₀)*Q=(P*X*Q)*D+P*X*E:=by
    calc
      _=P*X*(R₀*Q):=by noncomm_ring
      _= _:=by rw [right];noncomm_ring
  simp only [mul_add,mul_sub,add_mul,sub_mul,mul_smul_comm,smul_mul_assoc,leftTerm,rightTerm,smul_add] at projected
  apply (eq_sub_iff_add_eq).mpr
  convert! projected using 1
  module

private theorem source_left_generator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceProjection*jointGenerator p F 0 0=actualC p F*sourceProjection:=by
  rw [actualGenerator_source,mul_add,actualA_sourceProjection,add_zero]
  exact (actualC_sourceProjection p F).eq

private theorem source_upper_generator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    jointGenerator p F 0 0*sourceExcitedProjection=sourceExcitedProjection*actualC p F+0:=by
  rw [actualGenerator_source,add_mul,actualA_N1G1_zero,add_zero,add_zero]
  exact (actualC_excitedProjection p F).eq.symm

private theorem source_base_generator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    jointGenerator p F 0 0*sourceProjection=
      sourceProjection*actualC p F+sourceExcitedProjection*actualA p F*sourceProjection:=by
  rw [actualGenerator_source,add_mul,←(actualC_sourceProjection p F).eq,actualA_N1G0_range]

/-- The actual N1 upper sector obeys the same C-Liouvillian with its own original initial operator. -/
theorem sourceFullHalfUpper_sylvester (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (i : Fin 289) (lambda : ℂ) (positive : 0<lambda.re) :
    sourceSylvester q pL pR lambda (sourceFullHalfUpper q pL pR i lambda)=sourceFullInitialUpper q pL pR i:=by
  have generated:=project_pencil sourceProjection sourceExcitedProjection (jointGenerator pL q.F 0 0)
    (jointGenerator pR q.F 0 0) (actualC pL q.F) (actualC pR q.F)
    (sourceFullRawHalf q pL pR i lambda) (rawInitial (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i)) 0 lambda
    (source_left_generator pL q.F) (source_upper_generator pR q.F) (fullRawHalf_pencil q pL pR i lambda positive)
  simpa only [sourceSylvester_apply,sourceFullHalfUpper,sourceFullInitialUpper,mul_zero,smul_zero,sub_zero] using generated

/-- The full current keeps the original retainer-driven upper-sector return. -/
theorem sourceFullHalfBase_sylvester (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (i : Fin 289) (lambda : ℂ) (positive : 0<lambda.re) :
    sourceSylvester q pL pR lambda (sourceFullHalfBase q pL pR i lambda)=
      sourceFullInitialBase q pL pR i-
        Complex.I • (sourceFullHalfUpper q pL pR i lambda*(actualA pR q.F*sourceProjection)):=by
  have generated:=project_pencil sourceProjection sourceProjection (jointGenerator pL q.F 0 0)
    (jointGenerator pR q.F 0 0) (actualC pL q.F) (actualC pR q.F)
    (sourceFullRawHalf q pL pR i lambda) (rawInitial (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i))
    (sourceExcitedProjection*actualA pR q.F*sourceProjection) lambda
    (source_left_generator pL q.F) (source_base_generator pR q.F) (fullRawHalf_pencil q pL pR i lambda positive)
  simpa only [sourceSylvester_apply,sourceFullHalfBase,sourceFullHalfUpper,sourceFullInitialBase,mul_assoc] using generated

private theorem sourceRead_both_projection (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (X : H→L[ℂ] H) :
    sourcePoleRead q.epsilon q.precision pL pR l r (sourceProjection*X*sourceProjection)=
      sourcePoleRead q.epsilon q.precision pL pR l r X:=by
  rw [sourcePoleRead_actual,sourcePoleRead_actual]
  simp only [mul_apply_eq_comp,sourcePolePrepared_sourceProjection]
  have paired : inner ℂ (sourceProjection (sourcePolePrepared q.epsilon q.precision pL l))
      (X (sourcePolePrepared q.epsilon q.precision pR r))=
      inner ℂ (sourcePolePrepared q.epsilon q.precision pL l)
        (sourceProjection (X (sourcePolePrepared q.epsilon q.precision pR r))):=by
    unfold sourceProjection
    exact NativeHistoryGrade.projection_symmetric _ _ _
  rw [sourcePolePrepared_sourceProjection] at paired
  exact paired.symm

/-- All 289 original current slots read the base operator of this coupled system. -/
theorem sourceFullHalf_actualCurrent (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (i : Fin 289) (lambda : ℂ) (positive : 0<lambda.re) :
    sourcePoleCurrentHalf q pL pR l r lambda i=
      -sourcePoleRead q.epsilon q.precision pL pR l r (sourceFullHalfBase q pL pR i lambda):=by
  rw [sourceFullHalfBase,sourceRead_both_projection]
  have returned:=(sourcePoleRead q.epsilon q.precision pL pR l r).integral_comp_comm
    (rawFlow_integrable (sourcePhysicalMaterialPoint q pL pR) (fieldUnit i) lambda positive)
  unfold sourcePoleCurrentHalf
  simp_rw [sourcePoleActionEuler_source,mul_neg]
  rw [integral_neg]
  simpa only [map_smul,smul_eq_mul,rawFlow,sourcePhysicalMaterialPoint,sourceMaterialTransfer,sourceFullRawHalf,rawHalf] using congrArg Neg.neg returned

theorem sourceFullHalf_common_carrier (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (i : Fin 289) (lambda : ℂ) (positive : 0<lambda.re) :
    movingOverlap pL*(show Matrix RestStateIndex RestStateIndex ℂ from fun l r=>
      sourcePoleCurrentHalf q pL pR l r lambda i)*(movingOverlap pR).conjTranspose=
      -sourceTensor q.epsilon q.precision 0 0 (sourceFullHalfBase q pL pR i lambda):=by
  have current : (show Matrix RestStateIndex RestStateIndex ℂ from fun l r=>
      sourcePoleCurrentHalf q pL pR l r lambda i)=
        -sourceTensor q.epsilon q.precision pL pR (sourceFullHalfBase q pL pR i lambda):=by
    ext l r
    exact sourceFullHalf_actualCurrent q pL pR l r i lambda positive
  rw [current,mul_neg,neg_mul,sourceTensor_same_carrier]

/-- Both actual source equations retain the slow momentum-frequency coupling and the N1 retainer term. -/
theorem sourceFullHalf_slow_system (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re) (i : Fin 289) :
    let X0:=sourceFullHalfBase q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    let X1:=sourceFullHalfUpper q (-(delta • n)) 0 i ((delta:ℂ)*zeta)
    ((delta:ℂ) • (zeta • X1+Complex.I • (sourceVelocityLinear q.F n*X1))-
      Complex.I • (actualC 0 q.F*X1-X1*actualC 0 q.F)=sourceFullInitialUpper q (-(delta • n)) 0 i) ∧
    ((delta:ℂ) • (zeta • X0+Complex.I • (sourceVelocityLinear q.F n*X0))-
      Complex.I • (actualC 0 q.F*X0-X0*actualC 0 q.F)=sourceFullInitialBase q (-(delta • n)) 0 i-
        Complex.I • (X1*(actualA 0 q.F*sourceProjection))):=by
  have positive : 0<((delta:ℂ)*zeta).re:=by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positiveDelta positiveZeta
  have upper:=sourceFullHalfUpper_sylvester q (-(delta • n)) 0 i ((delta:ℂ)*zeta) positive
  have base:=sourceFullHalfBase_sylvester q (-(delta • n)) 0 i ((delta:ℂ)*zeta) positive
  rw [sourceSylvester_scaled] at upper base
  exact ⟨upper,base⟩

theorem sourceFullRawHalf_gauge (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) :
    sourceFullRawHalf q pL pR (gaugeSlot mu a) lambda=sourceGaugeRawHalf q pL pR mu a lambda:=by
  unfold sourceFullRawHalf sourceGaugeRawHalf
  rfl

theorem sourceFullHalfBase_gauge (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (positive : 0<lambda.re)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceFullHalfBase q pL pR (gaugeSlot mu a) lambda=sourceGaugeHalf q pL pR mu a lambda:=by
  unfold sourceFullHalfBase
  rw [sourceFullRawHalf_gauge]
  exact sourceGaugeHalf_rightProjection q pL pR mu a lambda positive nonrealL nonrealR

theorem sourceFullHalfUpper_gauge_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (positive : 0<lambda.re)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceFullHalfUpper q pL pR (gaugeSlot mu a) lambda=0:=by
  have orthogonal : sourceProjection*sourceExcitedProjection=0:=by
    unfold sourceProjection sourceExcitedProjection
    rw [NativeHistoryGrade.projection_product]
    norm_num [sourceLabel,sourceExcitedLabel]
  unfold sourceFullHalfUpper
  rw [sourceFullRawHalf_gauge]
  change sourceGaugeHalf q pL pR mu a lambda*sourceExcitedProjection=0
  rw [←sourceGaugeHalf_rightProjection q pL pR mu a lambda positive nonrealL nonrealR,mul_assoc,orthogonal,mul_zero]

/-- The coupled full-current source remains the forcing of the original causal field with every compatibility row. -/
theorem sourceFullHalf_causal_field (q : PhysicalResponsePoint) (p k : PhysicalMomentum) (l r : RestStateIndex)
    (frequency : CausalFrequency k) :
    let J : Fin 289→ℂ:=fun i=> -sourcePoleRead q.epsilon q.precision (p-k) p l r
      (sourceFullHalfBase q (p-k) p i frequency.val)
    nativeFourierHessian nativeHessian (fixedMomentum k frequency.val)*ᵥ
        PreparationVacuumOriginalGreenFeedback.sourceField (causalPoint k frequency) J=
      J-originalRowLift (fixedMomentum k frequency.val)*ᵥ
        (nullProjection*ᵥcausalHalfCosource q p k l r frequency):=by
  have same : (fun i=> -sourcePoleRead q.epsilon q.precision (p-k) p l r
      (sourceFullHalfBase q (p-k) p i frequency.val))=causalHalfCurrent q p k l r frequency:=by
    funext i
    exact (sourceFullHalf_actualCurrent q (p-k) p l r i frequency.val frequency.property.1).symm
  dsimp only
  rw [same]
  exact causalHalfField_whole q p k l r frequency

end LowEnergy.PreparationVacuumGaugeSlowFrequency
