import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaugeLaplaceEquation

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumGaugeSlowFrequency
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumSharedPoleCarrier CanonicalGradedCurrent
open SourceFiniteUnitary MeasureTheory Filter Set
open scoped Topology BigOperators InnerProductSpace
attribute [local irreducible] actualC actualA rawReader sourcePoleRead rawHalf rawInitial jointGenerator sourceProjection
  sourceGaugeHalf sourceGaugeRawHalf sourceGaugeInitial sourceSylvester sourceVelocityLinear

/-- The initial response is generated from the same two material resolvents and the original gauge reader. -/
theorem sourceGaugeInitial_material_legs (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceGaugeInitial q pL pR mu a=
      (CanonicalPhysicalResolvent.finiteResolvent pL q.F q.z*rawReader (gaugeField mu a) pR q.F 0*
        CanonicalPhysicalResolvent.finiteResolvent pR q.F q.w)*sourceProjection:=by
  have generated:=sourceGaugeRawFlow_projected q pL pR mu a 0 nonrealL nonrealR
  have initial : rawFlow (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) 0=
      rawInitial (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a):=
    rawKernel_initial (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a)
  rw [initial] at generated
  simpa only [sourceGaugeInitial,sourceGaugeZeroHistoryKernel,neg_zero,time_zero,one_mul,mul_one] using generated

private theorem sourceProjection_generator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceProjection*jointGenerator p F 0 0=actualC p F*sourceProjection:=by
  rw [actualGenerator_source,mul_add,actualA_sourceProjection,add_zero]
  exact (actualC_sourceProjection p F).eq

private theorem supported_generator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (X : H→L[ℂ] H) (supported : X*sourceProjection=X) :
    X*jointGenerator p F 0 0=X*actualC p F:=by
  calc
    _=(X*sourceProjection)*jointGenerator p F 0 0:=by rw [supported]
    _=X*(sourceProjection*jointGenerator p F 0 0):=mul_assoc _ _ _
    _=X*(sourceProjection*actualC p F):=by
      rw [sourceProjection_generator,←(actualC_sourceProjection p F).eq]
    _=(X*sourceProjection)*actualC p F:=(mul_assoc _ _ _).symm
    _= _:=by rw [supported]

/-- Source grade support removes the retainer from this actual gauge response after the fulljoint half equation is generated. -/
theorem sourceGaugeHalf_sylvester (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (positive : 0<lambda.re)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceSylvester q pL pR lambda (sourceGaugeHalf q pL pR mu a lambda)=sourceGaugeInitial q pL pR mu a:=by
  have source:=congrArg (fun X : H→L[ℂ] H=>sourceProjection*X)
    (sourceGaugeRawHalf_pencil q pL pR mu a lambda positive)
  have left : sourceProjection*(jointGenerator pL q.F 0 0*sourceGaugeRawHalf q pL pR mu a lambda)=
      actualC pL q.F*sourceGaugeHalf q pL pR mu a lambda:=by
    rw [←mul_assoc,sourceProjection_generator,mul_assoc,sourceGaugeHalf]
  have right : sourceProjection*(sourceGaugeRawHalf q pL pR mu a lambda*jointGenerator pR q.F 0 0)=
      sourceGaugeHalf q pL pR mu a lambda*actualC pR q.F:=by
    rw [←mul_assoc]
    unfold sourceGaugeHalf
    simpa only [sourceGaugeHalf] using supported_generator pR q.F _
      (sourceGaugeHalf_rightProjection q pL pR mu a lambda positive nonrealL nonrealR)
  simp only [mul_add,mul_sub,mul_smul_comm,left,right] at source
  simpa only [sourceSylvester_apply,sourceGaugeHalf,sourceGaugeInitial] using source

/-- The generator's momentum dependence is paid by the original source action, not by continuous moving labels. -/
theorem sourceLeftGenerator_scaled (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (delta : ℝ) :
    actualC (-(delta • n)) F=actualC 0 F-(delta:ℂ) • sourceVelocityLinear F n:=by
  rw [actualC_affine,map_neg,map_smul]
  apply ContinuousLinearMap.ext
  intro x
  simp only [add_apply,neg_apply,sub_apply,smul_apply]
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  module

theorem sourceSylvester_scaled (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ) (zeta : ℂ)
    (X : H→L[ℂ] H) :
    sourceSylvester q (-(delta • n)) 0 ((delta:ℂ)*zeta) X=
      (delta:ℂ) • (zeta • X+Complex.I • (sourceVelocityLinear q.F n*X))-
        Complex.I • (actualC 0 q.F*X-X*actualC 0 q.F):=by
  rw [sourceSylvester_apply q (-(delta • n)) 0 ((delta:ℂ)*zeta) X]
  apply ContinuousLinearMap.ext
  intro x
  simp only [add_apply,sub_apply,smul_apply,mul_apply_eq_comp]
  have shift:=congrArg (fun A : H→L[ℂ] H=>A (X x)) (sourceLeftGenerator_scaled q.F n delta)
  simp only [sub_apply,smul_apply] at shift
  rw [shift]
  module

/-- Exact moving-source slow-frequency equation; its off-diagonal commutator remains part of the actual response. -/
theorem sourceGaugeHalf_slow_equation (q : PhysicalResponsePoint) (n : PhysicalMomentum) (delta : ℝ)
    (positiveDelta : 0<delta) (zeta : ℂ) (positiveZeta : 0<zeta.re)
    (mu : Fin 4) (a : Fin 12) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    let X:=sourceGaugeHalf q (-(delta • n)) 0 mu a ((delta:ℂ)*zeta)
    (delta:ℂ) • (zeta • X+Complex.I • (sourceVelocityLinear q.F n*X))-
      Complex.I • (actualC 0 q.F*X-X*actualC 0 q.F)=sourceGaugeInitial q (-(delta • n)) 0 mu a:=by
  have positive : 0<((delta:ℂ)*zeta).re:=by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positiveDelta positiveZeta
  have source:=sourceGaugeHalf_sylvester q (-(delta • n)) 0 mu a ((delta:ℂ)*zeta) positive nonrealL nonrealR
  rw [sourceSylvester_scaled] at source
  exact source

/-- The moving half-current matrix returns to the same fixed eight-state carrier before any slow limit. -/
theorem sourceGaugeHalf_common_carrier (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (positive : 0<lambda.re) :
    movingOverlap pL*(show Matrix RestStateIndex RestStateIndex ℂ from fun l r=>
      sourcePoleCurrentHalf q pL pR l r lambda (gaugeSlot mu a))*(movingOverlap pR).conjTranspose=
      -sourceTensor q.epsilon q.precision 0 0 (sourceGaugeHalf q pL pR mu a lambda):=by
  have current : (show Matrix RestStateIndex RestStateIndex ℂ from fun l r=>
      sourcePoleCurrentHalf q pL pR l r lambda (gaugeSlot mu a))=
        -sourceTensor q.epsilon q.precision pL pR (sourceGaugeHalf q pL pR mu a lambda):=by
    ext l r
    exact sourceGaugeHalf_actualCurrent q pL pR l r mu a lambda positive
  rw [current,mul_neg,neg_mul,sourceTensor_same_carrier]

end LowEnergy.PreparationVacuumGaugeSlowFrequency
