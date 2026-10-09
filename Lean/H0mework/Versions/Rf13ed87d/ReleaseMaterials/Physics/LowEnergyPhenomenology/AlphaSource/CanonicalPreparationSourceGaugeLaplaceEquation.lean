import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCommonCausalReturn

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

def sourceGaugeRawHalf (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) : H→L[ℂ] H:=
  rawHalf (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) lambda

def sourceGaugeHalf (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) : H→L[ℂ] H:=
  sourceProjection*sourceGaugeRawHalf q pL pR mu a lambda

def sourceGaugeInitial (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (mu : Fin 4) (a : Fin 12) : H→L[ℂ] H:=
  sourceProjection*rawInitial (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a)

def sourceSylvester (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (lambda : ℂ) :
    (H→L[ℂ] H)→L[ℂ] (H→L[ℂ] H):=
  lambda • ContinuousLinearMap.id ℂ (H→L[ℂ] H)-
    Complex.I • (ContinuousLinearMap.mul ℂ (H→L[ℂ] H) (actualC pL q.F))+
    Complex.I • ((ContinuousLinearMap.mul ℂ (H→L[ℂ] H)).flip (actualC pR q.F))

theorem sourceSylvester_apply (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (lambda : ℂ) (X : H→L[ℂ] H) :
    sourceSylvester q pL pR lambda X=lambda • X-Complex.I • (actualC pL q.F*X)+Complex.I • (X*actualC pR q.F):=rfl

attribute [local irreducible] sourceGaugeRawHalf sourceGaugeHalf sourceGaugeInitial

private theorem rawFlow_material (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (t : ℝ) :
    rawFlow (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) t=
      fiveKernel (gaugeField mu a) pR (pL-pR) q.F q.z q.w t 0:=rfl

/-- The source grade return is an equality on the original fulljoint time word. -/
theorem sourceGaugeRawFlow_projected (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceProjection*rawFlow (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) t=
      sourceGaugeZeroHistoryKernel q pL pR mu a t*sourceProjection:=by
  rw [rawFlow_material]
  exact sourceGaugeKernel_projected q pL pR mu a t nonrealL nonrealR

/-- Both-sided source support is generated before any spectral projection or slow limit. -/
theorem sourceGaugeHalf_rightProjection (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (positive : 0<lambda.re)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceGaugeHalf q pL pR mu a lambda*sourceProjection=sourceGaugeHalf q pL pR mu a lambda:=by
  let L : (H→L[ℂ] H)→L[ℂ] (H→L[ℂ] H):=ContinuousLinearMap.mul ℂ (H→L[ℂ] H) sourceProjection
  let R : (H→L[ℂ] H)→L[ℂ] (H→L[ℂ] H):=(ContinuousLinearMap.mul ℂ (H→L[ℂ] H)).flip sourceProjection
  have integrable:=rawFlow_integrable (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) lambda positive
  have left:=L.integral_comp_comm integrable
  have both:=(R.comp L).integral_comp_comm integrable
  have same (t : ℝ) : (R.comp L) (laplaceWeight lambda t • rawFlow (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) t)=
      L (laplaceWeight lambda t • rawFlow (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) t):=by
    change (sourceProjection*(laplaceWeight lambda t • rawFlow (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) t))*sourceProjection=
      sourceProjection*(laplaceWeight lambda t • rawFlow (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) t)
    rw [mul_smul_comm,smul_mul_assoc,sourceGaugeRawFlow_projected q pL pR mu a t nonrealL nonrealR,
      mul_assoc,sourceProjection_square]
  simp_rw [same] at both
  unfold sourceGaugeHalf sourceGaugeRawHalf rawHalf
  exact both.symm.trans left

theorem sourceGaugeHalf_leftProjection (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) :
    sourceProjection*sourceGaugeHalf q pL pR mu a lambda=sourceGaugeHalf q pL pR mu a lambda:=by
  rw [sourceGaugeHalf,←mul_assoc,sourceProjection_square]

/-- The actual material initial operator is retained, including both fulljoint resolvents. -/
theorem sourceGaugeRawHalf_pencil (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (positive : 0<lambda.re) :
    lambda • sourceGaugeRawHalf q pL pR mu a lambda-
      Complex.I • (jointGenerator pL q.F 0 0*sourceGaugeRawHalf q pL pR mu a lambda)+
      Complex.I • (sourceGaugeRawHalf q pL pR mu a lambda*jointGenerator pR q.F 0 0)=
        rawInitial (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a):=by
  have source:=rawHalf_pencil (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) lambda positive
  rw [propagationPencil_actual,leftGenerator,rightGenerator,sourcePhysicalMaterialPoint_left,sourcePhysicalMaterialPoint_right] at source
  unfold sourceGaugeRawHalf
  convert! source using 1
  apply ContinuousLinearMap.ext
  intro x
  simp only [sourcePhysicalMaterialPoint,add_apply,sub_apply,smul_apply,mul_apply_eq_comp,map_smul]
  module

private theorem sourcePoleRead_projected (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (X : H→L[ℂ] H) :
    sourcePoleRead q.epsilon q.precision pL pR l r (sourceProjection*X)=
      sourcePoleRead q.epsilon q.precision pL pR l r X:=by
  rw [sourcePoleRead_actual,sourcePoleRead_actual]
  change inner ℂ (sourcePolePrepared q.epsilon q.precision pL l)
      (sourceProjection (X (sourcePolePrepared q.epsilon q.precision pR r)))=_
  have paired : inner ℂ (sourceProjection (sourcePolePrepared q.epsilon q.precision pL l))
      (X (sourcePolePrepared q.epsilon q.precision pR r))=
      inner ℂ (sourcePolePrepared q.epsilon q.precision pL l)
        (sourceProjection (X (sourcePolePrepared q.epsilon q.precision pR r))):=by
    unfold sourceProjection
    exact NativeHistoryGrade.projection_symmetric _ _ _
  rw [sourcePolePrepared_sourceProjection] at paired
  exact paired.symm

/-- The unchanged fulljoint actual gauge current reads this generated operator. -/
theorem sourceGaugeHalf_actualCurrent (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (positive : 0<lambda.re) :
    sourcePoleCurrentHalf q pL pR l r lambda (gaugeSlot mu a)=
      -sourcePoleRead q.epsilon q.precision pL pR l r (sourceGaugeHalf q pL pR mu a lambda):=by
  rw [sourceGaugeHalf,sourcePoleRead_projected]
  have returned:=(sourcePoleRead q.epsilon q.precision pL pR l r).integral_comp_comm
    (rawFlow_integrable (sourcePhysicalMaterialPoint q pL pR) (gaugeField mu a) lambda positive)
  unfold sourcePoleCurrentHalf
  simp_rw [sourcePoleActionEuler_source]
  change (∫t in Ioi (0:ℝ),laplaceWeight lambda t*(-sourcePoleRead q.epsilon q.precision pL pR l r
    (fiveKernel (gaugeField mu a) pR (pL-pR) q.F q.z q.w t 0)))=_
  simp only [mul_neg]
  rw [integral_neg]
  simpa only [map_smul,smul_eq_mul,rawFlow_material,sourceGaugeRawHalf,rawHalf] using congrArg Neg.neg returned

end LowEnergy.PreparationVacuumGaugeSlowFrequency
