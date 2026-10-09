import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationActualFieldInverse

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationFieldFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil SourcePropagationResolvent
open PreparationVacuumPhysicalTailPrice PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
open SourcePropagationSpectralAxis
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ TransferOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ TransferOp:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedSpace ℝ TransferOp:=ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ TransferOp:=by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=TransferOp)) using 1
local instance : ContinuousSMul ℝ TransferOp:=by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=TransferOp)) using 1
local instance : ContinuousENorm TransferOp:=by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=TransferOp)) using 1
local instance : AddCommGroup TransferOp:=ContinuousLinearMap.addCommGroup
local instance : IsTopologicalAddGroup TransferOp:=by
  have normal : @IsTopologicalAddGroup TransferOp
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup.toAddGroup:=inferInstance
  convert! normal using 1
local instance : IsScalarTower ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  rfl⟩
local instance : SMulCommClass ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  exact (map_smul A c (B X)).symm⟩

open PreparationVacuumOriginalGreenFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumRealReaction
attribute [local irreducible] fieldInverse sourceRead sourceGreen jointResolvent jointCurrent
  rawReader rawReaderContact originalJacobi originalReadback originalRowLift sourceCompatibility

def backgroundInitial (q : PhysicalResponsePoint) (reader : Field289) (h : Field289) : Op:=
  fiveKernel reader q.p q.k q.F q.z q.w 0 h

theorem backgroundInitial_at_source (q : PhysicalResponsePoint) (reader : Field289) :
    backgroundInitial q reader 0=rawInitial q reader:=rawKernel_initial q reader

theorem backgroundInitial_C2 (q : PhysicalResponsePoint) (reader : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) : ContDiffAt ℝ 2 (backgroundInitial q reader) 0 :=by
  have generated:=((jointResolvent_C2 (q.p+q.k) q.F q.z hz).mul (rawReader_C2 reader q.p q.F)).mul
    (jointResolvent_C2 q.p q.F q.w hw)
  convert! generated using 1
  funext h
  simp only [backgroundInitial,fiveKernel,neg_zero,physicalTime_initial,one_mul,mul_one,Pi.mul_apply]

theorem backgroundInitial_derivative (q : PhysicalResponsePoint) (reader force : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>backgroundInitial q reader (r • force)) (slopeInitial q reader force) 0 :=by
  have generated:=fiveKernel_generated reader force q.p q.k q.F q.z q.w hz hw 0
  rw [slopeKernel_initial] at generated
  exact generated

/-- Restriction changes scalar presentation, while preserving every complete operator value. -/
def asRealOperator : TransferOp→L[ℝ] (Op→L[ℝ] Op):=
  ContinuousLinearMap.restrictScalarsL ℂ Op Op ℝ ℝ

def realOperatorMap :
    @ContinuousLinearMap ℝ ℝ inferInstance inferInstance (RingHom.id ℝ) TransferOp
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup.toAddCommMonoid
      (Op→L[ℝ] Op) (inferInstance : PseudoMetricSpace (Op→L[ℝ] Op)).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup (Op→L[ℝ] Op)).toAddCommGroup.toAddCommMonoid
      (inferInstance : NormedSpace ℝ TransferOp).toModule
      (inferInstance : NormedSpace ℝ (Op→L[ℝ] Op)).toModule:=by
  convert! asRealOperator using 1

theorem realOperatorMap_apply (T : TransferOp) (A : Op) : realOperatorMap T A=T A:=rfl

/-- Full source frequency response at the same original field background. -/
def backgroundOperator (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ) (h : Field289) : Op:=
  fieldInverse q lambda h (backgroundInitial q reader h)

theorem backgroundOperator_C2 (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ)
    (off : lambda.re≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    ContDiffAt ℝ 2 (backgroundOperator q reader lambda) 0 :=by
  have inverse:=(ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=TransferOp) (F:=Op→L[ℝ] Op) realOperatorMap).contDiffAt.comp 0 (fieldInverse_C2 q lambda off)
  have generated:=inverse.clm_apply (backgroundInitial_C2 q reader hz hw)
  convert! generated using 1

theorem backgroundOperator_initial (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ)
    (positive : 0<lambda.re) :
    backgroundOperator q reader lambda 0=rawHalf q reader lambda :=by
  unfold backgroundOperator
  rw [fieldInverse_initial q lambda (ne_of_gt positive),backgroundInitial_at_source]
  unfold actualResolvent
  rw [if_pos positive,rawHalf_true_inverse q reader lambda positive]

theorem backgroundOperator_pencil_generated (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ)
    (off : lambda.re≠0) :
    ∀ᶠh : Field289 in 𝓝 0,fieldPencil q lambda h (backgroundOperator q reader lambda h)=backgroundInitial q reader h :=by
  filter_upwards [fieldInverse_left_generated q lambda off] with h generated
  have applied:=congrArg (fun T : TransferOp=>T (backgroundInitial q reader h)) generated
  simpa only [backgroundOperator,mul_apply_eq_comp,one_apply_eq_self] using applied

private theorem inverse_source_algebra {R : Type*} [Ring R] (I D A B : R) :
    (I*D*I)*A+I*B=I*(B+D*(I*A)) :=by
  simp only [mul_add,mul_assoc]
  rw [add_comm]

theorem backgroundOperator_derivative (q : PhysicalResponsePoint) (reader force : Field289) (lambda : ℂ)
    (positive : 0<lambda.re) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>backgroundOperator q reader lambda (r • force)) (slopeHalf q reader force lambda) 0 :=by
  have original:=fieldInverse_ray_derivative q lambda (ne_of_gt positive) force
  have normal : @HasDerivAt ℝ _ TransferOp (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup
      (inferInstance : NormedSpace ℝ TransferOp).toModule
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : ContinuousSMul ℝ TransferOp) (fun r : ℝ=>fieldInverse q lambda (r • force))
      (fieldInverseDerivative q lambda force) 0:=by
    convert! original using 1
  have inverse:=(ContinuousLinearMap.hasFDerivAt (𝕜:=ℝ) (E:=TransferOp) (F:=Op→L[ℝ] Op) realOperatorMap).comp_hasDerivAt
    (𝕜:=ℝ) (E:=Op→L[ℝ] Op) (F:=TransferOp) (0:ℝ) normal
  have initial : @HasDerivAt ℝ _ Op (inferInstance : NormedAddCommGroup Op).toAddCommGroup
      (inferInstance : NormedSpace ℝ Op).toModule
      (inferInstance : PseudoMetricSpace Op).toUniformSpace.toTopologicalSpace
      (inferInstance : ContinuousSMul ℝ Op) (fun r : ℝ=>backgroundInitial q reader (r • force))
      (slopeInitial q reader force) 0:=by
    convert! backgroundInitial_derivative q reader force hz hw using 1
  have generated:=inverse.clm_apply initial
  simp only [zero_smul,backgroundInitial_at_source,fieldInverse_initial q lambda (ne_of_gt positive),
    fieldInverseDerivative_apply,Function.comp_apply,realOperatorMap_apply] at generated
  have derivative : (actualResolvent q lambda*driveOperator q force*actualResolvent q lambda) (rawInitial q reader)+
      actualResolvent q lambda (slopeInitial q reader force)=slopeHalf q reader force lambda:=by
    unfold actualResolvent
    rw [if_pos positive,slopeHalf_true_inverse q reader force lambda positive]
    simp only [mul_apply_eq_comp,driveOperator_apply,map_add,map_sub,map_neg]
    abel
  have mapped : HasDerivAt (fun r : ℝ=>backgroundOperator q reader lambda (r • force))
      ((actualResolvent q lambda*driveOperator q force*actualResolvent q lambda) (rawInitial q reader)+
        actualResolvent q lambda (slopeInitial q reader force)) 0:=by
    convert! generated using 1
  exact mapped.congr_deriv derivative

/-- Euler source remains the negative original external-leg read, once before the field Green. -/
def backgroundSource (q : PhysicalResponsePoint) (lambda : ℂ) (h : Field289) : Fin 289→ℂ:=
  fun i=>-sourceRead q (backgroundOperator q (fieldUnit i) lambda h)

theorem backgroundSource_C2 (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0)
    (hz : q.z.im≠0) (hw : q.w.im≠0) : ContDiffAt ℝ 2 (backgroundSource q lambda) 0 :=by
  apply contDiffAt_pi.mpr
  intro i
  exact ((sourceRead q).restrictScalars ℝ).contDiff.contDiffAt.comp 0
    (backgroundOperator_C2 q (fieldUnit i) lambda off hz hw) |>.neg

theorem backgroundSource_initial (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    backgroundSource q lambda 0=halfForcing q 0 false lambda :=by
  rw [←inverseSource_actual q 0 false lambda positive]
  ext i
  simp only [backgroundSource,inverseSource,inversePreparedOperator,↓reduceIte,backgroundOperator_initial q (fieldUnit i) lambda positive,Bool.false_eq_true]
  rw [rawHalf_true_inverse q (fieldUnit i) lambda positive]

theorem backgroundSource_derivative (q : PhysicalResponsePoint) (force : Field289) (lambda : ℂ)
    (positive : 0<lambda.re) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>backgroundSource q lambda (r • force)) (halfForcing q force true lambda) 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  have generated:=((sourceRead q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (backgroundOperator_derivative q (fieldUnit i) force lambda positive hz hw) |>.neg
  have read : -sourceRead q (slopeHalf q (fieldUnit i) force lambda)=halfForcing q force true lambda i:=by
    rw [←inverseSource_actual q force true lambda positive]
    simp only [inverseSource,inversePreparedOperator,↓reduceIte]
    rw [slopeHalf_true_inverse q (fieldUnit i) force lambda positive]
  exact generated.congr_deriv read

def backgroundField (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (h : Field289) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
    (backgroundSource q lambda.val h)

theorem backgroundField_equation (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (h : Field289) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥbackgroundField q lambda h=
      backgroundSource q lambda.val h-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)
            (backgroundSource q lambda.val h) :=by
  unfold backgroundField
  exact original_forced_field
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
    (backgroundSource q lambda.val h)

theorem backgroundField_derivative (q : PhysicalResponsePoint) (force : Field289)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>backgroundField q lambda (r • force)) (halfField q force true q.k lambda) 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  unfold backgroundField PreparationVacuumOriginalGreenFeedback.sourceField halfField
  simp only [Matrix.mulVec,dotProduct]
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hasDerivAt_pi.mp (backgroundSource_derivative q force lambda.val positive hz hw)) j).const_mul _

def backgroundCurvature (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) (h : Field289) : Fin 36→ℂ:=
  originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥbackgroundField q lambda h

theorem backgroundCurvature_derivative (q : PhysicalResponsePoint) (force : Field289)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>backgroundCurvature q lambda (r • force)) (curvatureReturn q force true lambda) 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  unfold backgroundCurvature curvatureReturn
  rw [pencilField_actual q force true lambda positive]
  simp only [Matrix.mulVec,dotProduct]
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hasDerivAt_pi.mp (backgroundField_derivative q force lambda positive hz hw)) j).const_mul _

end LowEnergy.SourcePropagationFieldFeedback
