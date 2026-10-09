import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedTimeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherSylvester
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherAction

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNonlinearHalf
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumNoetherChart
open PreparationVacuumPhysicalHalfAxis PreparationVacuumPropagationPencil
open SourcePropagationResolvent SourcePropagationSpectralAxis SourcePropagationFieldFeedback
open SourcePropagationNearFieldTime ActualDressedSylvester
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
local instance : NormedAlgebra ℝ ResponseOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ ResponseOp := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ SourcePropagationResolvent.TransferOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ SourcePropagationResolvent.TransferOp := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedSpace ℝ SourcePropagationResolvent.TransferOp := ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ SourcePropagationResolvent.TransferOp := by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=SourcePropagationResolvent.TransferOp)) using 1
local instance : ContinuousSMul ℝ SourcePropagationResolvent.TransferOp := by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=SourcePropagationResolvent.TransferOp)) using 1
local instance : ContinuousENorm SourcePropagationResolvent.TransferOp := by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=SourcePropagationResolvent.TransferOp)) using 1
attribute [local irreducible] fieldInverse fieldPencil jointResolvent jointCurrent
  noetherReader noetherReaderContact rawReader rawReaderContact rawInitial slopeInitial
  noetherStaticInitial noetherStaticContact noetherStaticHalf sourceInverse actualResolvent

/-- Both material resolvents surround the original fixed-canonical-momentum Noether reader. -/
def noetherBackgroundInitial (q : PhysicalResponsePoint) (reader h : Field289) : ResponseOp :=
  jointResolvent (q.p+q.k) q.F q.z h*noetherReader reader q.p q.F h*jointResolvent q.p q.F q.w h

theorem noether_background_initial_source (q : PhysicalResponsePoint) (reader : Field289) :
    noetherBackgroundInitial q reader 0=rawInitial q reader := by
  simp only [noetherBackgroundInitial,noetherReader_source,rawInitial]

theorem noether_background_initial_C2 (q : PhysicalResponsePoint) (reader : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    ContDiffAt ℝ 2 (noetherBackgroundInitial q reader) 0 := by
  exact ((jointResolvent_C2 (q.p+q.k) q.F q.z hz).mul (noetherReader_C2 reader q.p q.F)).mul
    (jointResolvent_C2 q.p q.F q.w hw)

private theorem corrected_initial_product {A : Type*} [Ring A] (L R J CL CR raw next : A) :
    (-(L*CL*L))*J*R+L*next*R+L*J*(-(R*CR*R))=
      ((-(L*CL*L))*J*R+L*raw*R+L*J*(-(R*CR*R)))+L*(next-raw)*R := by
  simp only [mul_sub,sub_mul]
  abel

theorem noether_background_initial_derivative (q : PhysicalResponsePoint) (reader force : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>noetherBackgroundInitial q reader (r • force))
      (noetherStaticInitial q reader force) 0 := by
  have generated:=((inverse_direction (q.p+q.k) q.F q.z hz force).mul
    (noetherReader_generated reader force q.p q.F)).mul (inverse_direction q.p q.F q.w hw force)
  have mapped : HasDerivAt (fun r : ℝ=>noetherBackgroundInitial q reader (r • force))
      ((-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 force*
          jointResolvent (q.p+q.k) q.F q.z 0))*rawReader reader q.p q.F 0*jointResolvent q.p q.F q.w 0+
        jointResolvent (q.p+q.k) q.F q.z 0*noetherReaderContact reader force q.p q.F*jointResolvent q.p q.F q.w 0+
        jointResolvent (q.p+q.k) q.F q.z 0*rawReader reader q.p q.F 0*
          (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0))) 0 := by
    simpa only [noetherBackgroundInitial,Pi.mul_apply,zero_smul,noetherReader_source] using! generated
  apply mapped.congr_deriv
  unfold noetherStaticInitial noetherStaticContact slopeInitial
  exact corrected_initial_product _ _ _ _ _ _ _

/-- The original generated inverse is consumed at the same nonlinear source field. -/
def noetherBackgroundOperator (q : PhysicalResponsePoint) (reader : Field289) (lambda : ℂ)
    (h : Field289) : ResponseOp :=
  fieldInverse q lambda h (noetherBackgroundInitial q reader h)

attribute [local irreducible] noetherBackgroundInitial noetherBackgroundOperator

theorem noether_background_operator_C2 (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (off : lambda.re≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    ContDiffAt ℝ 2 (noetherBackgroundOperator q reader lambda) 0 := by
  have inverse:=(ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=SourcePropagationResolvent.TransferOp) (F:=ResponseOp→L[ℝ]ResponseOp)
    realOperatorMap).contDiffAt.comp 0 (fieldInverse_C2 q lambda off)
  have generated:=inverse.clm_apply (noether_background_initial_C2 q reader hz hw)
  convert! generated using 1
  funext h
  simp only [noetherBackgroundOperator,Function.comp_apply,realOperatorMap_apply]

theorem noether_background_operator_source (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) :
    noetherBackgroundOperator q reader lambda 0=rawHalf q reader lambda := by
  unfold noetherBackgroundOperator
  rw [fieldInverse_initial q lambda (ne_of_gt positive),noether_background_initial_source]
  unfold actualResolvent
  rw [if_pos positive,rawHalf_true_inverse q reader lambda positive]

theorem noether_background_operator_pencil (q : PhysicalResponsePoint) (reader : Field289)
    (lambda : ℂ) (off : lambda.re≠0) :
    ∀ᶠh : Field289 in 𝓝 0,
      fieldPencil q lambda h (noetherBackgroundOperator q reader lambda h)=noetherBackgroundInitial q reader h := by
  filter_upwards [fieldInverse_left_generated q lambda off] with h generated
  have applied:=congrArg (fun T : SourcePropagationResolvent.TransferOp=>T (noetherBackgroundInitial q reader h)) generated
  simpa only [noetherBackgroundOperator,mul_apply_eq_comp,one_apply_eq_self] using! applied

private theorem inverse_apply_initial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I D : E→L[ℂ]E) (A B : E) :
    (I*D*I) A+I B=I (B+D (I A)) := by
  change I (D (I A))+I B=I (B+D (I A))
  rw [map_add,add_comm]

private theorem initial_drive_add {A : Type*} [AddCommGroup A] (B L R : A) :
    B+(-L+R)=B-L+R := by abel

theorem noether_background_operator_derivative (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0<lambda.re) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>noetherBackgroundOperator q reader lambda (r • force))
      (noetherStaticHalf q reader force lambda) 0 := by
  have original:=fieldInverse_ray_derivative q lambda (ne_of_gt positive) force
  have normal : @HasDerivAt ℝ _ SourcePropagationResolvent.TransferOp (inferInstance : NormedAddCommGroup SourcePropagationResolvent.TransferOp).toAddCommGroup
      (inferInstance : NormedSpace ℝ SourcePropagationResolvent.TransferOp).toModule
      (inferInstance : PseudoMetricSpace SourcePropagationResolvent.TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : ContinuousSMul ℝ SourcePropagationResolvent.TransferOp) (fun r : ℝ=>fieldInverse q lambda (r • force))
      (fieldInverseDerivative q lambda force) 0 := by
    convert! original using 1
  have inverse:=(ContinuousLinearMap.hasFDerivAt (𝕜:=ℝ) (E:=SourcePropagationResolvent.TransferOp) (F:=ResponseOp→L[ℝ]ResponseOp)
    realOperatorMap).comp_hasDerivAt (𝕜:=ℝ) (E:=ResponseOp→L[ℝ]ResponseOp) (F:=SourcePropagationResolvent.TransferOp) (0:ℝ) normal
  have initial : @HasDerivAt ℝ _ ResponseOp (inferInstance : NormedAddCommGroup ResponseOp).toAddCommGroup
      (inferInstance : NormedSpace ℝ ResponseOp).toModule
      (inferInstance : PseudoMetricSpace ResponseOp).toUniformSpace.toTopologicalSpace
      (inferInstance : ContinuousSMul ℝ ResponseOp) (fun r : ℝ=>noetherBackgroundInitial q reader (r • force))
      (noetherStaticInitial q reader force) 0 := by
    convert! noether_background_initial_derivative q reader force hz hw using 1
  have generated:=inverse.clm_apply initial
  simp only [zero_smul,noether_background_initial_source,fieldInverse_initial q lambda (ne_of_gt positive),
    fieldInverseDerivative_apply,Function.comp_apply,realOperatorMap_apply] at generated
  have derivative : (actualResolvent q lambda*driveOperator q force*actualResolvent q lambda) (rawInitial q reader)+
      actualResolvent q lambda (noetherStaticInitial q reader force)=noetherStaticHalf q reader force lambda := by
    simp only [actualResolvent,if_pos positive]
    calc
      _=sourceInverse q lambda (noetherStaticInitial q reader force+
          driveOperator q force (sourceInverse q lambda (rawInitial q reader))) :=
        inverse_apply_initial _ _ _ _
      _=sourceInverse q lambda (noetherStaticInitial q reader force-
          leftCurrent q force*sourceInverse q lambda (rawInitial q reader)+
            sourceInverse q lambda (rawInitial q reader)*rightCurrent q force) := by
        apply congrArg (sourceInverse q lambda)
        rw [driveOperator_apply]
        exact initial_drive_add _ _ _
      _=_ := (noether_static_half_inverse q reader force lambda positive).symm
  have mapped : HasDerivAt (fun r : ℝ=>noetherBackgroundOperator q reader lambda (r • force))
      ((actualResolvent q lambda*driveOperator q force*actualResolvent q lambda) (rawInitial q reader)+
        actualResolvent q lambda (noetherStaticInitial q reader force)) 0 := by
    convert! generated using 1
    simp only [noetherBackgroundOperator]
  exact mapped.congr_deriv derivative

end LowEnergy.GaussComposite.ActualDressedNonlinearHalf
