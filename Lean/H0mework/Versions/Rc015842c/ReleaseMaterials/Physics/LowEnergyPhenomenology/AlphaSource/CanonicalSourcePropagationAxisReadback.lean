import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationPastInverse

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationSpectralAxis
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil SourcePropagationResolvent
open PreparationVacuumPhysicalTailPrice PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
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
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection PreparationVacuumRealReaction
attribute [local irreducible] PreparationVacuumSourcePreparedState.sourcePreparation
  GaussComposite.SourceGraph.prepared PreparationVacuumSourcePreparedResponse.sourceProfile
  physicalTime jointGenerator propagationPencil evolutionGenerator
  sourceInverse sourceRead sourceGreen originalJacobi originalReadback originalRowLift sourceCompatibility

/-- Both source-produced inverse branches keep the same original physical propagation pencil. -/
def actualResolvent (q : PhysicalResponsePoint) (lambda : ℂ) : TransferOp:=
  if 0<lambda.re then sourceInverse q lambda else pastSourceInverse q lambda

theorem actualResolvent_left (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    propagationPencil q lambda*actualResolvent q lambda=1 :=by
  unfold actualResolvent
  split_ifs with positive
  · exact sourceInverse_left q lambda positive
  · exact pastSourceInverse_left q lambda (lt_of_le_of_ne (le_of_not_gt positive) off)

theorem actualResolvent_right (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    actualResolvent q lambda*propagationPencil q lambda=1 :=by
  unfold actualResolvent
  split_ifs with positive
  · exact sourceInverse_right q lambda positive
  · exact pastSourceInverse_right q lambda (lt_of_le_of_ne (le_of_not_gt positive) off)

theorem actualResolvent_isUnit (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    IsUnit (propagationPencil q lambda):=
  ⟨⟨propagationPencil q lambda,actualResolvent q lambda,actualResolvent_left q lambda off,
    actualResolvent_right q lambda off⟩,rfl⟩

private theorem inverse_from_two_sides {R : Type*} [Ring R] (P A : R)
    (left : P*A=1) (right : A*P=1) : A=Ring.inverse P :=by
  have unit : IsUnit P:=⟨⟨P,A,left,right⟩,rfl⟩
  exact (left_inv_eq_right_inv (Ring.inverse_mul_cancel P unit) left).symm

theorem actualResolvent_spectral (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    actualResolvent q lambda=resolvent (evolutionGenerator q) lambda :=by
  have same : (@algebraMap ℂ TransferOp inferInstance inferInstance (inferInstance : Algebra ℂ TransferOp) lambda)-evolutionGenerator q=propagationPencil q lambda:=by
    unfold propagationPencil
    simp only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.one_def]
  have inverse : actualResolvent q lambda=Ring.inverse (propagationPencil q lambda):=by
    convert! inverse_from_two_sides (R:=TransferOp) (propagationPencil q lambda) (actualResolvent q lambda)
      (actualResolvent_left q lambda off) (actualResolvent_right q lambda off) using 1
  have actual : Ring.inverse (propagationPencil q lambda)=resolvent (evolutionGenerator q) lambda:=by
    unfold resolvent
    exact congrArg Ring.inverse same.symm
  exact inverse.trans actual

theorem actual_spectrum_axis (q : PhysicalResponsePoint) :
    spectrum ℂ (evolutionGenerator q)⊆{lambda | lambda.re=0} :=by
  intro lambda member
  have nonpositive:=actual_spectrum_nonpositive q member
  by_contra off
  have negative : lambda.re<0:=lt_of_le_of_ne nonpositive off
  have inverse:=pastSourcePencil_isUnit q lambda negative
  unfold propagationPencil at inverse
  apply spectrum.notMem_iff.mpr ?_ member
  simpa only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.one_def] using inverse

/-- At zero spatial transfer the actual source left and right generators coincide. -/
theorem zero_transfer_source_kernel (q : PhysicalResponsePoint) (zeroTransfer : q.k=0) :
    evolutionGenerator q (1:Op)=0 :=by
  rw [evolutionGenerator_apply]
  have same : leftGenerator q=rightGenerator q:=by
    unfold leftGenerator rightGenerator
    rw [zeroTransfer,add_zero]
  rw [same,one_mul,mul_one,neg_add_cancel]

theorem zero_transfer_pencil_unit (q : PhysicalResponsePoint) (zeroTransfer : q.k=0) (lambda : ℂ) :
    propagationPencil q lambda (1:Op)=lambda • (1:Op) :=by
  unfold propagationPencil
  simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,zero_transfer_source_kernel q zeroTransfer,sub_zero]

/-- The exact source kernel produces its complete operator 1/lambda response. -/
theorem zero_transfer_resolvent_unit (q : PhysicalResponsePoint) (zeroTransfer : q.k=0)
    (lambda : ℂ) (off : lambda.re≠0) :
    actualResolvent q lambda (1:Op)=lambda⁻¹ • (1:Op) :=by
  have nonzero : lambda≠0:=fun h=>off (by rw [h];rfl)
  have inverse:=congrArg (fun T : TransferOp=>T (1:Op)) (actualResolvent_right q lambda off)
  have equation : actualResolvent q lambda (lambda • (1:Op))=(1:Op):=by
    simpa only [mul_apply_eq_comp,one_apply_eq_self,zero_transfer_pencil_unit q zeroTransfer] using inverse
  calc
    _=lambda⁻¹ • (lambda • actualResolvent q lambda (1:Op)):=by rw [smul_smul,inv_mul_cancel₀ nonzero,one_smul]
    _=lambda⁻¹ • (1:Op):=by rw [←map_smul,equation]

/-- The source pole read remains the original pair of independently prepared external legs. -/
theorem zero_transfer_prepared_pole_read (q : PhysicalResponsePoint) (zeroTransfer : q.k=0)
    (lambda : ℂ) (off : lambda.re≠0) :
    sourceRead q (actualResolvent q lambda (1:Op))=
      lambda⁻¹*inner ℂ (responseLeft q) (responseRight q) :=by
  rw [zero_transfer_resolvent_unit q zeroTransfer lambda off,map_smul]
  have original : sourceRead q (1:Op)=inner ℂ (responseLeft q) (responseRight q):=by
    unfold sourceRead
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,one_apply_eq_self,innerSL_apply_apply]
  rw [original]
  rfl

private theorem actual_hilbert_nontrivial (q : PhysicalResponsePoint) : Nontrivial H :=by
  let original:=PreparationVacuumSourcePreparedState.sourcePreparation q.epsilon q.precision
  let u : H:=GaussComposite.SourceGraph.prepared
    (CanonicalPreparationCore.Completed.zeroLocalizedProfile PreparationChartGuard.actualNativeLocalizer original.point.val)
  have norm : ‖u‖=1:=original.unit
  apply nontrivial_of_ne u 0
  intro zero
  have falseNorm : (0:ℝ)=1:=by simpa only [zero,norm_zero] using norm
  exact zero_ne_one falseNorm

theorem zero_transfer_actual_spectral_point (q : PhysicalResponsePoint) (zeroTransfer : q.k=0) :
    (0:ℂ)∈spectrum ℂ (evolutionGenerator q) :=by
  let := actual_hilbert_nontrivial q
  by_contra regular
  have unit:=spectrum.notMem_iff.mp regular
  have kernel : ((@algebraMap ℂ TransferOp inferInstance inferInstance (inferInstance : Algebra ℂ TransferOp) 0)-evolutionGenerator q) (1:Op)=0:=by
    have zeroMap : (@algebraMap ℂ TransferOp inferInstance inferInstance (inferInstance : Algebra ℂ TransferOp) 0)=(0:TransferOp):=map_zero _
    have point : ((0:TransferOp)-evolutionGenerator q) (1:Op)=0:=by
      simp only [sub_apply,zero_apply,zero_transfer_source_kernel q zeroTransfer,sub_self]
    convert! point using 1
    exact congrArg (fun T : TransferOp=>(T-evolutionGenerator q) (1:Op)) zeroMap
  have cancel:=congrArg (fun T : TransferOp=>T (1:Op)) unit.val_inv_mul
  have canceled : (1:Op)=(↑unit.unit⁻¹ : TransferOp) ((@algebraMap ℂ TransferOp inferInstance inferInstance (inferInstance : Algebra ℂ TransferOp) 0-evolutionGenerator q) (1:Op)):=by
    simpa only [mul_apply_eq_comp,one_apply_eq_self] using cancel.symm
  have readKernel : (↑unit.unit⁻¹ : TransferOp) ((@algebraMap ℂ TransferOp inferInstance inferInstance (inferInstance : Algebra ℂ TransferOp) 0-evolutionGenerator q) (1:Op))=(↑unit.unit⁻¹ : TransferOp) (0:Op):=congrArg (fun A : Op=>(↑unit.unit⁻¹ : TransferOp) A) kernel
  have impossible : (1:Op)=0:=canceled.trans (readKernel.trans (map_zero (↑unit.unit⁻¹ : TransferOp)))
  exact (one_ne_zero : (1:Op)≠0) impossible

/-- The complete original raw/five source and readback consume the generated inverse. -/
def axisPreparedOperator (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (i : Fin 289) : Op:=
  if response then actualResolvent q lambda (slopeInitial q (fieldUnit i) force-
      leftCurrent q force*actualResolvent q lambda (rawInitial q (fieldUnit i))+
      actualResolvent q lambda (rawInitial q (fieldUnit i))*rightCurrent q force)
  else actualResolvent q lambda (rawInitial q (fieldUnit i))

theorem axisPreparedOperator_future (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    axisPreparedOperator q force response lambda i=inversePreparedOperator q force response lambda i :=by
  simp only [axisPreparedOperator,inversePreparedOperator,actualResolvent,if_pos positive]

def axisSource (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (lambda : ℂ) : Fin 289→ℂ:=
  fun i=>-sourceRead q (axisPreparedOperator q force response lambda i)

def axisField (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
      (axisSource q force response lambda.val)

theorem axisSource_future (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) :
    axisSource q force response lambda=halfForcing q force response lambda :=by
  rw [←inverseSource_actual q force response lambda positive]
  ext i
  simp only [axisSource,inverseSource,axisPreparedOperator_future q force response lambda positive i]

theorem axisField_equation (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥaxisField q force response lambda=
      axisSource q force response lambda.val-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)
            (axisSource q force response lambda.val) :=by
  unfold axisField
  exact original_forced_field
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
    (axisSource q force response lambda.val)

theorem axisField_future (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    axisField q force response lambda=halfField q force response q.k lambda :=by
  unfold axisField halfField
  rw [axisSource_future q force response lambda.val positive]

theorem axisField_curvature_future (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥaxisField q force response lambda=
      curvatureReturn q force response lambda :=by
  rw [axisField_future q force response lambda positive]
  unfold curvatureReturn
  rw [pencilField_actual q force response lambda positive]

end LowEnergy.SourcePropagationSpectralAxis
