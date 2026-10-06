import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationPropagationHalfAxisPencil
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalRealReaction

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPropagationPencil
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback PreparationVacuumPhysicalHalfAxis PreparationVacuumActionFieldLift
open PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldConstraintResponse PreparationVacuumRealReaction PreparationVacuumPhysicalTailPrice
open Filter Set MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix
attribute [local irreducible] sourceRead sourceGreen originalJacobi originalChange originalReadback
  originalRowLift sourceCompatibility originalReader36 rawHalf slopeHalf responseLeft responseRight

/-- The original reader coordinate selects its raw or actual five-term operator return. -/
def operatorHalf (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (i : Fin 289) : Op:=
  if response then slopeHalf q (fieldUnit i) force lambda else rawHalf q (fieldUnit i) lambda

def operatorInitial (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (i : Fin 289) : Op:=
  if response then slopeInitial q (fieldUnit i) force else rawInitial q (fieldUnit i)

def operatorDriveHalf (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (i : Fin 289) : Op:=
  if response then -(leftCurrent q force*rawHalf q (fieldUnit i) lambda)+
    rawHalf q (fieldUnit i) lambda*rightCurrent q force else 0

theorem actual_operator_pencil (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    propagationPencil q lambda (operatorHalf q force response lambda i)=
      operatorInitial q force response i+operatorDriveHalf q force response lambda i :=by
  cases response
  · simpa only [operatorHalf,operatorInitial,operatorDriveHalf,Bool.false_eq_true,↓reduceIte,add_zero]
      using rawHalf_pencil q (fieldUnit i) lambda positive
  · simpa only [operatorHalf,operatorInitial,operatorDriveHalf,↓reduceIte,sub_eq_add_neg,neg_mul,add_assoc]
      using slopeHalf_pencil q (fieldUnit i) force lambda positive

/-- Euler forcing is the original negative source read, before the same field Green. -/
def pencilSource (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) : Fin 289→ℂ:=fun i=>-sourceRead q (operatorHalf q force response lambda i)

private theorem sourceRead_apply (q : PhysicalResponsePoint) (A : Op) :
    sourceRead q A=inner ℂ (responseLeft q) (A (responseRight q)) :=by
  unfold sourceRead
  rfl

private theorem read_integral (q : PhysicalResponsePoint) (f : ℝ→Op) (lambda : ℂ)
    (integrable : IntegrableOn (fun r=>laplaceWeight lambda r • f r) (Ioi (0:ℝ))) :
    (∫r in Ioi (0:ℝ),laplaceWeight lambda r*(-sourceRead q (f r)))=
      -sourceRead q (∫r in Ioi (0:ℝ),laplaceWeight lambda r • f r) :=by
  rw [←(sourceRead q).integral_comp_comm integrable,←integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  change laplaceWeight lambda r*(-sourceRead q (f r))=-sourceRead q (laplaceWeight lambda r • f r)
  rw [map_smul,smul_eq_mul,mul_neg]

theorem pencilSource_actual (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) :
    pencilSource q force response lambda=halfForcing q force response lambda :=by
  ext i
  cases response
  · have h:=read_integral q (rawFlow q (fieldUnit i)) lambda (rawFlow_integrable q (fieldUnit i) lambda positive)
    unfold pencilSource operatorHalf rawHalf halfForcing
    simpa only [Bool.false_eq_true,↓reduceIte,fullSourceJet,sourceJet,negativeJet,pairJet,rawKernelJet_value,
      sourceRead_apply,rawFlow] using h.symm
  · have h:=read_integral q (slopeFlow q (fieldUnit i) force) lambda (slopeFlow_integrable q (fieldUnit i) force lambda positive)
    unfold pencilSource operatorHalf slopeHalf halfForcing
    simpa only [↓reduceIte,fullSourceJet,sourceSlopeJet,negativeJet,pairJet,slopeKernelJet_value,
      sourceRead_apply,slopeFlow] using h.symm

/-- Field momentum is the same transfer carried by the actual two material legs. -/
def pencilField (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
    (pencilSource q force response lambda.val)

theorem pencilField_actual (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    pencilField q force response lambda=halfField q force response q.k lambda :=by
  unfold pencilField halfField
  rw [pencilSource_actual q force response lambda.val positive]

theorem pencilField_equation (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥpencilField q force response lambda=
      pencilSource q force response lambda.val-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)
            (pencilSource q force response lambda.val) :=by
  rw [pencilField_actual q force response lambda positive,pencilSource_actual q force response lambda.val positive]
  exact halfField_equation q force response q.k lambda

theorem pencilSource_initial_cosource (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    originalReadback (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥ
      pencilSource q force response lambda.val=
      (fun row=>halfTimeSource q force response (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val row+
        fullBoundary q force response (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val 0 row) :=by
  rw [pencilSource_actual q force response lambda.val positive]
  exact funext (halfForcing_readback q force response (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val positive)

/-- Every row of the original ordinary two-form reader is retained, including its frame terms. -/
def curvatureReturn (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) : Fin 36→ℂ:=
  originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥ
    pencilField q force response lambda

def curvatureReaction (q : PhysicalResponsePoint) (lambda : physicalSpectralDomain q.k) :
    Matrix (Fin 36) (Fin 289) ℂ:=
  fun row j=>∑a : Fin 289,originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val) row a*halfReactionMatrix q q.k lambda a j

theorem curvatureReaction_actual (q : PhysicalResponsePoint) (force : Field289)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    curvatureReturn q force true lambda=(fun row=>∑j : Fin 289,force j • curvatureReaction q lambda row j) :=by
  unfold curvatureReturn curvatureReaction
  rw [pencilField_actual q force true lambda positive,
    halfReactionMatrix_actual q force q.k lambda positive hz hw]
  ext row
  simp only [realAction,Matrix.mulVec,dotProduct,Matrix.mul_apply,Finset.mul_sum,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_smul_comm _ _ _

theorem actual_source_jacobian_pencil (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re)
    (i j : Fin 289) :
    halfSourceMatrix q lambda i j=-sourceRead q (slopeHalf q (fieldUnit i) (fieldUnit j) lambda) :=by
  have same:=congrArg (fun f : Fin 289→ℂ=>f i) (pencilSource_actual q (fieldUnit j) true lambda positive)
  simpa only [halfSourceMatrix,pencilSource,operatorHalf,↓reduceIte] using same.symm

theorem curvatureReturn_controlled (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) (T : ℝ) (nonnegative : 0≤T) (row : Fin 36) :
    ‖curvatureReturn q force response lambda row-
        (originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥ
          physicalField q force response q.k lambda T) row‖≤
      ∑i : Fin 289,‖originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val) row i‖*
        explicitFieldTail q force response q.k lambda T i :=by
  unfold curvatureReturn
  rw [pencilField_actual q force response lambda positive]
  simp only [Matrix.mulVec,dotProduct]
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (actualField_price q force response q.k lambda positive T nonnegative i) (norm_nonneg _)

end LowEnergy.PreparationVacuumPropagationPencil
