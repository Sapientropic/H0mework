import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationInverse

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationResolvent
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumFieldConstraintResponse PreparationVacuumRealReaction
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ TransferOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ TransferOp:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourceRead sourceGreen sourceInverse evolutionGenerator propagationPencil
  originalJacobi originalReadback originalRowLift sourceCompatibility originalReader36

/-- The actual complete operator inverse returns both source branches with the same initial contacts. -/
def inversePreparedOperator (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (i : Fin 289) : Op:=
  if response then sourceInverse q lambda (slopeInitial q (fieldUnit i) force-
      leftCurrent q force*sourceInverse q lambda (rawInitial q (fieldUnit i))+
      sourceInverse q lambda (rawInitial q (fieldUnit i))*rightCurrent q force)
  else sourceInverse q lambda (rawInitial q (fieldUnit i))

theorem inversePreparedOperator_actual (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) :
    inversePreparedOperator q force response lambda i=operatorHalf q force response lambda i :=by
  cases response
  · simpa only [inversePreparedOperator,operatorHalf,Bool.false_eq_true,↓reduceIte]
      using (rawHalf_true_inverse q (fieldUnit i) lambda positive).symm
  · simpa only [inversePreparedOperator,operatorHalf,↓reduceIte]
      using (slopeHalf_true_inverse q (fieldUnit i) force lambda positive).symm

def inverseSource (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (lambda : ℂ) : Fin 289→ℂ:=
  fun i=>-sourceRead q (inversePreparedOperator q force response lambda i)

theorem inverseSource_actual (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) :
    inverseSource q force response lambda=halfForcing q force response lambda :=by
  rw [←pencilSource_actual q force response lambda positive]
  ext i
  rw [inverseSource,pencilSource,inversePreparedOperator_actual q force response lambda positive i]

def inverseField (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val,lambda.property⟩
      (inverseSource q force response lambda.val)

theorem inverseField_actual (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    inverseField q force response lambda=halfField q force response q.k lambda :=by
  unfold inverseField halfField
  rw [inverseSource_actual q force response lambda.val positive]

theorem inverseField_equation (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    originalJacobi (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥinverseField q force response lambda=
      inverseSource q force response lambda.val-originalRowLift
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)
            (inverseSource q force response lambda.val) :=by
  rw [inverseField_actual q force response lambda positive,inverseSource_actual q force response lambda.val positive]
  exact halfField_equation q force response q.k lambda

theorem inverseField_curvature (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : physicalSpectralDomain q.k) (positive : 0<lambda.val.re) :
    originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial q.k) lambda.val)*ᵥinverseField q force response lambda=
      curvatureReturn q force response lambda :=by
  rw [inverseField_actual q force response lambda positive]
  unfold curvatureReturn
  rw [pencilField_actual q force response lambda positive]

theorem inverseSource_realJacobian (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) (i j : Fin 289) :
    halfSourceMatrix q lambda i j=-sourceRead q (inversePreparedOperator q (fieldUnit j) true lambda i) :=by
  rw [inversePreparedOperator_actual q (fieldUnit j) true lambda positive i]
  exact actual_source_jacobian_pencil q lambda positive i j

/-- The source-produced inverse itself excludes every positive-real-part spectral point. -/
theorem actual_spectrum_excludes_positive (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0<lambda.re) :
    lambda ∉ spectrum ℂ (evolutionGenerator q) :=by
  apply spectrum.notMem_iff.mpr
  have h:=sourcePencil_isUnit q lambda positive
  unfold propagationPencil at h
  simpa only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.one_def] using h

theorem actual_spectrum_nonpositive (q : PhysicalResponsePoint) :
    spectrum ℂ (evolutionGenerator q)⊆{lambda | lambda.re≤0} :=by
  intro lambda member
  by_contra wrong
  exact actual_spectrum_excludes_positive q lambda (lt_of_not_ge wrong) member

end LowEnergy.SourcePropagationResolvent
