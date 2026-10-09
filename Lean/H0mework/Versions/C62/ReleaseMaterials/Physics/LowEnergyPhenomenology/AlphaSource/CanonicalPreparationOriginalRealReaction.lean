import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationRealSourceJacobian

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumRealReaction
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumActionFieldLift PreparationVacuumOriginalGreenFeedback
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace Interval
attribute [local irreducible] originalJacobi originalChange originalReadback originalRowLift
  sourceGreen sourceCompatibility extendedKernel

/-- Matrices act here only on the original real field coordinates. -/
def realAction (M : Matrix (Fin 289) (Fin 289) ℂ) (f : Field289) : Fin 289→ℂ:=
  fun i=>∑j : Fin 289,f j • M i j

theorem realAction_mul (M N : Matrix (Fin 289) (Fin 289) ℂ) (f : Field289) :
    M*ᵥrealAction N f=realAction (M*N) f :=by
  ext i
  simp only [realAction,Matrix.mulVec,dotProduct,Matrix.mul_apply,Finset.mul_sum,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact mul_smul_comm _ _ _

def windowReactionMatrix (q : PhysicalResponsePoint) (k : PhysicalMomentum)
    (lambda : physicalSpectralDomain k) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ:=
  sourceGreen ⟨fullMomentum (physicalSpatial k) lambda.val,lambda.property⟩*windowSourceMatrix q lambda.val T

def halfReactionMatrix (q : PhysicalResponsePoint) (k : PhysicalMomentum)
    (lambda : physicalSpectralDomain k) : Matrix (Fin 289) (Fin 289) ℂ:=
  sourceGreen ⟨fullMomentum (physicalSpatial k) lambda.val,lambda.property⟩*halfSourceMatrix q lambda.val

theorem windowReactionMatrix_actual (q : PhysicalResponsePoint) (force : Field289)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (T : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    physicalField q force true k lambda T=realAction (windowReactionMatrix q k lambda T) force :=by
  have forcing : fullForcing q force true lambda.val T=realAction (windowSourceMatrix q lambda.val T) force:=
    funext (fun i=>windowSourceMatrix_actual q force lambda.val T hz hw i)
  unfold physicalField PreparationVacuumOriginalGreenFeedback.sourceField windowReactionMatrix
  rw [forcing,realAction_mul]

theorem windowReactionMatrix_generated (q : PhysicalResponsePoint) (force : Field289)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (T : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (physicalFieldCurve q force k lambda T)
      (realAction (windowReactionMatrix q k lambda T) force) 0 :=by
  rw [←windowReactionMatrix_actual q force k lambda T hz hw]
  exact physicalField_generated q force k lambda hz hw T

theorem halfReactionMatrix_actual (q : PhysicalResponsePoint) (force : Field289)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    halfField q force true k lambda=realAction (halfReactionMatrix q k lambda) force :=by
  have forcing : halfForcing q force true lambda.val=realAction (halfSourceMatrix q lambda.val) force:=
    funext (fun i=>halfSourceMatrix_actual q force lambda.val positive hz hw i)
  unfold halfField PreparationVacuumOriginalGreenFeedback.sourceField halfReactionMatrix
  rw [forcing,realAction_mul]

theorem realAction_unit (M : Matrix (Fin 289) (Fin 289) ℂ) (j : Fin 289) :
    realAction M (fieldUnit j)=fun i=>M i j :=by
  ext i
  simp [realAction,fieldUnit,Pi.single_apply,ite_smul]

theorem halfReactionMatrix_column (q : PhysicalResponsePoint)
    (k : PhysicalMomentum) (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (j : Fin 289) :
    (fun i=>halfReactionMatrix q k lambda i j)=halfField q (fieldUnit j) true k lambda :=by
  rw [halfReactionMatrix_actual q (fieldUnit j) k lambda positive hz hw,realAction_unit]

theorem reactionMatrix_window_limit (q : PhysicalResponsePoint) (k : PhysicalMomentum)
    (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re) (i j : Fin 289) :
    Tendsto (fun T=>windowReactionMatrix q k lambda T i j) atTop (𝓝 (halfReactionMatrix q k lambda i j)) :=by
  simp only [windowReactionMatrix,halfReactionMatrix,Matrix.mul_apply]
  apply tendsto_finsetSum
  intro a _
  exact (sourceMatrix_window_limit q lambda.val positive a j).const_mul _

/-- The same response columns retain every original compatibility row. -/
def halfCompatibilityMatrix (q : PhysicalResponsePoint) (k : PhysicalMomentum)
    (lambda : physicalSpectralDomain k) : Matrix (Fin 289) (Fin 289) ℂ:=
  nullProjection*originalReadback (fullMomentum (physicalSpatial k) lambda.val)*halfSourceMatrix q lambda.val

theorem halfReactionMatrix_equation (q : PhysicalResponsePoint) (k : PhysicalMomentum)
    (lambda : physicalSpectralDomain k) :
    originalJacobi (fullMomentum (physicalSpatial k) lambda.val)*halfReactionMatrix q k lambda=
      halfSourceMatrix q lambda.val-originalRowLift (fullMomentum (physicalSpatial k) lambda.val)*
        halfCompatibilityMatrix q k lambda :=by
  unfold halfReactionMatrix halfCompatibilityMatrix
  have generated:=original_green_equation
    (⟨fullMomentum (physicalSpatial k) lambda.val,lambda.property⟩ : regularSource)
  rw [←mul_assoc,generated,sub_mul,one_mul]
  simp only [mul_assoc]

theorem halfReactionMatrix_readback (q : PhysicalResponsePoint) (k : PhysicalMomentum)
    (lambda : physicalSpectralDomain k) (positive : 0<lambda.val.re) (j : Fin 289) :
    originalReadback (fullMomentum (physicalSpatial k) lambda.val)*ᵥ(fun i=>halfSourceMatrix q lambda.val i j)=
      (fun i=>halfTimeSource q (fieldUnit j) true (physicalSpatial k) lambda.val i+
        fullBoundary q (fieldUnit j) true (physicalSpatial k) lambda.val 0 i) :=
  funext (halfForcing_readback q (fieldUnit j) true (physicalSpatial k) lambda.val positive)

end LowEnergy.PreparationVacuumRealReaction
