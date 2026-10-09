import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActionModeWindow

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMatterEulerFeedback
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumFieldConstraintResponse
open Filter Set MeasureTheory
open scoped Topology Interval BigOperators Matrix
attribute [local irreducible] sourceGreen sourceCompatibility originalJacobi originalRowLift
  originalReadback originalChange extendedKernel

/-- The actual nonlinear action Euler source is returned through the original full field Green. -/
def actionFieldCurve (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T r : ℝ) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩
    (actionModeWindowCurve q force wave lambda.val T r)

theorem actionFieldCurve_equation (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T r : ℝ) :
    originalJacobi (fullMomentum (physicalSpatial wave) lambda.val)*ᵥactionFieldCurve q force wave lambda T r=
      actionModeWindowCurve q force wave lambda.val T r-
        originalRowLift (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (physicalSpatial wave) lambda.val)
            (actionModeWindowCurve q force wave lambda.val T r) :=
  original_forced_field ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩
    (actionModeWindowCurve q force wave lambda.val T r)

theorem actionFieldCurve_initial (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) :
    actionFieldCurve q force wave lambda T 0=modeField q force false wave lambda T :=by
  rw [actionFieldCurve,actionModeWindowCurve_initial]
  rfl

theorem actionFieldCurve_generated (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    HasDerivAt (actionFieldCurve q force wave lambda T) (modeField q force true wave lambda T) 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  simp only [actionFieldCurve,modeField,PreparationVacuumOriginalGreenFeedback.sourceField,Matrix.mulVec,dotProduct]
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hasDerivAt_pi.mp (actionModeWindowCurve_generated q force wave lambda.val hz hw T)) j).const_mul _

theorem actionFieldResponse_equation (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    originalJacobi (fullMomentum (physicalSpatial wave) lambda.val)*ᵥderiv (actionFieldCurve q force wave lambda T) 0=
      modeForcing q force true wave lambda.val T-
        originalRowLift (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (physicalSpatial wave) lambda.val)
            (modeForcing q force true wave lambda.val T) :=by
  rw [(actionFieldCurve_generated q force wave lambda hz hw T).deriv]
  exact modeField_equation q force true wave lambda T

theorem actionFieldResponse_cosources (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    deriv (actionFieldCurve q force wave lambda T) 0=
      originalChange (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
        ((contactInverse (fullMomentum (physicalSpatial wave) lambda.val)+activeProjection*
          (extendedKernel (fullMomentum (physicalSpatial wave) lambda.val))⁻¹)*ᵥ
            (fun row=>(∫t in (0:ℝ)..T,laplaceWeight lambda.val t*
              modeTimeSource q force true wave (physicalSpatial wave) t row)-
                (modeBoundary q force true wave (physicalSpatial wave) lambda.val T row-
                  modeBoundary q force true wave (physicalSpatial wave) lambda.val 0 row))) :=by
  rw [(actionFieldCurve_generated q force wave lambda hz hw T).deriv]
  exact modeField_cosources q force true wave lambda T

theorem actionFieldResponse_compatibility (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) (row : Fin 9) :
    sourceCompatibility (fullMomentum (physicalSpatial wave) lambda.val)
      (modeForcing q force true wave lambda.val T) (compatibilitySlot row)=
        (∫t in (0:ℝ)..T,laplaceWeight lambda.val t*
          (compatibilityC0 (physicalSpatial wave) (fun i=>(modeJet q force true wave t i).value) row+
            compatibilityCtime (physicalSpatial wave) (fun i=>(modeJet q force true wave t i).first) row))-
          (modeBoundary q force true wave (physicalSpatial wave) lambda.val T (compatibilitySlot row)-
            compatibilityCtime (physicalSpatial wave) (fun i=>(modeJet q force true wave 0 i).value) row) :=
  modeCompatibility_window q force true wave (physicalSpatial wave) lambda.val T row

theorem actionFieldResponse_initial (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (row : Fin 9) :
    modeBoundary q force true wave (physicalSpatial wave) lambda.val 0 (compatibilitySlot row)=
      compatibilityCtime (physicalSpatial wave)
        (fun i=>deriv (fun r : ℝ=>actionRealEulerSource q 0 wave (r • force) i) 0) row :=by
  rw [modeBoundary_initial_compatibility]
  exact congrArg (fun current : Fin 289→ℂ=>compatibilityCtime (physicalSpatial wave) current row)
    (funext (fun i=>(actionRealEulerSource_responseTimePort q 0 wave force hz hw i).symm))

def actionFieldCurvatureCurve (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T r : ℝ) : Fin 36→ℂ:=
  originalReader36 (fullMomentum (physicalSpatial wave) lambda.val)*ᵥactionFieldCurve q force wave lambda T r

theorem actionFieldCurvature_generated (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    HasDerivAt (actionFieldCurvatureCurve q force wave lambda T)
      (originalReader36 (fullMomentum (physicalSpatial wave) lambda.val)*ᵥmodeField q force true wave lambda T) 0 :=by
  apply hasDerivAt_pi.mpr
  intro row
  simp only [actionFieldCurvatureCurve,Matrix.mulVec,dotProduct]
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hasDerivAt_pi.mp (actionFieldCurve_generated q force wave lambda hz hw T)) j).const_mul _

theorem actionFieldCurvature_cosources (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    deriv (actionFieldCurvatureCurve q force wave lambda T) 0=
      originalReader36 (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
        (originalChange (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
          ((contactInverse (fullMomentum (physicalSpatial wave) lambda.val)+activeProjection*
            (extendedKernel (fullMomentum (physicalSpatial wave) lambda.val))⁻¹)*ᵥ
              (fun row=>(∫t in (0:ℝ)..T,laplaceWeight lambda.val t*
                modeTimeSource q force true wave (physicalSpatial wave) t row)-
                  (modeBoundary q force true wave (physicalSpatial wave) lambda.val T row-
                    modeBoundary q force true wave (physicalSpatial wave) lambda.val 0 row)))) :=by
  rw [(actionFieldCurvature_generated q force wave lambda hz hw T).deriv]
  exact congrArg (fun field : Fin 289→ℂ=>originalReader36
    (fullMomentum (physicalSpatial wave) lambda.val)*ᵥfield) (modeField_cosources q force true wave lambda T)

end LowEnergy.PreparationVacuumMatterEulerFeedback
