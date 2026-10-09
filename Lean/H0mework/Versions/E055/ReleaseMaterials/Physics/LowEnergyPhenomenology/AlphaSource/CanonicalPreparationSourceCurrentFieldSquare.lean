import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCurrentModeJacobian
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationPreparedMotherEulerReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentVisibleFeedback
open PreparationVacuumMatterEulerFeedback PreparationVacuumNoetherResponsePrice
open PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumOrderedRealSignal
open SourcePropagationNativeActionHessian SourcePropagationMotherResidualDirections
open CanonicalGradedSpatialSource
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Interval
attribute [local irreducible] sourceGreen sourceCompatibility originalJacobi originalRowLift originalReader36 nativeHessian

/-- The original complex spectral field is a real output space; the input remains the physical real field. -/
def sourceRealEmbedding : Field289→L[ℝ] (Fin 289→ℂ):=
  ContinuousLinearMap.pi (fun i=>Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

theorem sourceRealEmbedding_apply (force : Field289) :
    sourceRealEmbedding force=(fun i=>Complex.ofReal (force i)) :=rfl

private def matrixRead {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (Fin n→ℂ)→L[ℝ] (Fin m→ℂ):=
  ContinuousLinearMap.pi (fun i=>∑j : Fin n,A i j • (ContinuousLinearMap.proj j : (Fin n→ℂ)→L[ℝ] ℂ))

private theorem matrixRead_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n→ℂ) :
    matrixRead A v=A*ᵥv :=by
  funext i
  simp only [matrixRead,ContinuousLinearMap.pi_apply,sum_apply,
    smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,Matrix.mulVec,dotProduct]

def sourceNativeFourierReal (p : Fin 4→ℂ) : Field289→L[ℝ] (Fin 289→ℂ):=
  (matrixRead (nativeFourierHessian nativeHessian p)).comp sourceRealEmbedding

theorem sourceNativeFourierReal_original (p : Fin 4→ℂ) (force : Field289) :
    sourceNativeFourierReal p force=originalJacobi p*ᵥ(fun i=>Complex.ofReal (force i)) :=by
  rw [sourceNativeFourierReal,ContinuousLinearMap.comp_apply,matrixRead_apply,
    nativeActionFourierHessian_original,sourceRealEmbedding_apply]

def sourceWindowField (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) (h : Field289) : Fin 289→ℂ:=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩
    (sourceModeWindow q wave lambda.val T h)

def sourceFieldJacobian (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) : Field289→L[ℝ] (Fin 289→ℂ):=
  (matrixRead (sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩)).comp
    (sourceWindowJacobian q wave lambda.val T)

theorem sourceWindowField_hasFDerivAt (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    HasFDerivAt (sourceWindowField q wave lambda T) (sourceFieldJacobian q wave lambda T) 0 :=by
  have actual:=(matrixRead (sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩)).hasFDerivAt.comp
    0 (sourceModeWindow_hasFDerivAt q wave lambda.val hz hw T)
  convert! actual using 1

theorem sourceFieldJacobian_generated (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    sourceFieldJacobian q wave lambda T force=modeField q force true wave lambda T :=by
  rw [sourceFieldJacobian,ContinuousLinearMap.comp_apply,matrixRead_apply,
    sourceWindowJacobian_generated q wave lambda.val force hz hw T]
  rfl

theorem sourceWindowField_native (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) (h : Field289) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
      sourceWindowField q wave lambda T h=
        sourceModeWindow q wave lambda.val T h-
          originalRowLift (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial wave) lambda.val)
              (sourceModeWindow q wave lambda.val T h) :=
  nativeAction_sourceField ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩ _

theorem sourceFieldJacobian_native (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
      sourceFieldJacobian q wave lambda T force=
        sourceWindowJacobian q wave lambda.val T force-
          originalRowLift (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial wave) lambda.val)
              (sourceWindowJacobian q wave lambda.val T force) :=by
  rw [sourceFieldJacobian_generated q wave lambda force hz hw T,
    sourceWindowJacobian_generated q wave lambda.val force hz hw T,nativeActionFourierHessian_original]
  exact modeField_equation q force true wave lambda T

def sourceWindowCurvature (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) (h : Field289) : Fin 36→ℂ:=
  originalReader36 (fullMomentum (physicalSpatial wave) lambda.val)*ᵥsourceWindowField q wave lambda T h

def sourceCurvatureJacobian (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) : Field289→L[ℝ] (Fin 36→ℂ):=
  (matrixRead (originalReader36 (fullMomentum (physicalSpatial wave) lambda.val))).comp
    (sourceFieldJacobian q wave lambda T)

theorem sourceWindowCurvature_hasFDerivAt (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    HasFDerivAt (sourceWindowCurvature q wave lambda T) (sourceCurvatureJacobian q wave lambda T) 0 :=by
  have actual:=(matrixRead (originalReader36 (fullMomentum (physicalSpatial wave) lambda.val))).hasFDerivAt.comp
    0 (sourceWindowField_hasFDerivAt q wave lambda hz hw T)
  convert! actual using 1

theorem sourceCurvatureJacobian_generated (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    sourceCurvatureJacobian q wave lambda T force=
      originalReader36 (fullMomentum (physicalSpatial wave) lambda.val)*ᵥmodeField q force true wave lambda T :=by
  rw [sourceCurvatureJacobian,ContinuousLinearMap.comp_apply,matrixRead_apply,
    sourceFieldJacobian_generated q wave lambda force hz hw T]

theorem sourceFieldJacobian_initial (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (row : Fin 9) :
    modeBoundary q force true wave (physicalSpatial wave) lambda.val 0 (compatibilitySlot row)=
      compatibilityCtime (physicalSpatial wave) (sourceModeJacobian q wave 0 force) row :=by
  rw [sourceModeJacobian_generated q wave force hz hw 0]
  simpa only [modeJet,realEulerTimeJet_value,ite_true] using
    modeBoundary_initial_compatibility q force true wave (physicalSpatial wave) lambda.val row

theorem sourceFieldJacobian_compatibility (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) (row : Fin 9) :
    sourceCompatibility (fullMomentum (physicalSpatial wave) lambda.val)
      (sourceWindowJacobian q wave lambda.val T force) (compatibilitySlot row)=
        (∫t in (0:ℝ)..T,laplaceWeight lambda.val t*
          (compatibilityC0 (physicalSpatial wave) (fun i=>(modeJet q force true wave t i).value) row+
            compatibilityCtime (physicalSpatial wave) (fun i=>(modeJet q force true wave t i).first) row))-
          (modeBoundary q force true wave (physicalSpatial wave) lambda.val T (compatibilitySlot row)-
            compatibilityCtime (physicalSpatial wave) (sourceModeJacobian q wave 0 force) row) :=by
  rw [sourceWindowJacobian_generated q wave lambda.val force hz hw T,
    sourceModeJacobian_generated q wave force hz hw 0]
  simpa only [modeJet,realEulerTimeJet_value,ite_true] using
    modeCompatibility_window q force true wave (physicalSpatial wave) lambda.val T row

/-- This family's ordinary part is the source Fourier-linear Euler; its preparation part is the actual nonlinear action current. -/
def sourceFourierWindowResidual (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) (h : Field289) : Fin 289→ℂ:=
  sourceNativeFourierReal (fullMomentum (physicalSpatial wave) lambda.val) h-sourceModeWindow q wave lambda.val T h

def sourceFourierWindowJacobian (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (T : ℝ) : Field289→L[ℝ] (Fin 289→ℂ):=
  sourceNativeFourierReal (fullMomentum (physicalSpatial wave) lambda.val)-sourceWindowJacobian q wave lambda.val T

theorem sourceFourierWindowResidual_hasFDerivAt (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    HasFDerivAt (sourceFourierWindowResidual q wave lambda T) (sourceFourierWindowJacobian q wave lambda T) 0 :=
  (sourceNativeFourierReal (fullMomentum (physicalSpatial wave) lambda.val)).hasFDerivAt.sub
    (sourceModeWindow_hasFDerivAt q wave lambda.val hz hw T)

theorem sourceFourierWindowJacobian_original (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    sourceFourierWindowJacobian q wave lambda T force=
      originalJacobi (fullMomentum (physicalSpatial wave) lambda.val)*ᵥsourceRealEmbedding force-
        modeForcing q force true wave lambda.val T :=by
  rw [sourceFourierWindowJacobian,sub_apply,
    sourceNativeFourierReal_original,sourceWindowJacobian_generated q wave lambda.val force hz hw T,
    sourceRealEmbedding_apply]

end LowEnergy.PreparationVacuumCurrentVisibleFeedback
