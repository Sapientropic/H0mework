import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceHalfAxisCurrentOperator
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCurrentFieldSquare
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCurrentSpectralReality

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentHalfOperator
open PreparationVacuumCurrentVisibleFeedback PreparationVacuumMatterEulerFeedback
open PreparationVacuumNoetherResponsePrice PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumOrderedRealSignal PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFieldConstraintResponse CanonicalGradedSpatialSource
open SourcePropagationNativeActionHessian
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Interval
attribute [local irreducible] sourceGreen sourceCompatibility originalJacobi originalRowLift originalReader36 nativeHessian

private def matrixOperator {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (Fin n→ℂ)→L[ℝ] (Fin m→ℂ):=
  ContinuousLinearMap.pi (fun i=>∑j : Fin n,A i j • (ContinuousLinearMap.proj j : (Fin n→ℂ)→L[ℝ] ℂ))

private theorem matrixOperator_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n→ℂ) :
    matrixOperator A v=A*ᵥv :=by
  funext i
  simp only [matrixOperator,ContinuousLinearMap.pi_apply,sum_apply,smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,Matrix.mulVec,dotProduct]

private def matrixPrice {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ:=
  ∑i : Fin m,∑j : Fin n,‖A i j‖

private theorem matrixPrice_nonnegative {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0≤ matrixPrice A :=
  Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))

private theorem matrixOperator_price {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ‖matrixOperator A‖≤ matrixPrice A :=by
  apply (matrixOperator A).opNorm_le_bound (matrixPrice_nonnegative A)
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (matrixPrice_nonnegative A) (norm_nonneg v))).mpr
  intro i
  rw [matrixOperator_apply]
  change ‖∑j : Fin n,A i j*v j‖≤_
  refine (norm_sum_le _ _).trans ?_
  have rowbound : (∑j : Fin n,‖A i j*v j‖)≤∑j : Fin n,‖A i j‖*‖v‖ :=by
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
  refine rowbound.trans ?_
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (Finset.mem_univ i)) (norm_nonneg v)

def sourceHalfFieldOperator (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) : Field289→L[ℝ] (Fin 289→ℂ):=
  (matrixOperator (sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩)).comp
    (sourceHalfCurrent q wave lambda.val)

def sourceHalfCurvatureOperator (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) : Field289→L[ℝ] (Fin 36→ℂ):=
  (matrixOperator (originalReader36 (fullMomentum (physicalSpatial wave) lambda.val))).comp
    (sourceHalfFieldOperator q wave lambda)

def sourceFieldOperatorFactor (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) : ℝ:=
  matrixPrice (sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩)

def sourceCurvatureOperatorFactor (wave : PhysicalMomentum) (lambda : physicalSpectralDomain wave) : ℝ:=
  matrixPrice (originalReader36 (fullMomentum (physicalSpatial wave) lambda.val))

theorem sourceHalfFieldOperator_generated (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (positive : 0<lambda.val.re) : sourceHalfFieldOperator q wave lambda force=modeHalfField q force true wave lambda :=by
  rw [sourceHalfFieldOperator,ContinuousLinearMap.comp_apply,matrixOperator_apply,
    sourceHalfCurrent_generated q wave lambda.val force hz hw positive]
  rfl

theorem sourceHalfCurvatureOperator_generated (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (positive : 0<lambda.val.re) :
    sourceHalfCurvatureOperator q wave lambda force=modeHalfCurvature q force true wave lambda :=by
  rw [sourceHalfCurvatureOperator,ContinuousLinearMap.comp_apply,matrixOperator_apply,
    sourceHalfFieldOperator_generated q wave lambda force hz hw positive]
  rfl

private theorem sourceFieldJacobian_originalOperator (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    sourceFieldJacobian q wave lambda T=
      (matrixOperator (sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩)).comp
        (sourceWindowJacobian q wave lambda.val T) :=by
  ext force i
  rw [sourceFieldJacobian_generated q wave lambda force hz hw T,ContinuousLinearMap.comp_apply,
    matrixOperator_apply,sourceWindowJacobian_generated q wave lambda.val force hz hw T]
  rfl

private theorem sourceCurvatureJacobian_originalOperator (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    sourceCurvatureJacobian q wave lambda T=
      (matrixOperator (originalReader36 (fullMomentum (physicalSpatial wave) lambda.val))).comp
        (sourceFieldJacobian q wave lambda T) :=by
  ext force i
  rw [sourceCurvatureJacobian_generated q wave lambda force hz hw T,ContinuousLinearMap.comp_apply,
    matrixOperator_apply,sourceFieldJacobian_generated q wave lambda force hz hw T]

theorem sourceHalfFieldOperator_tail (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.val.re)
    (T : ℝ) (future : 0≤ T) :
    ‖sourceHalfFieldOperator q wave lambda-sourceFieldJacobian q wave lambda T‖≤
      sourceFieldOperatorFactor wave lambda*sourceCurrentTailPrice q wave lambda.val T :=by
  rw [sourceHalfFieldOperator,sourceFieldJacobian_originalOperator q wave lambda hz hw T,←ContinuousLinearMap.comp_sub]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul (matrixOperator_price _)
    (sourceHalfCurrent_tail q wave lambda.val hz hw positive T future) (norm_nonneg _)
    (matrixPrice_nonnegative _)

theorem sourceHalfCurvatureOperator_tail (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.val.re)
    (T : ℝ) (future : 0≤ T) :
    ‖sourceHalfCurvatureOperator q wave lambda-sourceCurvatureJacobian q wave lambda T‖≤
      sourceCurvatureOperatorFactor wave lambda*
        (sourceFieldOperatorFactor wave lambda*sourceCurrentTailPrice q wave lambda.val T) :=by
  rw [sourceHalfCurvatureOperator,sourceCurvatureJacobian_originalOperator q wave lambda hz hw T,←ContinuousLinearMap.comp_sub]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul (matrixOperator_price _)
    (sourceHalfFieldOperator_tail q wave lambda hz hw positive T future) (norm_nonneg _)
    (matrixPrice_nonnegative _)

theorem sourceHalfFieldOperator_price (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.val.re) :
    ‖sourceHalfFieldOperator q wave lambda‖≤ sourceFieldOperatorFactor wave lambda*
      ((2/lambda.val.re)*sourceCurrentPrice q wave lambda.val) :=by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul (matrixOperator_price _)
    (sourceHalfCurrent_price q wave lambda.val hz hw positive) (norm_nonneg _) (matrixPrice_nonnegative _)

theorem sourceHalfCurvatureOperator_price (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.val.re) :
    ‖sourceHalfCurvatureOperator q wave lambda‖≤ sourceCurvatureOperatorFactor wave lambda*
      (sourceFieldOperatorFactor wave lambda*((2/lambda.val.re)*sourceCurrentPrice q wave lambda.val)) :=by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul (matrixOperator_price _)
    (sourceHalfFieldOperator_price q wave lambda hz hw positive) (norm_nonneg _) (matrixPrice_nonnegative _)

theorem sourceHalfFieldOperator_native (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (positive : 0<lambda.val.re) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
      sourceHalfFieldOperator q wave lambda force=
        sourceHalfCurrent q wave lambda.val force-
          originalRowLift (fullMomentum (physicalSpatial wave) lambda.val)*ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial wave) lambda.val)
              (sourceHalfCurrent q wave lambda.val force) :=by
  rw [sourceHalfFieldOperator_generated q wave lambda force hz hw positive,
    sourceHalfCurrent_generated q wave lambda.val force hz hw positive,nativeActionFourierHessian_original]
  exact modeHalfField_equation q force true wave lambda

theorem sourceFieldJacobian_operatorNorm (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.val.re) :
    Tendsto (fun T=>sourceFieldJacobian q wave lambda T) atTop (𝓝 (sourceHalfFieldOperator q wave lambda)) :=by
  have same : (fun T=>sourceFieldJacobian q wave lambda T)=fun T=>
      (matrixOperator (sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩)).comp
        (sourceWindowJacobian q wave lambda.val T) :=by
    funext T
    exact sourceFieldJacobian_originalOperator q wave lambda hz hw T
  rw [same]
  have composition:=(ContinuousLinearMap.compL ℝ Field289 (Fin 289→ℂ) (Fin 289→ℂ)
    (matrixOperator (sourceGreen ⟨fullMomentum (physicalSpatial wave) lambda.val,lambda.property⟩))).continuous.tendsto
      (sourceHalfCurrent q wave lambda.val)
  simpa only [Function.comp_def,ContinuousLinearMap.compL_apply,sourceHalfFieldOperator] using
    composition.comp (sourceWindowJacobian_operatorNorm q wave lambda.val hz hw positive)

theorem sourceCurvatureJacobian_operatorNorm (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.val.re) :
    Tendsto (fun T=>sourceCurvatureJacobian q wave lambda T) atTop (𝓝 (sourceHalfCurvatureOperator q wave lambda)) :=by
  have same : (fun T=>sourceCurvatureJacobian q wave lambda T)=fun T=>
      (matrixOperator (originalReader36 (fullMomentum (physicalSpatial wave) lambda.val))).comp
        (sourceFieldJacobian q wave lambda T) :=by
    funext T
    exact sourceCurvatureJacobian_originalOperator q wave lambda hz hw T
  rw [same]
  have composition:=(ContinuousLinearMap.compL ℝ Field289 (Fin 289→ℂ) (Fin 36→ℂ)
    (matrixOperator (originalReader36 (fullMomentum (physicalSpatial wave) lambda.val)))).continuous.tendsto
      (sourceHalfFieldOperator q wave lambda)
  simpa only [Function.comp_def,ContinuousLinearMap.compL_apply,sourceHalfCurvatureOperator] using
    composition.comp (sourceFieldJacobian_operatorNorm q wave lambda hz hw positive)

theorem sourceHalfCurrent_reality (q : PhysicalResponsePoint) (wave : PhysicalMomentum) (lambda : ℂ)
    (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (positive : 0<lambda.re) :
    sourceHalfCurrent q (-wave) (star lambda) force=fun i=>star (sourceHalfCurrent q wave lambda force i) :=by
  have matePositive : 0<(star lambda).re:=by simpa only [Complex.star_def,Complex.conj_re] using positive
  rw [sourceHalfCurrent_generated q (-wave) (star lambda) force hz hw matePositive,
    sourceHalfCurrent_generated q wave lambda force hz hw positive]
  funext i
  unfold modeHalfForcing
  have conjugate:=integral_conj (f:=fun t : ℝ=>laplaceWeight lambda t*(modeJet q force true wave t i).value)
    (μ:=volume.restrict (Ioi (0:ℝ)))
  simp only [starRingEnd_apply] at conjugate
  rw [←conjugate]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [sourceLaplaceWeight_reality,modeJet,realEulerTimeJet_value,ite_true,star_mul]
  have same:=congrFun (sourceModeJacobian_reality q wave force hz hw t) i
  rw [sourceModeJacobian_generated q (-wave) force hz hw t,
    sourceModeJacobian_generated q wave force hz hw t] at same
  rw [same]
  exact mul_comm _ _

theorem sourceHalfCurvatureOperator_mate (q : PhysicalResponsePoint) (wave : PhysicalMomentum)
    (lambda : physicalSpectralDomain wave) (force : Field289) :
    originalReader36 (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (-wave)) (star lambda.val))*ᵥ
      (fun i=>star (sourceHalfFieldOperator q wave lambda force i))=
        fun row=>star (sourceHalfCurvatureOperator q wave lambda force row) :=by
  rw [sourcePhysicalMomentum_reality,sourceOriginalReader36_reality]
  funext row
  rw [sourceHalfCurvatureOperator,ContinuousLinearMap.comp_apply,matrixOperator_apply]
  simp only [Matrix.mulVec,dotProduct,star_sum,star_mul,mul_comm]

end LowEnergy.PreparationVacuumCurrentHalfOperator
