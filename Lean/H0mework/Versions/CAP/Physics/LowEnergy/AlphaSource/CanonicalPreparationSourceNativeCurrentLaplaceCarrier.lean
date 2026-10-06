import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativeSignalLaplaceReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentNativeLaplaceBridge
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open SourcePropagationNoetherTime PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumOriginalGreenFeedback PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumFieldConstraintResponse
open Filter MeasureTheory Set
open scoped BigOperators Topology Matrix Interval
attribute [local irreducible] nativeHessian nativeJetBasis originalJacobi sourceCompatibility originalReader36
  sourceCurrentOperator sourceQuadratureCurrent

private def sourceMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : (Fin n→ℂ)→L[ℝ] (Fin m→ℂ):=
  ContinuousLinearMap.pi (fun i=>∑j : Fin n,A i j • (ContinuousLinearMap.proj j : (Fin n→ℂ)→L[ℝ] ℂ))

private theorem sourceMatrix_actual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n→ℂ) :
    sourceMatrix A v=A*ᵥv :=by
  ext i
  simp only [sourceMatrix,ContinuousLinearMap.pi_apply,sum_apply,smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,Matrix.mulVec,dotProduct]

def sourceLaplaceFieldMap (clock lambda : ℂ) : SignalAmplitude→L[ℝ] SignalAmplitude:=
  sourcePlaneHalfScalar clock lambda • ContinuousLinearMap.id ℝ SignalAmplitude

def sourceLaplaceAmplitudeMap (clock lambda : ℂ) : SignalAmplitude→L[ℝ] SignalAmplitude:=
  (lambda-clock) • ContinuousLinearMap.id ℝ SignalAmplitude

theorem sourceLaplaceFieldMap_actual (clock lambda : ℂ) (off : clock.re<lambda.re) (a : SignalAmplitude) :
    sourceLaplaceFieldMap clock lambda a=(lambda-clock)⁻¹ • a :=by
  rw [sourceLaplaceFieldMap,smul_apply,ContinuousLinearMap.id_apply,sourcePlaneHalfScalar_actual clock lambda off]

theorem sourceLaplaceAmplitudeMap_inverse (clock lambda : ℂ) (off : clock.re<lambda.re) :
    (sourceLaplaceAmplitudeMap clock lambda).comp (sourceLaplaceFieldMap clock lambda)=ContinuousLinearMap.id ℝ SignalAmplitude ∧
      (sourceLaplaceFieldMap clock lambda).comp (sourceLaplaceAmplitudeMap clock lambda)=ContinuousLinearMap.id ℝ SignalAmplitude :=by
  have different : lambda-clock≠0 :=by
    intro same
    have real:=congrArg Complex.re same
    simp only [Complex.sub_re,Complex.zero_re] at real
    linarith
  constructor <;> ext a i <;>
    simp only [ContinuousLinearMap.comp_apply,sourceLaplaceFieldMap,sourceLaplaceAmplitudeMap,
      smul_apply,ContinuousLinearMap.id_apply,sourcePlaneHalfScalar_actual clock lambda off,Pi.smul_apply,smul_eq_mul] <;>
    field_simp

def sourceLaplaceCurrent (q : PhysicalResponsePoint) (clock lambda : ℂ) : SignalAmplitude→L[ℝ] SignalAmplitude:=
  (sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) lambda).comp
    (sourceLaplaceAmplitudeMap clock lambda)

def sourceLaplaceInitial (q : PhysicalResponsePoint) (clock lambda : ℂ) : SignalAmplitude→L[ℝ] SignalAmplitude:=
  (sourceMatrix (sourceTemporalFirst (physicalSpatial q.k)+(clock+lambda) • sourceTemporalSecond)).comp
    (sourceLaplaceAmplitudeMap clock lambda)

/-- The current input is the actual integrated field, with its source-generated amplitude inverse and retained initial jet. -/
def sourceCommonEuler (q : PhysicalResponsePoint) (clock lambda : ℂ) : SignalAmplitude→L[ℝ] SignalAmplitude:=
  sourceMatrix (originalJacobi (fullMomentum (physicalSpatial q.k) lambda))-
    sourceLaplaceCurrent q clock lambda-sourceLaplaceInitial q clock lambda

theorem sourceLaplaceCurrent_history (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : clock.re<lambda.re) (a : SignalAmplitude) :
    sourceLaplaceCurrent q clock lambda (sourceLaplaceFieldMap clock lambda a)=
      sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) lambda a :=by
  have paid:=congrArg (fun A : SignalAmplitude→L[ℝ] SignalAmplitude=>A a)
    (sourceLaplaceAmplitudeMap_inverse clock lambda off).1
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at paid
  rw [sourceLaplaceCurrent,ContinuousLinearMap.comp_apply,paid]

theorem sourceLaplaceInitial_history (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : clock.re<lambda.re) (a : SignalAmplitude) :
    sourceLaplaceInitial q clock lambda (sourceLaplaceFieldMap clock lambda a)=
      sourceNativeBoundary (physicalSpatial q.k) clock lambda a 0 :=by
  have paid:=congrArg (fun A : SignalAmplitude→L[ℝ] SignalAmplitude=>A a)
    (sourceLaplaceAmplitudeMap_inverse clock lambda off).1
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at paid
  rw [sourceLaplaceInitial,ContinuousLinearMap.comp_apply,paid,sourceMatrix_actual,sourceNativeBoundary_initial]

theorem sourceCommonEuler_history (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : clock.re<lambda.re) (a : SignalAmplitude) :
    sourceCommonEuler q clock lambda (sourceLaplaceFieldMap clock lambda a)=
      originalJacobi (fullMomentum (physicalSpatial q.k) clock)*ᵥsourceLaplaceFieldMap clock lambda a-
        sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) lambda a :=by
  have different : lambda-clock≠0 :=by
    intro same
    have real:=congrArg Complex.re same
    simp only [Complex.sub_re,Complex.zero_re] at real
    linarith
  have matrix:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A*ᵥa)
    (sourceTemporalPencil_difference (physicalSpatial q.k) lambda clock)
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec] at matrix
  rw [sourceCommonEuler,sub_apply,sub_apply,sourceMatrix_actual,
    sourceLaplaceCurrent_history q clock lambda off,sourceLaplaceInitial_history q clock lambda off,
    sourceNativeBoundary_initial,sourceLaplaceFieldMap_actual clock lambda off a,
    Matrix.mulVec_smul,Matrix.mulVec_smul]
  ext i
  have row:=congrFun matrix i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,add_comm clock lambda] at row ⊢
  have coefficient : (lambda-clock)⁻¹*(lambda-clock)=1:=inv_mul_cancel₀ different
  linear_combination (lambda-clock)⁻¹ * row +
    ((sourceTemporalFirst (physicalSpatial q.k)+(lambda+clock) • sourceTemporalSecond)*ᵥa) i * coefficient

theorem sourceLaplaceAmplitudeMap_price (clock lambda : ℂ) :
    ‖sourceLaplaceAmplitudeMap clock lambda‖ ≤ ‖lambda-clock‖ :=by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  simp only [sourceLaplaceAmplitudeMap,smul_apply,ContinuousLinearMap.id_apply,norm_smul]
  exact le_rfl

def sourceLaplaceCurrentPrice (q : PhysicalResponsePoint) (clock lambda : ℂ) : ℝ:=
  ((2/sourceReadGap (fullMomentum (physicalSpatial q.k) clock) lambda)*
    sourceCausalCoefficient q (fullMomentum (physicalSpatial q.k) clock) lambda)*‖lambda-clock‖

theorem sourceLaplaceCurrent_price (q : PhysicalResponsePoint) (clock lambda : ℂ)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.re) :
    ‖sourceLaplaceCurrent q clock lambda‖ ≤ sourceLaplaceCurrentPrice q clock lambda :=by
  have paid:=sourceCausalHalfOperator_tail q (fullMomentum (physicalSpatial q.k) clock) lambda off 0 (le_refl 0)
  have empty : sourceCausalWindow q (fullMomentum (physicalSpatial q.k) clock) lambda 0=0 :=by
    simp only [sourceCausalWindow,intervalIntegral.integral_same]
  rw [empty,sub_zero] at paid
  simp only [sourceCausalTailPrice,mul_zero,Real.exp_zero,mul_one] at paid
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul paid (sourceLaplaceAmplitudeMap_price clock lambda) (norm_nonneg _) ((norm_nonneg _).trans paid)).trans_eq rfl)


def sourceCommonUpdateOperator (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k) :
    SignalAmplitude→L[ℝ] SignalAmplitude:=
  (sourceMatrix (sourceGreen ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩)).comp
    (sourceLaplaceCurrent q clock lambda.val+sourceLaplaceInitial q clock lambda.val)

theorem sourceCommonUpdateOperator_actual (q : PhysicalResponsePoint) (clock : ℂ)
    (lambda : physicalSpectralDomain q.k) (field : SignalAmplitude) :
    sourceCommonUpdateOperator q clock lambda field=
      sourceGreen ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩*ᵥ
        (sourceLaplaceCurrent q clock lambda.val field+sourceLaplaceInitial q clock lambda.val field) :=by
  rw [sourceCommonUpdateOperator,ContinuousLinearMap.comp_apply,sourceMatrix_actual,add_apply]

def sourceCommonUpdatePrice (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k) : ℝ:=
  ‖sourceMatrix (sourceGreen ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩)‖*
    (sourceLaplaceCurrentPrice q clock lambda.val+‖sourceLaplaceInitial q clock lambda.val‖)

theorem sourceCommonUpdateOperator_price (q : PhysicalResponsePoint) (clock : ℂ)
    (lambda : physicalSpectralDomain q.k)
    (off : sourceClockGrowth (fullMomentum (physicalSpatial q.k) clock)<lambda.val.re) :
    ‖sourceCommonUpdateOperator q clock lambda‖ ≤ sourceCommonUpdatePrice q clock lambda :=by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (add_le_add (sourceLaplaceCurrent_price q clock lambda.val off) (le_refl ‖sourceLaplaceInitial q clock lambda.val‖))) (norm_nonneg _))

def sourceCommonFieldUpdate (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k)
    (external : SignalAmplitude) (field : SignalAmplitude) : SignalAmplitude:=
  sourceGreen ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩*ᵥ
    (external+sourceLaplaceCurrent q clock lambda.val field+sourceLaplaceInitial q clock lambda.val field)


theorem sourceCommonFieldUpdate_square (q : PhysicalResponsePoint) (clock : ℂ)
    (lambda : physicalSpectralDomain q.k) (external field : SignalAmplitude) :
    sourceCommonFieldUpdate q clock lambda external field=
      sourceGreen ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩*ᵥexternal+
        sourceCommonUpdateOperator q clock lambda field :=by
  rw [sourceCommonFieldUpdate,sourceCommonUpdateOperator_actual,←Matrix.mulVec_add]
  congr 1
  abel

theorem sourceCommonFieldUpdate_native (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k)
    (external field : SignalAmplitude) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
      sourceCommonFieldUpdate q clock lambda external field=
        external+sourceLaplaceCurrent q clock lambda.val field+sourceLaplaceInitial q clock lambda.val field-
          originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
              (external+sourceLaplaceCurrent q clock lambda.val field+sourceLaplaceInitial q clock lambda.val field) :=by
  exact nativeAction_sourceField ⟨_,lambda.property⟩ _

theorem sourceCommonFieldUpdate_native36 (q : PhysicalResponsePoint) (clock : ℂ) (lambda : physicalSpectralDomain q.k)
    (external field : SignalAmplitude) :
    originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
        sourceCommonFieldUpdate q clock lambda external field)=
      originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
        (external+sourceLaplaceCurrent q clock lambda.val field+sourceLaplaceInitial q clock lambda.val field)-
      originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
        (originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
            (external+sourceLaplaceCurrent q clock lambda.val field+sourceLaplaceInitial q clock lambda.val field)) :=by
  rw [sourceCommonFieldUpdate_native,Matrix.mulVec_sub]

end LowEnergy.PreparationVacuumCurrentNativeLaplaceBridge
