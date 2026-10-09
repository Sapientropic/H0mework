import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCurrentFeedbackAdjugate

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentConstrainedInverse
open SourcePropagationNativeActionHessian PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldConstraintResponse
open scoped BigOperators Topology Matrix
attribute [local irreducible] nativeHessian originalJacobi sourceGreen sourceCompatibility originalReader36
  sourceCurrentUpdateMatrix sourceCurrentMatrix sourceLaplaceCurrent sourceLaplaceInitial sourceCommonUpdateOperator

def sourceDressedGreen (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock) :
    Matrix (Fin 289) (Fin 289) ℂ:=
  sourceFeedbackResolvent q clock frequency.val*
    sourceGreen ⟨fullMomentum (physicalSpatial q.k) frequency.val.val.val,frequency.val.val.property⟩

def sourceDressedField (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (external : SignalAmplitude) : SignalAmplitude:=sourceDressedGreen q clock frequency*ᵥexternal

def sourceDressedSource (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (external : SignalAmplitude) : SignalAmplitude:=external+
  sourceLaplaceCurrent q clock frequency.val.val.val (sourceDressedField q clock frequency external)+
  sourceLaplaceInitial q clock frequency.val.val.val (sourceDressedField q clock frequency external)

theorem sourceDressedGreen_expression (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock) :
    sourceDressedGreen q clock frequency=
      (sourceFeedbackDenominator q clock frequency.val)⁻¹ •
        (sourceFeedbackAdjugate q clock frequency.val*
          sourceGreen ⟨fullMomentum (physicalSpatial q.k) frequency.val.val.val,frequency.val.val.property⟩) :=by
  rw [sourceDressedGreen,sourceFeedbackResolvent,Matrix.smul_mul]


private theorem matrix_row_price (A : Matrix (Fin 289) (Fin 289) ℂ) (d : ℂ) (external : SignalAmplitude)
    (row : Fin 289) :
    ‖((d • A)*ᵥexternal) row‖ ≤ (‖d‖*(∑column : Fin 289,‖A row column‖))*‖external‖ :=by
  rw [Matrix.smul_mulVec]
  simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Matrix.mulVec,dotProduct]
  have each (column : Fin 289) : ‖A row column*external column‖ ≤ ‖A row column‖*‖external‖:=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm external column) (norm_nonneg _))
  have sum:=Finset.sum_le_sum (fun column (_ : column∈Finset.univ)=>each column)
  rw [←Finset.sum_mul] at sum
  exact (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans sum) (norm_nonneg d)).trans_eq (mul_assoc _ _ _).symm

def sourceDressedFieldEntryPrice (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (row : Fin 289) : ℝ:=
  ‖sourceFeedbackDenominator q clock frequency.val‖⁻¹*
    ∑column : Fin 289,‖(sourceFeedbackAdjugate q clock frequency.val*
      sourceGreen ⟨fullMomentum (physicalSpatial q.k) frequency.val.val.val,frequency.val.val.property⟩) row column‖

theorem sourceDressedField_entryPrice (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (external : SignalAmplitude) (row : Fin 289) :
    ‖sourceDressedField q clock frequency external row‖ ≤ sourceDressedFieldEntryPrice q clock frequency row*‖external‖ :=by
  rw [sourceDressedField,sourceDressedGreen_expression]
  simpa only [sourceDressedFieldEntryPrice,norm_inv] using matrix_row_price
    (sourceFeedbackAdjugate q clock frequency.val*
      sourceGreen ⟨fullMomentum (physicalSpatial q.k) frequency.val.val.val,frequency.val.val.property⟩)
    (sourceFeedbackDenominator q clock frequency.val)⁻¹ external row

theorem sourceDressedField_generated (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (external : SignalAmplitude) :
    sourceDressedField q clock frequency external=
      sourceCommonFieldUpdate q clock frequency.val.val external (sourceDressedField q clock frequency external) :=by
  have paid:=sourceFeedbackResponse_generated q clock frequency
    (sourceGreen ⟨fullMomentum (physicalSpatial q.k) frequency.val.val.val,frequency.val.val.property⟩*ᵥexternal)
  rw [sourceCommonFieldUpdate_square]
  simpa only [sourceDressedField,sourceDressedGreen,←Matrix.mulVec_mulVec] using paid

theorem sourceDressedField_unique (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (external field : SignalAmplitude)
    (actualEquation : field=sourceCommonFieldUpdate q clock frequency.val.val external field) :
    field=sourceDressedField q clock frequency external :=by
  rw [sourceCommonFieldUpdate_square] at actualEquation
  have paid:=sourceFeedbackResponse_unique q clock frequency _ field actualEquation
  simpa only [sourceDressedField,sourceDressedGreen,←Matrix.mulVec_mulVec] using paid

theorem sourceDressedField_native (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (external : SignalAmplitude) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥ
      sourceDressedField q clock frequency external=
        sourceDressedSource q clock frequency external-
          originalRowLift (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial q.k) frequency.val.val.val)
              (sourceDressedSource q clock frequency external) :=by
  have paid:=sourceCommonFieldUpdate_native q clock frequency.val.val external
    (sourceDressedField q clock frequency external)
  rw [←sourceDressedField_generated] at paid
  exact paid

theorem sourceDressedField_commonEuler (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (external : SignalAmplitude) :
    sourceCommonEuler q clock frequency.val.val.val (sourceDressedField q clock frequency external)=
      external-originalRowLift (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥ
        sourceCompatibility (fullMomentum (physicalSpatial q.k) frequency.val.val.val)
          (sourceDressedSource q clock frequency external) :=by
  have native:=sourceDressedField_native q clock frequency external
  rw [nativeActionFourierHessian_original] at native
  have actual : sourceCommonEuler q clock frequency.val.val.val (sourceDressedField q clock frequency external)=
      originalJacobi (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥsourceDressedField q clock frequency external-
        sourceLaplaceCurrent q clock frequency.val.val.val (sourceDressedField q clock frequency external)-
        sourceLaplaceInitial q clock frequency.val.val.val (sourceDressedField q clock frequency external) :=by
    unfold sourceCommonEuler
    simp only [sub_apply]
    congr 2

  rw [actual,native,sourceDressedSource]
  abel

def sourceDressedCurvature (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock) :
    Matrix (Fin 36) (Fin 289) ℂ:=
  Matrix.of (originalReader36 (fullMomentum (physicalSpatial q.k) frequency.val.val.val))*sourceDressedGreen q clock frequency

theorem sourceDressedCurvature_actual (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (external : SignalAmplitude) :
    sourceDressedCurvature q clock frequency*ᵥexternal=
      originalReader36 (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥsourceDressedField q clock frequency external :=by
  rw [sourceDressedCurvature,←Matrix.mulVec_mulVec]
  rfl

theorem sourceDressedField_native36 (q : PhysicalResponsePoint) (clock : ℂ) (frequency : sourceCurrentRegularDomain q clock)
    (external : SignalAmplitude) :
    originalReader36 (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥ
        sourceDressedField q clock frequency external)=
      originalReader36 (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥsourceDressedSource q clock frequency external-
      originalReader36 (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥ
        (originalRowLift (fullMomentum (physicalSpatial q.k) frequency.val.val.val)*ᵥ
          sourceCompatibility (fullMomentum (physicalSpatial q.k) frequency.val.val.val)
            (sourceDressedSource q clock frequency external)) :=by
  rw [sourceDressedField_native,Matrix.mulVec_sub]

/-- The finite window approximates the actual current input on the common field carrier; its initial contribution is unchanged. -/
theorem sourceDressedCurrent_windowPrice (q : PhysicalResponsePoint) (clock : ℂ) (frequency : SourceCurrentFrequency q clock)
    (field : SignalAmplitude) (T : ℝ) (future : 0 ≤ T) :
    ‖sourceLaplaceCurrent q clock frequency.val.val field-
      sourceCausalWindow q (fullMomentum (physicalSpatial q.k) clock) frequency.val.val T
        ((frequency.val.val-clock) • field)‖ ≤
      (sourceCausalTailPrice q (fullMomentum (physicalSpatial q.k) clock) frequency.val.val T*
        ‖frequency.val.val-clock‖)*‖field‖ :=by
  have tail:=sourceCausalHalfOperator_tail q (fullMomentum (physicalSpatial q.k) clock)
    frequency.val.val frequency.property T future
  have applied:=(sourceCausalHalfOperator q (fullMomentum (physicalSpatial q.k) clock) frequency.val.val-
      sourceCausalWindow q (fullMomentum (physicalSpatial q.k) clock) frequency.val.val T).le_opNorm
        ((frequency.val.val-clock) • field)
  have bound:=applied.trans (mul_le_mul_of_nonneg_right tail (norm_nonneg _))
  simpa only [sourceLaplaceCurrent,ContinuousLinearMap.comp_apply,sourceLaplaceAmplitudeMap,
    smul_apply,ContinuousLinearMap.id_apply,sub_apply,norm_smul,mul_assoc] using bound

end LowEnergy.PreparationVacuumCurrentConstrainedInverse
