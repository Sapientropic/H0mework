import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedAnchorInverse

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedConstraint
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationPhysicalVoltageCompleteReturn
open PreparationVacuumCurrentSignalOperator SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse
open scoped BigOperators Matrix
attribute [local irreducible] sourceGreen originalJacobi originalChange originalInverse originalReadback
  originalRowLift dressedWindowPolarization anchorFeedbackResolvent anchorEvent anchorInput

/-- The original nine null coordinates remain independent initial data. -/
def sourceNull (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  originalChange p*nullProjection*originalInverse p

private theorem null_square : nullProjection*nullProjection=nullProjection := by
  unfold nullProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

private theorem null_active : nullProjection*activeProjection=0 := by
  unfold nullProjection activeProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases same : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.zero_apply]
    unfold nullFlag activeFlag
    simp only [decide_eq_true_eq]
    split_ifs <;> norm_num; omega
  · simp [same]

private theorem null_contact (p : Fin 4→ℂ) : nullProjection*contactInverse p=0 := by
  have certificate : fastNormalizeTerms
      (productTerms (projectionTerms nullFlag) contactInverseTerms++negativeTerms [])=[]:=by decide +kernel
  have generated:=normalization_equal (productTerms (projectionTerms nullFlag) contactInverseTerms) [] certificate p
  simpa only [productTerms_value,projectionTerms_value,sourceMatrix_nil,nullProjection,contactInverse] using generated

private theorem null_read_kernel (p : Fin 4→ℂ) : nullProjection*originalReadback p*originalJacobi p=0 := by
  have generated:=congrArg Matrix.transpose (original_null_intertwiner (-p))
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_zero,original_jacobi_reciprocity] at generated
  have symmetric : nullProjection.transpose=nullProjection:=Matrix.diagonal_transpose _
  rw [symmetric] at generated
  simpa only [originalReadback,mul_assoc] using generated

theorem source_null_projection (p : Fin 4→ℂ) : sourceNull p*sourceNull p=sourceNull p := by
  calc
    _=originalChange p*nullProjection*(originalInverse p*originalChange p)*nullProjection*originalInverse p := by
      unfold sourceNull; noncomm_ring
    _=originalChange p*(nullProjection*nullProjection)*originalInverse p := by
      rw [original_inverse_change,mul_one]; noncomm_ring
    _=sourceNull p := by rw [null_square]; rfl

theorem source_null_euler (p : Fin 4→ℂ) : originalJacobi p*sourceNull p=0 := by
  rw [sourceNull,←mul_assoc,←mul_assoc,original_null_intertwiner,zero_mul]

theorem source_null_green (p : regularSource) : sourceNull p.val*sourceGreen p=0 := by
  calc
    _=originalChange p.val*nullProjection*(originalInverse p.val*originalChange p.val)*
        (contactInverse p.val+activeProjection*(extendedKernel p.val)⁻¹)*originalReadback p.val := by
      rw [sourceNull,sourceGreen]; noncomm_ring
    _=originalChange p.val*(nullProjection*contactInverse p.val+
        (nullProjection*activeProjection)*(extendedKernel p.val)⁻¹)*originalReadback p.val := by
      rw [original_inverse_change,mul_one]; noncomm_ring
    _=0 := by rw [null_contact,null_active,zero_mul,add_zero,mul_zero,zero_mul]

theorem source_compatibility_euler (p : Fin 4→ℂ) (a : SignalAmplitude) :
    sourceCompatibility p (originalJacobi p*ᵥa)=0 := by
  rw [sourceCompatibility,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,null_read_kernel,Matrix.zero_mulVec]

/-- Genuine inverse of the regular quantum feedback, with the original null data retained. -/
def anchorResponse (event : DressedEvent) (T : ℝ) (forcing initial : SignalAmplitude) : SignalAmplitude :=
  anchorFeedbackResolvent event T*ᵥ((T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥforcing)+
    sourceNull anchorInput*ᵥinitial)

attribute [local irreducible] anchorResponse

private theorem anchor_point : generatedRegularPoint.val=anchorInput := by
  unfold anchorInput
  rfl

theorem anchor_response_generated (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (forcing initial : SignalAmplitude) :
    anchorResponse event T forcing initial=sourceNull anchorInput*ᵥinitial+(T:ℂ)⁻¹ •
      (sourceGreen generatedRegularPoint*ᵥ(forcing+
        dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥanchorResponse event T forcing initial)) := by
  have generated:=anchor_feedback_response event T positive small
    ((T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥforcing)+sourceNull anchorInput*ᵥinitial)
  rw [←anchorResponse] at generated
  calc
    _=_ := generated
    _=_ := by
      change (T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥforcing)+sourceNull anchorInput*ᵥinitial+
        (T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥ
          (dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥanchorResponse event T forcing initial))=_
      rw [Matrix.mulVec_add,smul_add]
      abel

theorem anchor_response_initial (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (forcing initial : SignalAmplitude) :
    sourceNull anchorInput*ᵥanchorResponse event T forcing initial=sourceNull anchorInput*ᵥinitial := by
  have ng:=source_null_green generatedRegularPoint
  rw [anchor_point] at ng
  conv_lhs => arg 2; rw [anchor_response_generated event T positive small]
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_mulVec,source_null_projection,
    Matrix.mulVec_mulVec,ng,Matrix.zero_mulVec,smul_zero,add_zero]

private theorem anchor_pencil (event : DressedEvent) (T : ℝ) :
    dressedNativeWindowPencil (anchorEvent event) 0 anchorInput 3 T=
      (T:ℂ) • originalJacobi anchorInput-dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T := by
  rw [dressedNativeWindowPencil,anchor_window_factor,nativeActionFourierHessian_original]

/-- The remaining full Euler residual is exactly the original compatibility lift. -/
theorem anchor_response_euler (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (forcing initial : SignalAmplitude) :
    dressedNativeWindowPencil (anchorEvent event) 0 anchorInput 3 T*ᵥanchorResponse event T forcing initial=
      forcing-originalRowLift anchorInput*ᵥsourceCompatibility anchorInput
        (forcing+dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥ
          anchorResponse event T forcing initial) := by
  have nonzero : (T:ℂ)≠0:=by exact_mod_cast positive.ne'
  rw [anchor_pencil,Matrix.sub_mulVec,Matrix.smul_mulVec]
  conv_lhs => arg 1; arg 2; rw [anchor_response_generated event T positive small]
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,source_null_euler,Matrix.zero_mulVec,zero_add,
    Matrix.mulVec_smul,smul_smul,mul_inv_cancel₀ nonzero,one_smul]
  have original:=original_forced_field generatedRegularPoint
    (forcing+dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥanchorResponse event T forcing initial)
  rw [PreparationVacuumOriginalGreenFeedback.sourceField,anchor_point] at original
  rw [original]
  abel

private theorem response_restores (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (a : SignalAmplitude) :
    anchorResponse event T (dressedNativeWindowPencil (anchorEvent event) 0 anchorInput 3 T*ᵥa) a=a := by
  have nonzero : (T:ℂ)≠0:=by exact_mod_cast positive.ne'
  have original:=sourceGreen_original_left generatedRegularPoint
  rw [anchor_point] at original
  change sourceGreen generatedRegularPoint*originalJacobi anchorInput=1-sourceNull anchorInput at original
  have equation : (T:ℂ)⁻¹ • (sourceGreen generatedRegularPoint*ᵥ
      (dressedNativeWindowPencil (anchorEvent event) 0 anchorInput 3 T*ᵥa))+sourceNull anchorInput*ᵥa=
      anchorFeedback event T*ᵥa := by
    rw [anchor_pencil,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.mulVec_sub,Matrix.mulVec_smul,
      smul_sub,smul_smul,inv_mul_cancel₀ nonzero,one_smul,Matrix.mulVec_mulVec,original,
      Matrix.sub_mulVec,Matrix.one_mulVec,anchorFeedback,Matrix.sub_mulVec,Matrix.one_mulVec,
      Matrix.smul_mulVec,←Matrix.mulVec_mulVec]
    abel
  rw [anchorResponse,equation,Matrix.mulVec_mulVec,(anchor_inverse_generated event T positive small).2,
    Matrix.one_mulVec]

/-- The complete source equation is reduced to its original nine compatibility rows, without deleting initial data. -/
theorem anchor_solution_iff (event : DressedEvent) (T : ℝ) (positive : 0 < T) (small : T ≤ 1)
    (forcing a : SignalAmplitude) :
    dressedNativeWindowPencil (anchorEvent event) 0 anchorInput 3 T*ᵥa=forcing ↔
      ∃initial : SignalAmplitude,a=anchorResponse event T forcing initial ∧
        sourceCompatibility anchorInput
          (forcing+dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥa)=0 := by
  constructor
  · intro equation
    refine ⟨a,?_,?_⟩
    · rw [←equation,response_restores event T positive small]
    · have sumEq : forcing+dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥa=
          (T:ℂ) • (originalJacobi anchorInput*ᵥa) := by
        rw [←equation,anchor_pencil,Matrix.sub_mulVec,Matrix.smul_mulVec]
        abel
      rw [sumEq,sourceCompatibility,Matrix.mulVec_smul,Matrix.mulVec_smul]
      change (T:ℂ) • sourceCompatibility anchorInput (originalJacobi anchorInput*ᵥa)=0
      rw [source_compatibility_euler,smul_zero]
  · rintro ⟨initial,rfl,compatible⟩
    rw [anchor_response_euler event T positive small,compatible,Matrix.mulVec_zero,sub_zero]

end LowEnergy.GaussComposite.ActualEMDressedConstraint
