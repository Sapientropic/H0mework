import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourceFieldCovariance
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedSchur

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFieldCovariance
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullFieldRiesz
open SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualEMDressedSourceAnchor ActualEMDressedAnchorInverse ActualEMDressedConstraint ActualEMDressedSchur
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] sourceGreen dressedWindowPolarization anchorFeedbackResolvent
  sourceNullLift sourceCokernel sourceNullCoordinates nativeHessian

private theorem unit_matrix_mul (S U : Matrix (Fin 289) (Fin 289) ℝ) :
    sourceUnitMatrix (S*U)=sourceUnitMatrix S*sourceUnitMatrix U := by
  ext i j
  simp only [sourceUnitMatrix,Matrix.map_apply,Matrix.mul_apply,map_sum,map_mul]

private theorem unit_matrix_one : sourceUnitMatrix (1:Matrix (Fin 289) (Fin 289) ℝ)=1 := by
  ext i j
  simp [sourceUnitMatrix,Matrix.one_apply]

private theorem source_unit_inverse (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) :
    sourceUnitMatrix S*sourceUnitMatrix U=1 ∧ sourceUnitMatrix U*sourceUnitMatrix S=1 ∧
      (sourceUnitMatrix U).transpose*(sourceUnitMatrix S).transpose=1 := by
  have first : sourceUnitMatrix S*sourceUnitMatrix U=1 := by rw [←unit_matrix_mul,left,unit_matrix_one]
  have second : sourceUnitMatrix U*sourceUnitMatrix S=1 := by rw [←unit_matrix_mul,right,unit_matrix_one]
  exact ⟨first,second,by rw [←Matrix.transpose_mul,first,Matrix.transpose_one]⟩

def unitAnchorQuantum (event : DressedEvent) (S : Matrix (Fin 289) (Fin 289) ℝ) (T : ℝ) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  (sourceUnitMatrix S).transpose*dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*sourceUnitMatrix S

def unitAnchorGreen (U : Matrix (Fin 289) (Fin 289) ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  sourceUnitMatrix U*sourceGreen generatedRegularPoint*(sourceUnitMatrix U).transpose

def unitAnchorFeedback (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ) (T : ℝ) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  1-(T:ℂ)⁻¹ • (unitAnchorGreen U*unitAnchorQuantum event S T)

def unitAnchorInverse (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ) (T : ℝ) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  sourceUnitMatrix U*anchorFeedbackResolvent event T*sourceUnitMatrix S

/-- The original quantum normalization and action are transformed together. -/
theorem unit_anchor_pencil_split (event : DressedEvent) (S : Matrix (Fin 289) (Fin 289) ℝ) (T : ℝ) :
    unitWindowPencil (anchorEvent event) 0 anchorInput S 3 T=
      (T:ℂ) • ((sourceUnitMatrix S).transpose*nativeFourierHessian nativeHessian anchorInput*sourceUnitMatrix S)-
        unitAnchorQuantum event S T := by
  simp only [unitWindowPencil,dressedNativeWindowPencil,anchor_window_factor,unitAnchorQuantum,
    Matrix.mul_sub,Matrix.sub_mul,mul_smul_comm,smul_mul_assoc]

private theorem unit_feedback_product (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) (T : ℝ) :
    unitAnchorGreen U*unitAnchorQuantum event S T=
      sourceUnitMatrix U*(sourceGreen generatedRegularPoint*
        dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T)*sourceUnitMatrix S := by
  have pair:=source_unit_inverse S U left right
  unfold unitAnchorGreen unitAnchorQuantum
  calc
    _=sourceUnitMatrix U*sourceGreen generatedRegularPoint*
      ((sourceUnitMatrix U).transpose*(sourceUnitMatrix S).transpose)*
        dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*sourceUnitMatrix S := by noncomm_ring
    _=_ := by rw [pair.2.2,Matrix.mul_one];noncomm_ring

theorem unit_anchor_feedback_similarity (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) (T : ℝ) :
    unitAnchorFeedback event S U T=sourceUnitMatrix U*anchorFeedback event T*sourceUnitMatrix S := by
  rw [unitAnchorFeedback,unit_feedback_product event S U left right T,anchorFeedback]
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,mul_smul_comm,smul_mul_assoc,
    (source_unit_inverse S U left right).2.1,Matrix.mul_assoc]

/-- Invertibility comes from the actual source budget; units do not add an inverse premise. -/
theorem unit_anchor_inverse_generated (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) (T : ℝ) (positive : 0<T) (small : T≤1) :
    unitAnchorFeedback event S U T*unitAnchorInverse event S U T=1 ∧
      unitAnchorInverse event S U T*unitAnchorFeedback event S U T=1 := by
  have pair:=source_unit_inverse S U left right
  have inverse:=anchor_inverse_generated event T positive small
  rw [unit_anchor_feedback_similarity event S U left right T,unitAnchorInverse]
  constructor
  · calc
      _=sourceUnitMatrix U*anchorFeedback event T*(sourceUnitMatrix S*sourceUnitMatrix U)*
        anchorFeedbackResolvent event T*sourceUnitMatrix S := by noncomm_ring
      _=sourceUnitMatrix U*(anchorFeedback event T*anchorFeedbackResolvent event T)*sourceUnitMatrix S := by
        rw [pair.1,Matrix.mul_one];noncomm_ring
      _=1 := by rw [inverse.1,Matrix.mul_one,pair.2.1]
  · calc
      _=sourceUnitMatrix U*anchorFeedbackResolvent event T*(sourceUnitMatrix S*sourceUnitMatrix U)*
        anchorFeedback event T*sourceUnitMatrix S := by noncomm_ring
      _=sourceUnitMatrix U*(anchorFeedbackResolvent event T*anchorFeedback event T)*sourceUnitMatrix S := by
        rw [pair.1,Matrix.mul_one];noncomm_ring
      _=1 := by rw [inverse.2,Matrix.mul_one,pair.2.1]

def unitAnchorLift (U : Matrix (Fin 289) (Fin 289) ℝ) : (Fin 9→ℂ)→ₗ[ℂ]SignalAmplitude :=
  (Matrix.toLin' (sourceUnitMatrix U)).comp (sourceNullLift anchorInput)

def unitAnchorCokernel (U : Matrix (Fin 289) (Fin 289) ℝ) : SignalAmplitude→ₗ[ℂ](Fin 9→ℂ) :=
  (sourceCokernel anchorInput).comp (Matrix.toLin' (sourceUnitMatrix U).transpose)

def unitAnchorResponse (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ) (T : ℝ)
    (forcing : SignalAmplitude) (initial : Fin 9→ℂ) : SignalAmplitude :=
  unitAnchorInverse event S U T*ᵥ((T:ℂ)⁻¹ • (unitAnchorGreen U*ᵥforcing)+unitAnchorLift U initial)

/-- Original physical forcing and all nine original initial coordinates keep their source identity. -/
theorem unit_anchor_response_return (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) (T : ℝ) (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    unitAnchorResponse event S U T ((sourceUnitMatrix S).transpose*ᵥforcing) initial=
      sourceUnitMatrix U*ᵥanchorResponseNine event T forcing initial := by
  have pair:=source_unit_inverse S U left right
  have green : unitAnchorGreen U*ᵥ((sourceUnitMatrix S).transpose*ᵥforcing)=
      sourceUnitMatrix U*ᵥ(sourceGreen generatedRegularPoint*ᵥforcing) := by
    simp only [unitAnchorGreen,Matrix.mulVec_mulVec]
    have identity : sourceUnitMatrix U*sourceGreen generatedRegularPoint*(sourceUnitMatrix U).transpose*
        (sourceUnitMatrix S).transpose=sourceUnitMatrix U*sourceGreen generatedRegularPoint := by
      calc
        _=sourceUnitMatrix U*sourceGreen generatedRegularPoint*
          ((sourceUnitMatrix U).transpose*(sourceUnitMatrix S).transpose) := by noncomm_ring
        _=_ := by rw [pair.2.2,Matrix.mul_one]
    rw [identity]
  rw [unitAnchorResponse,green,unitAnchorLift,LinearMap.comp_apply,Matrix.toLin'_apply]
  rw [←Matrix.mulVec_smul,←Matrix.mulVec_add,unitAnchorInverse]
  simp only [Matrix.mulVec_mulVec,anchorResponseNine]
  congr 1
  rw [Matrix.mul_assoc,pair.1,Matrix.mul_one]

def unitAnchorSchur (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ) (T : ℝ) :
    Matrix (Fin 9) (Fin 9) ℂ :=
  LinearMap.toMatrix' ((unitAnchorCokernel U).comp ((Matrix.toLin' (unitAnchorQuantum event S T)).comp
    ((Matrix.toLin' (unitAnchorInverse event S U T)).comp (unitAnchorLift U))))

/-- The actual nine-dimensional source responsibility is independent of field units. -/
theorem unit_anchor_schur_unchanged (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) (T : ℝ) :
    unitAnchorSchur event S U T=anchorSchur event T := by
  have pair:=source_unit_inverse S U left right
  have middle : (sourceUnitMatrix U).transpose*unitAnchorQuantum event S T*
      unitAnchorInverse event S U T*sourceUnitMatrix U=
      dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*anchorFeedbackResolvent event T := by
    unfold unitAnchorQuantum unitAnchorInverse
    calc
      _=((sourceUnitMatrix U).transpose*(sourceUnitMatrix S).transpose)*
        dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*(sourceUnitMatrix S*sourceUnitMatrix U)*
          anchorFeedbackResolvent event T*(sourceUnitMatrix S*sourceUnitMatrix U) := by noncomm_ring
      _=_ := by rw [pair.2.2,pair.1];simp only [Matrix.one_mul,Matrix.mul_one]
  simp only [Matrix.mul_assoc] at middle
  unfold unitAnchorSchur anchorSchur
  apply congrArg LinearMap.toMatrix'
  apply LinearMap.ext
  intro initial
  simp only [unitAnchorCokernel,unitAnchorLift,LinearMap.comp_apply,Matrix.toLin'_apply,Matrix.mulVec_mulVec]
  rw [middle]

/-- The actual detector/source read keeps the complete response and all its initial data. -/
theorem unit_anchor_actual_interaction (solver detector source : DressedEvent)
    (S U : Matrix (Fin 289) (Fin 289) ℝ) (left : S*U=1) (right : U*S=1) (T : ℝ) (initial : Fin 9→ℂ) :
    dotProduct ((sourceUnitMatrix S).transpose*ᵥdressedCurrent detector 0)
      (unitAnchorResponse solver S U T ((sourceUnitMatrix S).transpose*ᵥdressedCurrent source 0) initial)=
      dotProduct (dressedCurrent detector 0) (anchorResponseNine solver T (dressedCurrent source 0) initial) := by
  rw [unit_anchor_response_return solver S U left right T]
  rw [dotProduct_comm ((sourceUnitMatrix S).transpose*ᵥdressedCurrent detector 0)
    (sourceUnitMatrix U*ᵥanchorResponseNine solver T (dressedCurrent source 0) initial)]
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec,(source_unit_inverse S U left right).1,Matrix.one_mulVec]


private theorem unit_quantum_forcing_return (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) (T : ℝ) (a : SignalAmplitude) :
    unitAnchorQuantum event S T*ᵥ(sourceUnitMatrix U*ᵥa)=
      (sourceUnitMatrix S).transpose*ᵥ(dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥa) := by
  have pair:=source_unit_inverse S U left right
  have product : unitAnchorQuantum event S T*sourceUnitMatrix U=
      (sourceUnitMatrix S).transpose*dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T := by
    unfold unitAnchorQuantum
    calc
      _=(sourceUnitMatrix S).transpose*dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*
        (sourceUnitMatrix S*sourceUnitMatrix U) := by noncomm_ring
      _=_ := by rw [pair.1,Matrix.mul_one]
  simpa only [Matrix.mulVec_mulVec] using congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥa) product

private theorem unit_cokernel_return (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) (a : SignalAmplitude) :
    unitAnchorCokernel U ((sourceUnitMatrix S).transpose*ᵥa)=sourceCokernel anchorInput a := by
  simp only [unitAnchorCokernel,LinearMap.comp_apply,Matrix.toLin'_apply,Matrix.mulVec_mulVec,
    (source_unit_inverse S U left right).2.2,Matrix.one_mulVec]

/-- The complete actual constraint remainder, including its source term, is preserved. -/
theorem unit_anchor_constraint_return (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) (T : ℝ) (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    unitAnchorCokernel U ((sourceUnitMatrix S).transpose*ᵥforcing+
      unitAnchorQuantum event S T*ᵥunitAnchorResponse event S U T ((sourceUnitMatrix S).transpose*ᵥforcing) initial)=
      sourceCokernel anchorInput (forcing+dressedWindowPolarization (anchorEvent event) 0 anchorInput 3 T*ᵥ
        anchorResponseNine event T forcing initial) := by
  rw [unit_anchor_response_return event S U left right T,
    unit_quantum_forcing_return event S U left right T,←Matrix.mulVec_add]
  exact unit_cokernel_return S U left right _

/-- Both sides of the same nine-source Schur equation retain their original values. -/
theorem unit_anchor_constraint_schur (event : DressedEvent) (S U : Matrix (Fin 289) (Fin 289) ℝ)
    (left : S*U=1) (right : U*S=1) (T : ℝ) (forcing : SignalAmplitude) (initial : Fin 9→ℂ) :
    unitAnchorCokernel U ((sourceUnitMatrix S).transpose*ᵥforcing+
      unitAnchorQuantum event S T*ᵥunitAnchorResponse event S U T ((sourceUnitMatrix S).transpose*ᵥforcing) initial)=
      anchorSchur event T*ᵥinitial-anchorSchurSource event T forcing :=
  (unit_anchor_constraint_return event S U left right T forcing initial).trans
    (anchor_schur_generated event T forcing initial)

/-- The full actual field equation is independent of a lawful real field-unit choice. -/
theorem unit_original_euler_iff (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (S U : Matrix (Fin 289) (Fin 289) ℝ) (left : S*U=1) (right : U*S=1)
    (lambda : ℂ) (T : ℝ) (a forcing : SignalAmplitude) :
    unitWindowPencil event transfer p S lambda T*ᵥ(sourceUnitMatrix U*ᵥa)=
      (sourceUnitMatrix S).transpose*ᵥforcing ↔ dressedNativeWindowPencil event transfer p lambda T*ᵥa=forcing := by
  have pair:=source_unit_inverse S U left right
  have product : unitWindowPencil event transfer p S lambda T*sourceUnitMatrix U=
      (sourceUnitMatrix S).transpose*dressedNativeWindowPencil event transfer p lambda T := by
    unfold unitWindowPencil
    calc
      _=(sourceUnitMatrix S).transpose*dressedNativeWindowPencil event transfer p lambda T*
        (sourceUnitMatrix S*sourceUnitMatrix U) := by noncomm_ring
      _=_ := by rw [pair.1,Matrix.mul_one]
  rw [Matrix.mulVec_mulVec,product,←Matrix.mulVec_mulVec]
  constructor
  · intro equal
    have original:=congrArg (fun v : SignalAmplitude=>(sourceUnitMatrix U).transpose*ᵥv) equal
    simpa only [Matrix.mulVec_mulVec,←Matrix.mul_assoc,pair.2.2,Matrix.one_mul,Matrix.one_mulVec] using original
  · exact congrArg (fun v : SignalAmplitude=>(sourceUnitMatrix S).transpose*ᵥv)

end LowEnergy.GaussComposite.ActualDressedFieldCovariance
