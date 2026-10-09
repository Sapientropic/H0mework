import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalPoleLaplace
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMovingCurrentInitialWard

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleHalfResponse
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumCurrentConstrainedInverse PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumCurrentSignalOperator PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFieldConstraintResponse SourcePropagationNativeActionHessian
open PreparationVacuumMixedFieldReturn
open scoped BigOperators Topology Matrix
attribute [local irreducible] sourceDressedField sourceDressedGreen sourceCompatibility
  sourcePoleCurrentHalf sourcePoleCorrectionHalf sourcePhysicalCurrentAmplitude

/-- Computed difference between the actual R-dressed prepared time0 insertion and the original wave vertex. -/
def sourcePoleInitialMismatch (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) : SignalAmplitude:=
  sourcePoleEulerInitial q pL pR left right-sourcePhysicalCurrentAmplitude pL pR left right

def sourcePoleQuantumIncrement (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) : SignalAmplitude:=
  (lambda-sourcePhysicalClock pL pR left right)⁻¹ • sourcePoleInitialMismatch q pL pR left right+
    sourcePoleCorrectionHalf q pL pR left right lambda

theorem sourcePoleQuantumHalf_wave_return (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) :
    sourcePoleCurrentHalf q pL pR left right lambda=
      sourcePhysicalCurrentHalf pL pR left right lambda+sourcePoleQuantumIncrement q pL pR left right lambda :=by
  rw [sourcePoleCurrentHalf_generated q pL pR left right lambda off,
    sourcePhysicalCurrentHalf_generated pL pR left right lambda off]
  unfold sourcePoleQuantumIncrement sourcePoleInitialMismatch
  rw [smul_sub]
  abel

def sourcePoleQuantumIncrementPrice (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (i : Fin 289) : ℝ:=
  ‖lambda-sourcePhysicalClock pL pR left right‖⁻¹*‖sourcePoleInitialMismatch q pL pR left right i‖+
    (2/lambda.re)*sourcePoleCorrectionDecay q pL pR left right lambda i

theorem sourcePoleQuantumIncrement_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (i : Fin 289) :
    ‖sourcePoleQuantumIncrement q pL pR left right lambda i‖ ≤
      sourcePoleQuantumIncrementPrice q pL pR left right lambda i :=by
  have correction:=sourcePoleCorrectionHalf_price q pL pR left right lambda off i
  unfold sourcePoleQuantumIncrement sourcePoleQuantumIncrementPrice
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,norm_mul,norm_inv] using
    (norm_add_le ((lambda-sourcePhysicalClock pL pR left right)⁻¹*sourcePoleInitialMismatch q pL pR left right i)
      (sourcePoleCorrectionHalf q pL pR left right lambda i)).trans
      (add_le_add (le_refl _) correction)

def sourcePoleDressedField (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)) :
    SignalAmplitude:=
  sourceDressedField (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency
    (sourcePoleCurrentHalf q pL pR left right frequency.val.val.val)

def sourcePoleDressedIncrement (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)) :
    SignalAmplitude:=
  sourceDressedField (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency
    (sourcePoleQuantumIncrement q pL pR left right frequency.val.val.val)

theorem sourcePoleDressedField_wave_return (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)) :
    sourcePoleDressedField q pL pR left right frequency=
      sourcePhysicalDrivenField q pL pR left right frequency+sourcePoleDressedIncrement q pL pR left right frequency :=by
  unfold sourcePoleDressedField
  rw [sourcePoleQuantumHalf_wave_return q pL pR left right _ (sourcePhysicalFrequency_positive q pL pR left right frequency)]
  simp only [sourceDressedField,Matrix.mulVec_add,sourcePhysicalDrivenField,sourcePoleDressedIncrement]

private theorem rowPrice {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (input : Fin m→ℂ) (price : Fin m→ℝ)
    (bound : ∀i,‖input i‖ ≤ price i) (row : Fin n) :
    ‖(A*ᵥinput) row‖ ≤ ∑i : Fin m,‖A row i‖*price i :=by
  rw [Matrix.mulVec,dotProduct]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (bound i) (norm_nonneg _)

def sourcePoleDressedIncrementPrice (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right))
    (row : Fin 289) : ℝ:=
  ∑i : Fin 289,‖sourceDressedGreen (sourcePhysicalMediumPoint q pL pR)
      (sourcePhysicalClock pL pR left right) frequency row i‖*
    sourcePoleQuantumIncrementPrice q pL pR left right frequency.val.val.val i

theorem sourcePoleDressedIncrement_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right))
    (row : Fin 289) :
    ‖sourcePoleDressedIncrement q pL pR left right frequency row‖ ≤
      sourcePoleDressedIncrementPrice q pL pR left right frequency row :=by
  unfold sourcePoleDressedIncrement sourceDressedField sourcePoleDressedIncrementPrice
  exact rowPrice _ _ _
    (fun i=>sourcePoleQuantumIncrement_price q pL pR left right _
      (sourcePhysicalFrequency_positive q pL pR left right frequency) i) row

def sourcePoleWindowField (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right))
    (T : ℝ) : SignalAmplitude:=
  sourceDressedField (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency
    (sourcePoleCurrentWindow q pL pR left right frequency.val.val.val T)

def sourcePoleFieldTail (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right))
    (T : ℝ) (row : Fin 289) : ℝ:=
  ∑i : Fin 289,‖sourceDressedGreen (sourcePhysicalMediumPoint q pL pR)
      (sourcePhysicalClock pL pR left right) frequency row i‖*
    sourcePoleCurrentTail q pL pR left right frequency.val.val.val T i

theorem sourcePoleDressedField_tail_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right))
    (T : ℝ) (future : 0 ≤ T) (row : Fin 289) :
    ‖(sourcePoleDressedField q pL pR left right frequency-sourcePoleWindowField q pL pR left right frequency T) row‖ ≤
      sourcePoleFieldTail q pL pR left right frequency T row :=by
  have difference : sourcePoleDressedField q pL pR left right frequency-sourcePoleWindowField q pL pR left right frequency T=
      sourceDressedGreen (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency*ᵥ
        (sourcePoleCurrentHalf q pL pR left right frequency.val.val.val-
          sourcePoleCurrentWindow q pL pR left right frequency.val.val.val T) :=by
    simp only [sourcePoleDressedField,sourcePoleWindowField,sourceDressedField,Matrix.mulVec_sub]
  rw [difference]
  exact rowPrice _ _ _
    (fun i=>sourcePoleCurrentHalf_tail_price q pL pR left right _
      (sourcePhysicalFrequency_positive q pL pR left right frequency) T future i) row

def sourcePoleQuantumFeedback (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)) :
    SignalAmplitude:=
  sourceLaplaceCurrent (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency.val.val.val
      (sourcePoleDressedField q pL pR left right frequency)+
    sourceLaplaceInitial (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency.val.val.val
      (sourcePoleDressedField q pL pR left right frequency)

theorem sourcePoleDressedField_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)) :
    sourcePoleDressedField q pL pR left right frequency=
      sourceCommonFieldUpdate (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)
        frequency.val.val (sourcePoleCurrentHalf q pL pR left right frequency.val.val.val)
        (sourcePoleDressedField q pL pR left right frequency) :=
  sourceDressedField_generated _ _ _ _

theorem sourcePoleDressedField_initial_return (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)) :
    let p:=sourceMovingReadMomentum pL pR frequency.val.val.val
    let returned:=sourcePoleDressedField q pL pR left right frequency
    let feedback:=sourcePoleQuantumFeedback q pL pR left right frequency
    nativeFourierHessian nativeHessian p*ᵥreturned+
      originalRowLift p*ᵥ(sourceMovingInitialCovector pL pR left right+
        sourceCompatibility p (sourcePoleQuantumIncrement q pL pR left right frequency.val.val.val))=
      sourcePoleCurrentHalf q pL pR left right frequency.val.val.val+feedback-
        originalRowLift p*ᵥsourceCompatibility p feedback :=by
  let p:=sourceMovingReadMomentum pL pR frequency.val.val.val
  let external:=sourcePoleCurrentHalf q pL pR left right frequency.val.val.val
  let increment:=sourcePoleQuantumIncrement q pL pR left right frequency.val.val.val
  let returned:=sourcePoleDressedField q pL pR left right frequency
  let feedback:=sourcePoleQuantumFeedback q pL pR left right frequency
  change nativeFourierHessian nativeHessian p*ᵥreturned+
    originalRowLift p*ᵥ(sourceMovingInitialCovector pL pR left right+sourceCompatibility p increment)=
      external+feedback-originalRowLift p*ᵥsourceCompatibility p feedback
  have native : nativeFourierHessian nativeHessian p*ᵥreturned=
      external+feedback-originalRowLift p*ᵥsourceCompatibility p (external+feedback) :=by
    have paid:=sourceDressedField_native (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency external
    simpa only [p,sourceMovingReadMomentum,external,feedback,returned,sourcePoleDressedField,
      sourceDressedSource,sourcePoleQuantumFeedback,sourcePhysicalMediumPoint,sourcePhysicalTransfer,add_assoc] using paid
  have add (a b : SignalAmplitude) : sourceCompatibility p (a+b)=sourceCompatibility p a+sourceCompatibility p b :=by
    unfold sourceCompatibility
    rw [Matrix.mulVec_add,Matrix.mulVec_add]
  have initial : sourceCompatibility p external=
      sourceMovingInitialCovector pL pR left right+sourceCompatibility p increment :=by
    dsimp [external,increment]
    rw [sourcePoleQuantumHalf_wave_return q pL pR left right _ (sourcePhysicalFrequency_positive q pL pR left right frequency),add]
    rw [sourceMovingPhysicalHalf_initial pL pR left right _ (sourcePhysicalFrequency_positive q pL pR left right frequency)]
  rw [add,initial,Matrix.mulVec_add] at native
  rw [native]
  abel

def sourcePoleDressedCurvature (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)) :
    Fin 36→ℂ:=
  sourceDressedCurvature (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency*ᵥ
    sourcePoleCurrentHalf q pL pR left right frequency.val.val.val

theorem sourcePoleDressedCurvature_actual (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)) :
    sourcePoleDressedCurvature q pL pR left right frequency=
      originalReader36 (sourceMovingReadMomentum pL pR frequency.val.val.val)*ᵥsourcePoleDressedField q pL pR left right frequency :=
  sourceDressedCurvature_actual _ _ _ _

theorem sourcePoleDressedCurvature_initial_return (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right)) :
    let p:=sourceMovingReadMomentum pL pR frequency.val.val.val
    let returned:=sourcePoleDressedField q pL pR left right frequency
    let feedback:=sourcePoleQuantumFeedback q pL pR left right frequency
    originalReader36 p*ᵥ(nativeFourierHessian nativeHessian p*ᵥreturned)+
      originalReader36 p*ᵥ(originalRowLift p*ᵥ(sourceMovingInitialCovector pL pR left right+
        sourceCompatibility p (sourcePoleQuantumIncrement q pL pR left right frequency.val.val.val)))=
      originalReader36 p*ᵥ(sourcePoleCurrentHalf q pL pR left right frequency.val.val.val+feedback)-
        originalReader36 p*ᵥ(originalRowLift p*ᵥsourceCompatibility p feedback) :=by
  have paid:=congrArg (fun value=>originalReader36 (sourceMovingReadMomentum pL pR frequency.val.val.val)*ᵥvalue)
    (sourcePoleDressedField_initial_return q pL pR left right frequency)
  simpa only [Matrix.mulVec_add,Matrix.mulVec_sub] using paid

def sourcePoleWindowCurvature (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right))
    (T : ℝ) : Fin 36→ℂ:=
  sourceDressedCurvature (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency*ᵥ
    sourcePoleCurrentWindow q pL pR left right frequency.val.val.val T

def sourcePoleCurvatureTail (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right))
    (T : ℝ) (row : Fin 36) : ℝ:=
  ∑i : Fin 289,‖sourceDressedCurvature (sourcePhysicalMediumPoint q pL pR)
      (sourcePhysicalClock pL pR left right) frequency row i‖*
    sourcePoleCurrentTail q pL pR left right frequency.val.val.val T i

theorem sourcePoleDressedCurvature_tail_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right))
    (T : ℝ) (future : 0 ≤ T) (row : Fin 36) :
    ‖(sourcePoleDressedCurvature q pL pR left right frequency-sourcePoleWindowCurvature q pL pR left right frequency T) row‖ ≤
      sourcePoleCurvatureTail q pL pR left right frequency T row :=by
  have difference : sourcePoleDressedCurvature q pL pR left right frequency-sourcePoleWindowCurvature q pL pR left right frequency T=
      sourceDressedCurvature (sourcePhysicalMediumPoint q pL pR) (sourcePhysicalClock pL pR left right) frequency*ᵥ
        (sourcePoleCurrentHalf q pL pR left right frequency.val.val.val-
          sourcePoleCurrentWindow q pL pR left right frequency.val.val.val T) :=by
    simp only [sourcePoleDressedCurvature,sourcePoleWindowCurvature,Matrix.mulVec_sub]
  rw [difference]
  exact rowPrice _ _ _
    (fun i=>sourcePoleCurrentHalf_tail_price q pL pR left right _
      (sourcePhysicalFrequency_positive q pL pR left right frequency) T future i) row

end LowEnergy.PreparationVacuumPhysicalPoleHalfResponse
