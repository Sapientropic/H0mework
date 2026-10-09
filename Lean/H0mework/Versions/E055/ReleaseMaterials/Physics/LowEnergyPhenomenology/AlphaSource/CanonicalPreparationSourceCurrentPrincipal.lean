import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativePrincipal
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationActualCurrentWard

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback SourcePropagationNativeActionHessian
open PreparationVacuumPhysicalFieldChannel PreparationVacuumPhysicalZeroRead
open PreparationVacuumElectromagneticIdentity PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumCurrentSignalOperator CanonicalGradedSpatialSource
open PreparationVacuumPhysicalPoleHalfResponse SourcePropagationConstrainedPoleReturn
open scoped Matrix BigOperators
attribute [local irreducible] nativeHessian originalJacobi originalChange originalInverse originalReadback
  originalRowLift sourcePoleCurrentWindow sourceActualCurrentCosource

theorem sourceFrame_coordinates (p : Fin 4→ℂ) (a b : ℂ) :
    (jetFrame p*ᵥ(Pi.single 0 a+Pi.single 1 b)) 83=a ∧
    (jetFrame p*ᵥ(Pi.single 0 a+Pi.single 1 b)) 85=b :=by
  rw [Matrix.mulVec_add,Matrix.mulVec_single,Matrix.mulVec_single]
  norm_num [jetFrame,jetFrameTerms,sourceMatrix_append,sourceMatrix,kernelTerms,timeCorrectionTerms,
    spaceCorrectionTerms,SourceTerm.matrix,Matrix.single_apply,Powers.value,coefficientValue,Fin.ext_iff]

private theorem jetFrame_origin : jetFrame 0=kernelFrame 0 :=by
  have t : originTerms timeCorrectionTerms=[]:=by decide +kernel
  have x : originTerms spaceCorrectionTerms=[]:=by decide +kernel
  unfold jetFrame jetFrameTerms kernelFrame
  rw [sourceMatrix_append,sourceMatrix_append,←originTerms_generated timeCorrectionTerms,
    ←originTerms_generated spaceCorrectionTerms,t,x,sourceMatrix_nil,add_zero,add_zero]

private theorem origin_degree (terms : List SourceTerm) (degree : ℕ) (positive : degree≠0) :
    originTerms (terms.filter (fun a=>decide (a.powers.total=degree)))=[] :=by
  unfold originTerms
  apply List.filter_eq_nil_iff.mpr
  intro a member
  have degreeEq : a.powers.total=degree:=of_decide_eq_true (List.mem_filter.mp member).2
  simp [degreeEq,positive]

theorem sourceKernel_generated : activeKernel 0*kernelFrame 0=0 :=by
  have quadratic : originTerms quadraticTerms=[]:=origin_degree residualTerms 2 (by decide)
  have cubic : originTerms cubicTerms=[]:=origin_degree residualTerms 3 (by decide)
  have momentum : planeMomentum 0 0=0:=by ext i;fin_cases i <;> rfl
  have h:=sourceFrame_residual 0 0
  rw [momentum,jetFrame_origin,←originTerms_generated quadraticTerms,
    ←originTerms_generated cubicTerms,quadratic,cubic,sourceMatrix_nil,zero_add] at h
  exact h

theorem sourceKernel_independent (a b : ℂ)
    (zero : kernelFrame 0*ᵥ(Pi.single 0 a+Pi.single 1 b)=0) : a=0 ∧ b=0 :=by
  have coordinates:=sourceFrame_coordinates 0 a b
  rw [jetFrame_origin,zero] at coordinates
  exact ⟨coordinates.1.symm,coordinates.2.symm⟩

/-- The two mode coordinates are read from the actual field, not selected externally. -/
def sourceModeCoordinates (p : Fin 4→ℂ) (field : Fin 289→ℂ) : Fin 289→ℂ :=
  Pi.single 0 ((originalInverse p*ᵥfield) 83)+Pi.single 1 ((originalInverse p*ᵥfield) 85)

def sourceModeComplement (p : Fin 4→ℂ) (field : Fin 289→ℂ) : Fin 289→ℂ :=
  field-nativeJetFrame p*ᵥsourceModeCoordinates p field

theorem sourceModeComplement_coordinates (p : Fin 4→ℂ) (field : Fin 289→ℂ) :
    (originalInverse p*ᵥsourceModeComplement p field) 83=0 ∧
    (originalInverse p*ᵥsourceModeComplement p field) 85=0 :=by
  have coords:=sourceFrame_coordinates p ((originalInverse p*ᵥfield) 83) ((originalInverse p*ᵥfield) 85)
  simp only [sourceModeComplement,Matrix.mulVec_sub,nativeJetFrame,Matrix.mulVec_mulVec,
    ←mul_assoc,original_inverse_change,one_mul,Pi.sub_apply,sourceModeCoordinates] at ⊢
  rw [coords.1,coords.2]
  simp

/-- The source principal matrix and the entire complementary action are retained together. -/
theorem sourceMode_quotient (time space : ℂ) (field : Fin 289→ℂ) :
    sourcePrincipal time space*ᵥsourceModeCoordinates (planeMomentum time space) field+
      nativeTestFrame (planeMomentum time space)*ᵥ
        (nativeFourierHessian nativeHessian (planeMomentum time space)*ᵥ
          sourceModeComplement (planeMomentum time space) field)=
      nativeTestFrame (planeMomentum time space)*ᵥ
        (nativeFourierHessian nativeHessian (planeMomentum time space)*ᵥfield) :=by
  rw [sourceModeComplement,Matrix.mulVec_sub,Matrix.mulVec_sub]
  have actual:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>
      A*ᵥsourceModeCoordinates (planeMomentum time space) field) (native_principal_generated time space)
  simp only [←Matrix.mulVec_mulVec] at actual
  rw [actual]
  abel

private theorem sourceKernel_null_certificate :
    fastNormalizeTerms (productTerms (reflectedTerms kernelTerms) (projectionTerms nullFlag))=[] :=by decide +kernel

private theorem sourceKernel_null (p : Fin 4→ℂ) : reflectedKernelFrame p*nullProjection=0 :=by
  have h:=fastNormalizeTerms_value (productTerms (reflectedTerms kernelTerms) (projectionTerms nullFlag)) p
  rw [sourceKernel_null_certificate,sourceMatrix_nil,productTerms_value,projectionTerms_value] at h
  exact h.symm

private theorem sourceTest_row (p : Fin 4→ℂ) : nativeTestFrame p*originalRowLift p=reflectedKernelFrame p :=by
  have inverse : originalReadback p*originalRowLift p=1:=by
    rw [originalReadback,originalRowLift,←Matrix.transpose_mul,original_inverse_change,Matrix.transpose_one]
  rw [nativeTestFrame,mul_assoc,inverse,mul_one]

def sourceAxisTransfer (momentum : ℝ) : PhysicalMomentum:=![momentum,0,0]
def sourceAxisLeft (p : PhysicalMomentum) (momentum : ℝ) : PhysicalMomentum:=p-sourceAxisTransfer momentum

theorem sourceAxis_same_transfer (p : PhysicalMomentum) (momentum : ℝ) :
    sourcePhysicalTransfer (sourceAxisLeft p momentum) p=sourceAxisTransfer momentum :=by
  unfold sourcePhysicalTransfer sourceAxisLeft
  abel

def sourceAxisSpatial (momentum : ℝ) : Fin 3→ℂ :=physicalSpatial (sourceAxisTransfer momentum)

theorem sourceAxis_same_Fourier (time : ℂ) (momentum : ℝ) :
    fullMomentum (sourceAxisSpatial momentum) time=planeMomentum time (Complex.I*(momentum:ℂ)) :=by
  ext i
  fin_cases i
  · rfl
  · change Complex.I*(momentum:ℂ)=Complex.I*(momentum:ℂ)
    rfl
  · change Complex.I*(0:ℂ)=0
    ring
  · change Complex.I*(0:ℂ)=0
    ring

/-- Actual amplitude-zero current, with material transfer and physical spatial Fourier sign fixed by the same event. -/
def sourceAxisCurrent (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) : SignalAmplitude:=
  sourcePoleCurrentWindow q (sourceAxisLeft p momentum) p left right time T

def sourceAxisCosource (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) : SignalAmplitude:=
  sourceActualCurrentCosource q (sourceAxisLeft p momentum) p left right (sourceAxisSpatial momentum) time T

def sourceAxisClearedField (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) : SignalAmplitude:=
  originalClearedGreen (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
    sourceAxisCurrent q p momentum left right time T

theorem sourceAxis_current_ward (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) :
    originalReadback (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
      sourceAxisCurrent q p momentum left right time T=sourceAxisCosource q p momentum left right time T :=by
  have h:=sourceActualCurrentWindow_ward q (sourceAxisLeft p momentum) p left right (sourceAxisSpatial momentum) time T
  simpa only [sourceAxis_same_Fourier,sourceAxisCurrent,sourceAxisCosource] using h

theorem sourceAxis_current_twoModes (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) :
    nativeTestFrame (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
      sourceAxisCurrent q p momentum left right time T=
      reflectedKernelFrame (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
        sourceAxisCosource q p momentum left right time T :=by
  rw [nativeTestFrame,←Matrix.mulVec_mulVec,sourceAxis_current_ward]

theorem sourceAxis_whole_native (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) :
    nativeFourierHessian nativeHessian (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
      sourceAxisClearedField q p momentum left right time T=
      originalFieldDenominator (planeMomentum time (Complex.I*(momentum:ℂ))) •
        (sourceAxisCurrent q p momentum left right time T-
          originalRowLift (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
            (nullProjection*ᵥsourceAxisCosource q p momentum left right time T)) :=by
  rw [sourceAxisClearedField,nativeActionFourierHessian_original,Matrix.mulVec_mulVec,
    originalClearedGreen_equation,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec]
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,sourceAxis_current_ward]

/-- Exact coupled principal equation for the actual current; no complementary response is dropped. -/
theorem sourceAxis_principal_response (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) :
    sourcePrincipal time (Complex.I*(momentum:ℂ))*ᵥ
      sourceModeCoordinates (planeMomentum time (Complex.I*(momentum:ℂ)))
        (sourceAxisClearedField q p momentum left right time T)+
      nativeTestFrame (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
        (nativeFourierHessian nativeHessian (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
          sourceModeComplement (planeMomentum time (Complex.I*(momentum:ℂ)))
            (sourceAxisClearedField q p momentum left right time T))=
      originalFieldDenominator (planeMomentum time (Complex.I*(momentum:ℂ))) •
        (reflectedKernelFrame (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
          sourceAxisCosource q p momentum left right time T) :=by
  rw [sourceMode_quotient,sourceAxis_whole_native,Matrix.mulVec_smul,Matrix.mulVec_sub,
    sourceAxis_current_twoModes,Matrix.mulVec_mulVec,sourceTest_row,Matrix.mulVec_mulVec,
    sourceKernel_null,Matrix.zero_mulVec,sub_zero]

/-- All113 actual nilpotent history sectors enter the same two-mode reader. -/
theorem sourceActualEuler_twoModes (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (p : Fin 4→ℂ) (t : ℝ) :
    nativeTestFrame p*ᵥsourcePoleActionEuler q pL pR left right 0 t=
      ∑n : Fin 113,nativeTestFrame p*ᵥsourcePrincipalEulerSector q pL pR left right n t :=by
  have source : sourcePoleActionEuler q pL pR left right 0 t=
      ∑n : Fin 113,sourcePrincipalEulerSector q pL pR left right n t:=by
    ext i
    simpa only [Finset.sum_apply] using sourcePrincipalEuler_generated q pL pR left right t i
  rw [source,Matrix.mulVec_sum]

end LowEnergy.PreparationVacuumMixedPrincipal
