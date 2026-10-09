import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullOriginSchur
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCurrentSupport

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullOriginResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open PreparationVacuumWholeOrigin SourcePropagationNativeActionHessian CanonicalGradedSpatialSource
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback SourcePropagationConstrainedPoleReturn
open PreparationVacuumPhysicalZeroRead PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMixedFieldReturn PreparationVacuumCurrentSignalOperator PreparationVacuumPhysicalCurrentLaplaceReturn
open scoped Matrix BigOperators Topology
attribute [local irreducible] activeKernel originalChange originalInverse originalReadback originalRowLift fullKernelFrame

private theorem readback_row (p : Fin 4→ℂ) : originalReadback p*originalRowLift p=1:=by
  have h:=congrArg Matrix.transpose (original_inverse_change (-p))
  simpa only [Matrix.transpose_mul,Matrix.transpose_one,originalReadback,originalRowLift] using h

theorem active_square : activeProjection*activeProjection=activeProjection:=by
  unfold activeProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem active_null : activeProjection*nullProjection=0:=by
  have separated : ∀i : Fin 289,activeFlag i=true→nullFlag i=false:=by decide +kernel
  unfold activeProjection nullProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : activeFlag i=true
  · simp [Matrix.diagonal_apply,separated i h]
  · simp [Matrix.diagonal_apply,h]

theorem activeKernel_right (p : Fin 4→ℂ) : activeKernel p*activeProjection=activeKernel p:=by
  have h:=congrArg Matrix.transpose (original_active_support (-p))
  simpa only [Matrix.transpose_mul,activeKernel_reflect,activeProjection,projectionMatrix,Matrix.diagonal_transpose] using h

def selectorTerms : List SourceTerm := [⟨0,83,⟨0,0,0,0⟩,1⟩,⟨1,85,⟨0,0,0,0⟩,1⟩,
  ⟨2,89,⟨0,0,0,0⟩,1⟩,⟨3,95,⟨0,0,0,0⟩,1⟩,⟨4,101,⟨0,0,0,0⟩,1⟩]
def modeSelector : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix selectorTerms 0
def blockCoordinates (field : Fin 289→ℂ) : Fin 289→ℂ:=modeSelector*ᵥfield

def blockComplement (_p : Fin 4→ℂ) (field : Fin 289→ℂ) : Fin 289→ℂ:=field-fullKernelFrame*ᵥblockCoordinates field

private theorem complement_support_certificate :
    fastNormalizeTerms ((projectionTerms activeFlag++negativeTerms (productTerms fullKernelTerms selectorTerms))++
      negativeTerms (productTerms (projectionTerms fullComplementFlag)
        (projectionTerms activeFlag++negativeTerms (productTerms fullKernelTerms selectorTerms))))=[] :=by decide +kernel

theorem blockComplement_supported (p : Fin 4→ℂ) (field : Fin 289→ℂ)
    (inside : activeProjection*ᵥfield=field) : fullComplementProjection*ᵥblockComplement p field=blockComplement p field :=by
  have h:=normalization_equal _ _ complement_support_certificate p
  simp only [sourceMatrix_append,negativeTerms_value,productTerms_value,projectionTerms_value] at h
  have selector : sourceMatrix selectorTerms p=modeSelector:=rfl
  have dual : sourceMatrix fullKernelTerms p=fullKernelFrame:=fullKernel_generated p
  rw [selector,dual] at h
  have returned:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A*ᵥfield) h
  have insideLiteral : projectionMatrix activeFlag*ᵥfield=field:=inside
  simp only [Matrix.add_mulVec,Matrix.neg_mulVec,←Matrix.mulVec_mulVec,insideLiteral] at returned
  simpa only [blockComplement,blockCoordinates,fullKernelFrame,fullComplementProjection,sub_eq_add_neg] using returned.symm

/-- Exact reconstruction of the actual complementary field from the source equation. -/
theorem blockComplement_generated (p : complementRegular) (field forcing : Fin 289→ℂ)
    (inside : activeProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    blockComplement p.val field=complementGreen p*ᵥ(forcing-activeKernel p.val*ᵥ(fullKernelFrame*ᵥblockCoordinates field)) :=by
  apply complement_response p _ _ (blockComplement_supported p.val field inside)
  rw [blockComplement,Matrix.mulVec_sub,equation]

theorem effective_actual_equation (p : complementRegular) (field forcing : Fin 289→ℂ)
    (inside : activeProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    effectiveKernel p*ᵥblockCoordinates field=effectiveReader p*ᵥforcing :=by
  have split : field=fullKernelFrame*ᵥblockCoordinates field+blockComplement p.val field:=by
    unfold blockComplement;abel
  have annihilate : effectiveReader p*ᵥ(activeKernel p.val*ᵥblockComplement p.val field)=0:=by
    rw [←blockComplement_supported p.val field inside,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
      effectiveReader_complement,Matrix.zero_mulVec]
  have actual:=congrArg (fun v=>effectiveReader p*ᵥv) equation
  conv_lhs at actual=>rw [split]
  rw [Matrix.mulVec_add,Matrix.mulVec_add,annihilate,add_zero,
    Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,effectiveKernel_generated] at actual
  exact actual

theorem effective_field_reconstruction (p : complementRegular) (field forcing : Fin 289→ℂ)
    (inside : activeProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    field=effectiveFrame p*ᵥblockCoordinates field+complementGreen p*ᵥforcing :=by
  have returned:=blockComplement_generated p field forcing inside equation
  rw [blockComplement,Matrix.mulVec_sub] at returned
  rw [effectiveFrame,Matrix.sub_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  linear_combination returned


private theorem selector_return_certificate :
    fastNormalizeTerms (productTerms selectorTerms fullKernelTerms++negativeTerms fiveProjectionTerms)=[]:=by decide +kernel

theorem fullKernel_coordinates : modeSelector*fullKernelFrame=fiveProjection:=by
  have h:=normalization_equal _ _ selector_return_certificate (0:Fin 4→ℂ)
  rw [productTerms_value,fullKernel_generated] at h
  exact h

theorem fullKernel_independent (left right : Fin 5→ℂ)
    (same : fullKernelFrame*ᵥfiveVector left=fullKernelFrame*ᵥfiveVector right) : left=right:=by
  have h:=congrArg (fun v=>modeSelector*ᵥv) same
  simp only [Matrix.mulVec_mulVec,fullKernel_coordinates,fiveProjection_vector] at h
  funext i
  have hi:=congrFun h (⟨i.val,by omega⟩:Fin 289)
  simpa only [fiveVector,dif_pos i.isLt] using hi

def actualMomentum (pL pR : PhysicalMomentum) (lambda : ℂ) : Fin 4→ℂ:=
  fullMomentum (physicalSpatial (sourcePhysicalTransfer pL pR)) lambda

def actualCurrent (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : SignalAmplitude:=sourcePoleCurrentWindow q pL pR left right lambda T

def actualCosource (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : SignalAmplitude:=
  sourceActualCurrentCosource q pL pR left right (physicalSpatial (sourcePhysicalTransfer pL pR)) lambda T

def actualNativeField (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : SignalAmplitude:=
  originalClearedGreen (actualMomentum pL pR lambda)*ᵥactualCurrent q pL pR left right lambda T

def actualField (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : SignalAmplitude:=
  activeProjection*ᵥ(originalInverse (actualMomentum pL pR lambda)*ᵥactualNativeField q pL pR left right lambda T)

def actualForcing (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : SignalAmplitude:=
  originalFieldDenominator (actualMomentum pL pR lambda) • (activeProjection*ᵥactualCosource q pL pR left right lambda T)

theorem actual_current_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) :
    originalReadback (actualMomentum pL pR lambda)*ᵥactualCurrent q pL pR left right lambda T=
      actualCosource q pL pR left right lambda T:=
  sourceActualCurrentWindow_ward q pL pR left right _ lambda T

theorem actual_whole_native (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) :
    nativeFourierHessian nativeHessian (actualMomentum pL pR lambda)*ᵥactualNativeField q pL pR left right lambda T=
      originalFieldDenominator (actualMomentum pL pR lambda) •
        (actualCurrent q pL pR left right lambda T-originalRowLift (actualMomentum pL pR lambda)*ᵥ
          (nullProjection*ᵥactualCosource q pL pR left right lambda T)):=by
  rw [actualNativeField,nativeActionFourierHessian_original,Matrix.mulVec_mulVec,originalClearedGreen_equation,
    Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec]
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,actual_current_ward]

theorem actual_source (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : activeKernel (actualMomentum pL pR lambda)*ᵥactualField q pL pR left right lambda T=
      actualForcing q pL pR left right lambda T:=by
  let P:=actualMomentum pL pR lambda
  have original:=actual_whole_native q pL pR left right lambda T
  have projected:=congrArg (fun v=>activeProjection*ᵥ(originalReadback P*ᵥv)) original
  have nullRead (c : SignalAmplitude) : activeProjection*ᵥ(originalReadback P*ᵥ(originalRowLift P*ᵥ(nullProjection*ᵥc)))=0:=by
    rw [Matrix.mulVec_mulVec (nullProjection*ᵥc) (originalReadback P) (originalRowLift P),readback_row,Matrix.one_mulVec,
      Matrix.mulVec_mulVec,active_null,Matrix.zero_mulVec]
  simp only [Matrix.mulVec_smul,Matrix.mulVec_sub] at projected
  rw [actual_current_ward,nullRead,sub_zero] at projected
  unfold actualField actualForcing
  rw [Matrix.mulVec_mulVec,activeKernel_right]
  simp only [Matrix.mulVec_mulVec] at projected ⊢
  rw [←mul_assoc,original_active_field] at projected
  simpa only [P,mul_assoc] using projected

theorem actual_inside (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : activeProjection*ᵥactualField q pL pR left right lambda T=actualField q pL pR left right lambda T:=by
  rw [actualField,Matrix.mulVec_mulVec,active_square]

theorem actual_effective_dynamics (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) (regular : actualMomentum pL pR lambda∈complementRegular) :
    effectiveKernel ⟨actualMomentum pL pR lambda,regular⟩*ᵥblockCoordinates (actualField q pL pR left right lambda T)=
      effectiveReader ⟨actualMomentum pL pR lambda,regular⟩*ᵥactualForcing q pL pR left right lambda T:=
  effective_actual_equation _ _ _ (actual_inside q pL pR left right lambda T) (actual_source q pL pR left right lambda T)

theorem actual_complement_return (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) (regular : actualMomentum pL pR lambda∈complementRegular) :
    blockComplement (actualMomentum pL pR lambda) (actualField q pL pR left right lambda T)=
      complementGreen ⟨actualMomentum pL pR lambda,regular⟩*ᵥ
        (actualForcing q pL pR left right lambda T-activeKernel (actualMomentum pL pR lambda)*ᵥ
          (fullKernelFrame*ᵥblockCoordinates (actualField q pL pR left right lambda T))):=
  blockComplement_generated _ _ _ (actual_inside q pL pR left right lambda T) (actual_source q pL pR left right lambda T)

theorem actual_native_reconstruction (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) (regular : actualMomentum pL pR lambda∈complementRegular) :
    originalChange (actualMomentum pL pR lambda)*ᵥactualField q pL pR left right lambda T=
      nativeEffectiveFrame ⟨actualMomentum pL pR lambda,regular⟩*ᵥblockCoordinates (actualField q pL pR left right lambda T)+
      originalChange (actualMomentum pL pR lambda)*ᵥ
        (complementGreen ⟨actualMomentum pL pR lambda,regular⟩*ᵥactualForcing q pL pR left right lambda T):=by
  have h:=effective_field_reconstruction (⟨actualMomentum pL pR lambda,regular⟩:complementRegular) _ _
    (actual_inside q pL pR left right lambda T) (actual_source q pL pR left right lambda T)
  have returned:=congrArg (fun v=>originalChange (actualMomentum pL pR lambda)*ᵥv) h
  simpa only [Matrix.mulVec_add,Matrix.mulVec_mulVec,nativeEffectiveFrame] using returned

theorem origin_kernel_complete (field : SignalAmplitude) (inside : activeProjection*ᵥfield=field)
    (kernel : activeKernel 0*ᵥfield=0) : field=fullKernelFrame*ᵥblockCoordinates field:=by
  have h:=blockComplement_generated complementOrigin field 0 inside kernel
  have vanished : blockComplement 0 field=0:=by
    change blockComplement 0 field=complementGreen complementOrigin*ᵥ(0-activeKernel 0*ᵥ(fullKernelFrame*ᵥblockCoordinates field)) at h
    rw [Matrix.mulVec_mulVec,fullKernel_origin,Matrix.zero_mulVec,sub_zero,Matrix.mulVec_zero] at h
    exact h
  unfold blockComplement at vanished
  exact sub_eq_zero.mp vanished

theorem actual_forcing_twoSectors (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : actualForcing q pL pR left right lambda T=
      originalFieldDenominator (actualMomentum pL pR lambda) •
        (activeProjection*ᵥ(originalReadback (actualMomentum pL pR lambda)*ᵥ
          (sourcePrincipalWindow q pL pR left right lambda T 0+sourcePrincipalWindow q pL pR left right lambda T 1))):=by
  unfold actualForcing
  rw [←actual_current_ward]
  unfold actualCurrent
  rw [sourceActualWindow_twoSectors]


/-- The source-generated effective response restores the whole field, retaining its actual contact and null components. -/
theorem actual_whole_reconstruction (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) (regular : actualMomentum pL pR lambda∈complementRegular) :
    actualNativeField q pL pR left right lambda T=
      originalChange (actualMomentum pL pR lambda)*ᵥ
        (contactProjection*ᵥ(originalInverse (actualMomentum pL pR lambda)*ᵥactualNativeField q pL pR left right lambda T))+
      (nativeEffectiveFrame ⟨actualMomentum pL pR lambda,regular⟩*ᵥblockCoordinates (actualField q pL pR left right lambda T)+
        originalChange (actualMomentum pL pR lambda)*ᵥ
          (complementGreen ⟨actualMomentum pL pR lambda,regular⟩*ᵥactualForcing q pL pR left right lambda T))+
      originalChange (actualMomentum pL pR lambda)*ᵥ
        (nullProjection*ᵥ(originalInverse (actualMomentum pL pR lambda)*ᵥactualNativeField q pL pR left right lambda T)):=by
  let P:=actualMomentum pL pR lambda
  let field:=actualNativeField q pL pR left right lambda T
  let x:=originalInverse P*ᵥfield
  have partition : x=contactProjection*ᵥx+activeProjection*ᵥx+nullProjection*ᵥx:=by
    have h:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥx) projection_partition
    simpa only [Matrix.add_mulVec,Matrix.one_mulVec] using h.symm
  have recovered : field=originalChange P*ᵥ(contactProjection*ᵥx)+
      originalChange P*ᵥactualField q pL pR left right lambda T+originalChange P*ᵥ(nullProjection*ᵥx):=by
    calc
      _=originalChange P*ᵥx:=by dsimp only [x];rw [Matrix.mulVec_mulVec,original_change_inverse,Matrix.one_mulVec]
      _= _ :=by
        have h:=congrArg (fun v=>originalChange P*ᵥv) partition
        simpa only [Matrix.mulVec_add,actualField,x,P,field] using h
  change field= _
  exact recovered.trans (congrArg (fun middle=>originalChange P*ᵥ(contactProjection*ᵥx)+middle+
    originalChange P*ᵥ(nullProjection*ᵥx)) (actual_native_reconstruction q pL pR left right lambda T regular))



open PreparationVacuumPhysicalConstraint114

private def fullNativeOriginTermsAtoms : List SourceAtom := [
  (⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩)]
private def fullNativeOriginTermsCodes : List ℕ := [
  48552,48560,78609,78617,171106,175731,184986,189611,198866,203458,203466,203491,212706,212738,217338,217363,226604,231229,
  240468,245093,254324,254357,258956,258980,268229,272820,272828,272852,501710,501718,531767,531775]
def fullNativeOriginTerms : List SourceTerm := decodeTerms fullNativeOriginTermsAtoms fullNativeOriginTermsCodes

def fullNativeOrigin : Matrix (Fin 289) (Fin 289) ℂ:=originalChange 0*fullKernelFrame

private theorem full_native_certificate :
    fastNormalizeTerms (productTerms (PreparationVacuumMixedPrincipal.originTerms originalChangeTerms) fullKernelTerms++
      negativeTerms fullNativeOriginTerms)=[]:=by decide +kernel

theorem fullNativeOrigin_generated : fullNativeOrigin=sourceMatrix fullNativeOriginTerms 0:=by
  have h:=normalization_equal _ _ full_native_certificate (0:Fin 4→ℂ)
  rw [productTerms_value,originTerms_generated,fullKernel_generated] at h
  simpa only [fullNativeOrigin,originalChange] using h

private theorem fullNative_held_read (v : SignalAmplitude) (held : ∀i,sourceHeldUnsupported i→v i=0) :
    fullNativeOrigin.transpose*ᵥv=
      Pi.single 0 ((3/10:ℂ)*rootTwo*(v 21-v 34))+Pi.single 1 ((3/10:ℂ)*rootTwo*(v 21-v 34)):=by
  rw [fullNativeOrigin_generated]
  norm_num [fullNativeOriginTerms,fullNativeOriginTermsAtoms,fullNativeOriginTermsCodes,decodeTerms,
    sourceMatrix,SourceTerm.matrix,Matrix.transpose_add,Matrix.transpose_single,Matrix.transpose_zero,
    Matrix.add_mulVec,Matrix.zero_mulVec,Matrix.single_mulVec,Powers.value,coefficientValue]
  simp (disch:=norm_num [sourceHeldUnsupported]) only [held]
  have v21 (h : 21<289) : v (⟨21,h⟩:Fin 289)=v 21:=rfl
  have v34 (h : 34<289) : v (⟨34,h⟩:Fin 289)=v 34:=rfl
  simp only [v21,v34,mul_zero]
  ext i
  simp only [Pi.single_apply,Function.update_apply,Pi.zero_apply,Pi.add_apply]
  split_ifs <;> ring

/-- The two canonical origin modes receive the actual held source current weight; no unit-column forcing is supplied. -/
theorem actual_origin_kernel_read (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : fullNativeOrigin.transpose*ᵥactualCurrent q pL pR left right lambda T=
      Pi.single 0 ((3/10:ℂ)*rootTwo*(actualCurrent q pL pR left right lambda T 21-actualCurrent q pL pR left right lambda T 34))+
      Pi.single 1 ((3/10:ℂ)*rootTwo*(actualCurrent q pL pR left right lambda T 21-actualCurrent q pL pR left right lambda T 34)):=by
  apply fullNative_held_read
  intro i hi
  exact sourceHeld_actualWindow_zero q pL pR left right lambda T i hi



open scoped Matrix.Norms.Operator

/-- The complete, source-controlled tensor prices the response of the actual current on its physical momentum transfer. -/
theorem actual_effective_response_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T r : ℝ) (nonneg : 0 ≤ r) (cap : r ≤ sourceRadius)
    (bound : ∀i,‖actualMomentum pL pR lambda i‖ ≤ r) :
    ‖leadingTensor (actualMomentum pL pR lambda)*ᵥblockCoordinates (actualField q pL pR left right lambda T)-
      effectiveReader (controlledPoint (actualMomentum pL pR lambda) (fun i=>(bound i).trans cap))*ᵥ
        actualForcing q pL pR left right lambda T‖ ≤
      effectiveErrorBudget*r^3*‖blockCoordinates (actualField q pL pR left right lambda T)‖:=by
  let point:=controlledPoint (actualMomentum pL pR lambda) (fun i=>(bound i).trans cap)
  have actual:=actual_effective_dynamics q pL pR left right lambda T point.property
  have price:=effectiveKernel_leading_price (actualMomentum pL pR lambda) r nonneg cap bound
  dsimp only [controlledPoint] at price ⊢
  rw [←actual,←Matrix.sub_mulVec]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right (by simpa only [norm_sub_rev] using price) (norm_nonneg _))


end LowEnergy.PreparationVacuumFullOriginResponse
