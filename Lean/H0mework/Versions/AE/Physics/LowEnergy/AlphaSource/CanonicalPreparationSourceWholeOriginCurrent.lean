import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceDualSchur
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceWholeCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWholeOrigin.Dual
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open SourcePropagationNativeActionHessian CanonicalGradedSpatialSource
open PreparationVacuumCurrentSignalOperator PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalFeedback SourcePropagationConstrainedPoleReturn
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalJacobi originalChange originalInverse originalReadback originalRowLift
  activeKernel kernelFrame nativeHessian sourceAxisCosource sourceAxisClearedField

private theorem readback_row (p : Fin 4→ℂ) : originalReadback p*originalRowLift p=1 :=by
  have h:=congrArg Matrix.transpose (original_inverse_change (-p))
  simpa only [Matrix.transpose_mul,Matrix.transpose_one,originalReadback,originalRowLift] using h

private theorem block_commute_certificate :
    selectedRows blockFlag activeTerms=columnTerms blockFlag activeTerms:=by
  have checked : activeTerms.all (fun a=>decide (blockFlag a.row=blockFlag a.column))=true:=by decide +kernel
  unfold selectedRows columnTerms
  apply List.filter_congr
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp checked a ha)

theorem block_source_commutes (p : Fin 4→ℂ) :
    blockProjection*activeKernel p=activeKernel p*blockProjection :=by
  have h:=congrArg (fun terms=>sourceMatrix terms p) block_commute_certificate
  rw [selectedRows_generated,columnTerms_value] at h
  simpa only [blockProjection,activeKernel] using h

theorem block_active : blockProjection*activeProjection=blockProjection :=by
  have contained : ∀i : Fin 289,blockFlag i=true→activeFlag i=true:=by decide +kernel
  unfold blockProjection activeProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : blockFlag i=true
  · simp [h,contained i h]
  · simp [h]

theorem block_null : blockProjection*nullProjection=0 :=by
  have separated : ∀i : Fin 289,blockFlag i=true→nullFlag i=false:=by decide +kernel
  unfold blockProjection nullProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : blockFlag i=true
  · simp [Matrix.diagonal_apply,separated i h]
  · simp [Matrix.diagonal_apply,h]

theorem block_square : blockProjection*blockProjection=blockProjection :=by
  unfold blockProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

def selectorTerms : List SourceTerm := [⟨0,89,⟨0,0,0,0⟩,1⟩,⟨1,95,⟨0,0,0,0⟩,1⟩,⟨2,101,⟨0,0,0,0⟩,1⟩]
def modeSelector : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix selectorTerms 0

def blockCoordinates (field : Fin 289→ℂ) : Fin 289→ℂ:=modeSelector*ᵥfield

def blockComplement (_p : Fin 4→ℂ) (field : Fin 289→ℂ) : Fin 289→ℂ:=field-dualKernelFrame*ᵥblockCoordinates field

private theorem complement_support_certificate :
    fastNormalizeTerms ((projectionTerms blockFlag++negativeTerms (productTerms dualKernelTerms selectorTerms))++
      negativeTerms (productTerms (projectionTerms complementFlag)
        (projectionTerms blockFlag++negativeTerms (productTerms dualKernelTerms selectorTerms))))=[] :=by decide +kernel

theorem blockComplement_supported (p : Fin 4→ℂ) (field : Fin 289→ℂ)
    (inside : blockProjection*ᵥfield=field) : complementProjection*ᵥblockComplement p field=blockComplement p field :=by
  have h:=normalization_equal _ _ complement_support_certificate p
  simp only [sourceMatrix_append,negativeTerms_value,productTerms_value,projectionTerms_value] at h
  have selector : sourceMatrix selectorTerms p=modeSelector:=rfl
  have dual : sourceMatrix dualKernelTerms p=dualKernelFrame:=rfl
  rw [selector,dual] at h
  have returned:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A*ᵥfield) h
  have insideLiteral : projectionMatrix blockFlag*ᵥfield=field:=inside
  simp only [Matrix.add_mulVec,Matrix.neg_mulVec,←Matrix.mulVec_mulVec,insideLiteral] at returned
  simpa only [blockComplement,blockCoordinates,dualKernelFrame,complementProjection,sub_eq_add_neg] using returned.symm

/-- Exact reconstruction of the actual complementary field from the source equation. -/
theorem blockComplement_generated (p : complementRegular) (field forcing : Fin 289→ℂ)
    (inside : blockProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    blockComplement p.val field=complementGreen p*ᵥ(forcing-activeKernel p.val*ᵥ(dualKernelFrame*ᵥblockCoordinates field)) :=by
  apply complement_response p _ _ (blockComplement_supported p.val field inside)
  rw [blockComplement,Matrix.mulVec_sub,equation]

theorem effective_actual_equation (p : complementRegular) (field forcing : Fin 289→ℂ)
    (inside : blockProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    effectiveKernel p*ᵥblockCoordinates field=effectiveReader p*ᵥforcing :=by
  have split : field=dualKernelFrame*ᵥblockCoordinates field+blockComplement p.val field:=by
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
    (inside : blockProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    field=effectiveFrame p*ᵥblockCoordinates field+complementGreen p*ᵥforcing :=by
  have returned:=blockComplement_generated p field forcing inside equation
  rw [blockComplement,Matrix.mulVec_sub] at returned
  rw [effectiveFrame,Matrix.sub_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  linear_combination returned

def actualBlockField (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) : Fin 289→ℂ:=
  blockProjection*ᵥ(originalInverse (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
    sourceAxisClearedField q p momentum left right time T)

def actualBlockForcing (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) : Fin 289→ℂ:=
  originalFieldDenominator (planeMomentum time (Complex.I*(momentum:ℂ))) •
    (blockProjection*ᵥsourceAxisCosource q p momentum left right time T)

theorem actualBlock_source (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) :
    activeKernel (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
      actualBlockField q p momentum left right time T=actualBlockForcing q p momentum left right time T :=by
  let P:=planeMomentum time (Complex.I*(momentum:ℂ))
  have original:=sourceAxis_whole_native q p momentum left right time T
  have projected:=congrArg (fun v=>blockProjection*ᵥ(originalReadback P*ᵥv)) original
  have nullRead (c : Fin 289→ℂ) : blockProjection*ᵥ(originalReadback P*ᵥ(originalRowLift P*ᵥ(nullProjection*ᵥc)))=0 :=by
    rw [Matrix.mulVec_mulVec (nullProjection*ᵥc) (originalReadback P) (originalRowLift P),readback_row,Matrix.one_mulVec,
      Matrix.mulVec_mulVec,block_null,Matrix.zero_mulVec]
  simp only [Matrix.mulVec_smul,Matrix.mulVec_sub] at projected
  rw [sourceAxis_current_ward,nullRead,sub_zero] at projected
  unfold actualBlockField actualBlockForcing
  rw [Matrix.mulVec_mulVec,←block_source_commutes,←Matrix.mulVec_mulVec]
  have factor : blockProjection*originalReadback P*nativeFourierHessian nativeHessian P=
      blockProjection*activeKernel P*originalInverse P :=by
    calc
      _=(blockProjection*activeProjection)*originalReadback P*nativeFourierHessian nativeHessian P:=by rw [block_active]
      _=blockProjection*(activeProjection*originalReadback P*nativeFourierHessian nativeHessian P):=by noncomm_ring
      _= _ :=by rw [original_active_field];noncomm_ring
  simp only [Matrix.mulVec_mulVec] at projected ⊢
  rw [←mul_assoc,factor] at projected
  simpa only [P,mul_assoc] using projected

theorem actualBlock_inside (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) :
    blockProjection*ᵥactualBlockField q p momentum left right time T=actualBlockField q p momentum left right time T :=by
  rw [actualBlockField,Matrix.mulVec_mulVec,block_square]

theorem actual_effective_dynamics (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ)
    (regular : planeMomentum time (Complex.I*(momentum:ℂ))∈complementRegular) :
    effectiveKernel ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
      blockCoordinates (actualBlockField q p momentum left right time T)=
      effectiveReader ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
        actualBlockForcing q p momentum left right time T :=
  effective_actual_equation _ _ _ (actualBlock_inside q p momentum left right time T)
    (actualBlock_source q p momentum left right time T)

theorem actual_complement_return (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ)
    (regular : planeMomentum time (Complex.I*(momentum:ℂ))∈complementRegular) :
    blockComplement (planeMomentum time (Complex.I*(momentum:ℂ))) (actualBlockField q p momentum left right time T)=
      complementGreen ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
        (actualBlockForcing q p momentum left right time T-
          activeKernel (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
            (dualKernelFrame*ᵥ
              blockCoordinates (actualBlockField q p momentum left right time T))) :=
  blockComplement_generated (⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩:complementRegular) _ _ (actualBlock_inside q p momentum left right time T)
    (actualBlock_source q p momentum left right time T)

theorem actual_native_reconstruction (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ)
    (regular : planeMomentum time (Complex.I*(momentum:ℂ))∈complementRegular) :
    originalChange (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥactualBlockField q p momentum left right time T=
      nativeEffectiveFrame ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
        blockCoordinates (actualBlockField q p momentum left right time T)+
      originalChange (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
        (complementGreen ⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩*ᵥ
          actualBlockForcing q p momentum left right time T) :=by
  have reconstructed:=effective_field_reconstruction
    (⟨planeMomentum time (Complex.I*(momentum:ℂ)),regular⟩:complementRegular) _ _
    (actualBlock_inside q p momentum left right time T) (actualBlock_source q p momentum left right time T)
  have returned:=congrArg (fun v=>originalChange (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥv) reconstructed
  simpa only [Matrix.mulVec_add,Matrix.mulVec_mulVec,nativeEffectiveFrame] using returned


end LowEnergy.PreparationVacuumWholeOrigin.Dual

namespace LowEnergy.PreparationVacuumWholeOrigin
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open SourcePropagationNativeActionHessian
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalZeroRead PreparationVacuumPhysicalNumberOneRead PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalPoleHalfResponse SourcePropagationConstrainedPoleReturn
open scoped Matrix BigOperators

def wholeContinuation (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  originalChange p*(wholeActiveOriginFrame+wholeNullOriginFrame)

theorem wholeContinuation_origin : wholeContinuation 0=wholeOriginFrame:=whole_origin_reconstruction

theorem wholeContinuation_read (p : Fin 4→ℂ) :
    (wholeContinuation (-p)).transpose=
      (wholeActiveOriginFrame+wholeNullOriginFrame).transpose*originalReadback p:=by
  rw [wholeContinuation,Matrix.transpose_mul,originalReadback]

private theorem whole_active_certificate :
    fastNormalizeTerms (productTerms (projectionTerms activeFlag) wholeActiveOriginTerms++negativeTerms wholeActiveOriginTerms)=[]:=by decide +kernel
private theorem whole_null_certificate :
    fastNormalizeTerms (productTerms (projectionTerms nullFlag) wholeNullOriginTerms++negativeTerms wholeNullOriginTerms)=[]:=by decide +kernel

theorem whole_active_supported : activeProjection*wholeActiveOriginFrame=wholeActiveOriginFrame:=by
  have h:=normalization_equal _ _ whole_active_certificate (0:Fin 4→ℂ)
  simpa only [productTerms_value,projectionTerms_value,activeProjection,wholeActiveOriginFrame] using h

theorem whole_null_supported : nullProjection*wholeNullOriginFrame=wholeNullOriginFrame:=by
  have h:=normalization_equal _ _ whole_null_certificate (0:Fin 4→ℂ)
  simpa only [productTerms_value,projectionTerms_value,nullProjection,wholeNullOriginFrame] using h

theorem wholeContinuation_actual_source (p : Fin 4→ℂ) :
    nativeFourierHessian nativeHessian p*wholeContinuation p=
      originalRowLift p*(activeKernel p*wholeActiveOriginFrame):=by
  rw [nativeActionFourierHessian_original,wholeContinuation,←mul_assoc,mul_add]
  have active : (originalJacobi p*originalChange p)*wholeActiveOriginFrame=
      originalRowLift p*(activeKernel p*wholeActiveOriginFrame):=by
    calc
      _=(originalJacobi p*originalChange p)*(activeProjection*wholeActiveOriginFrame):=by rw [whole_active_supported]
      _= _ :=by rw [←mul_assoc,original_active_intertwiner,mul_assoc]
  have null : (originalJacobi p*originalChange p)*wholeNullOriginFrame=0:=by
    calc
      _=(originalJacobi p*originalChange p)*(nullProjection*wholeNullOriginFrame):=by rw [whole_null_supported]
      _=0:=by rw [←mul_assoc,original_null_intertwiner,zero_mul]
  rw [active,null,add_zero]

/-- All five source paths read the same actual two-sector quantum current, including their null-coordinate responsibility. -/
theorem whole_current_twoSectors (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    (wholeContinuation (-(fullMomentum spatial lambda))).transpose*ᵥ
      (sourcePrincipalWindow q pL pR left right lambda T 0+sourcePrincipalWindow q pL pR left right lambda T 1)=
      (wholeActiveOriginFrame+wholeNullOriginFrame).transpose*ᵥ
        sourceActualCurrentCosource q pL pR left right spatial lambda T:=by
  rw [wholeContinuation_read,←Matrix.mulVec_mulVec,sourceActualWindow_twoSectors_ward]

theorem whole_current_null_retained (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    (wholeContinuation (-(fullMomentum spatial lambda))).transpose*ᵥ
      sourcePoleCurrentWindow q pL pR left right lambda T=
      wholeActiveOriginFrame.transpose*ᵥsourceActualCurrentCosource q pL pR left right spatial lambda T+
      wholeNullOriginFrame.transpose*ᵥsourceActualCurrentCosource q pL pR left right spatial lambda T:=by
  rw [sourceActualWindow_twoSectors,whole_current_twoSectors,Matrix.transpose_add,Matrix.add_mulVec]

theorem dual_actual_forcing_twoSectors (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T : ℝ) :
    Dual.actualBlockForcing q p momentum left right time T=
      originalFieldDenominator (planeMomentum time (Complex.I*(momentum:ℂ))) •
        (Dual.blockProjection*ᵥ(originalReadback (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
          (sourcePrincipalWindow q (sourceAxisLeft p momentum) p left right time T 0+
            sourcePrincipalWindow q (sourceAxisLeft p momentum) p left right time T 1))) :=by
  unfold Dual.actualBlockForcing
  rw [←sourceAxis_current_ward]
  unfold sourceAxisCurrent
  rw [sourceActualWindow_twoSectors]


theorem wholeNull_coordinates (current : Fin 289→ℂ) :
    wholeNullOriginFrame.transpose*ᵥcurrent=
      Pi.single 1 (-2*current 114)+Pi.single 3 (-2*current 114)+Pi.single 4 (current 114):=by
  simp only [wholeNullOriginFrame,wholeNullOriginTerms,sourceMatrix,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    SourceTerm.matrix,Matrix.transpose_add,Matrix.transpose_single,Matrix.transpose_zero,
    Matrix.add_mulVec,Matrix.zero_mulVec,Matrix.single_mulVec,Powers.value,coefficientValue]
  norm_num [Pi.single,add_assoc]

theorem whole_current_null_value (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    wholeNullOriginFrame.transpose*ᵥsourceActualCurrentCosource q pL pR left right spatial lambda T=
      Pi.single 1 (-2*sourceActualCurrentCosource q pL pR left right spatial lambda T 114)+
      Pi.single 3 (-2*sourceActualCurrentCosource q pL pR left right spatial lambda T 114)+
      Pi.single 4 (sourceActualCurrentCosource q pL pR left right spatial lambda T 114):=
  wholeNull_coordinates _


end LowEnergy.PreparationVacuumWholeOrigin
