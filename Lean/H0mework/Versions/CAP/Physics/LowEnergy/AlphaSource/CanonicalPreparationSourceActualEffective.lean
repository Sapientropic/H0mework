import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMixedSchur

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedEffective
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal
open SourcePropagationNativeActionHessian CanonicalGradedSpatialSource
open PreparationVacuumCurrentSignalOperator PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalFeedback SourcePropagationConstrainedPoleReturn
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalJacobi originalChange originalInverse originalReadback originalRowLift
  activeKernel kernelFrame nativeHessian sourceAxisCosource sourceAxisClearedField

private theorem readback_row (p : Fin 4→ℂ) : originalReadback p*originalRowLift p=1 :=by
  rw [originalReadback,originalRowLift,←Matrix.transpose_mul,original_inverse_change,Matrix.transpose_one]

private theorem active_transpose : activeProjection.transpose=activeProjection :=by
  simp [activeProjection,projectionMatrix]

def canonicalAction (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=
  originalReadback p*originalJacobi p*originalChange p

private theorem canonicalAction_active (p : Fin 4→ℂ) : canonicalAction p*activeProjection=activeKernel p :=by
  calc
    _=originalReadback p*(originalJacobi p*originalChange p*activeProjection):=by unfold canonicalAction;noncomm_ring
    _=originalReadback p*(originalRowLift p*activeKernel p):=by rw [original_active_intertwiner]
    _=activeKernel p:=by rw [←mul_assoc,readback_row,one_mul]

private theorem canonicalAction_reflect (p : Fin 4→ℂ) : (canonicalAction (-p)).transpose=canonicalAction p :=by
  simp only [canonicalAction,originalReadback,Matrix.transpose_mul,neg_neg,Matrix.transpose_transpose,
    original_jacobi_reciprocity,mul_assoc]

private theorem canonicalAction_active_left (p : Fin 4→ℂ) : activeProjection*canonicalAction p=(activeKernel (-p)).transpose :=by
  have h:=congrArg Matrix.transpose (canonicalAction_active (-p))
  simpa only [Matrix.transpose_mul,active_transpose,canonicalAction_reflect] using h

theorem activeKernel_reflect (p : Fin 4→ℂ) : (activeKernel (-p)).transpose=activeKernel p :=by
  have support:=congrArg Matrix.transpose (original_active_support (-p))
  rw [Matrix.transpose_mul,active_transpose] at support
  calc
    _=(activeKernel (-p)).transpose*activeProjection:=support.symm
    _=(activeProjection*canonicalAction p)*activeProjection:=by rw [canonicalAction_active_left]
    _=activeProjection*activeKernel p:=by rw [mul_assoc,canonicalAction_active]
    _=activeKernel p:=original_active_support p

theorem original_active_field (p : Fin 4→ℂ) :
    activeProjection*originalReadback p*nativeFourierHessian nativeHessian p=activeKernel p*originalInverse p :=by
  rw [nativeActionFourierHessian_original]
  calc
    _=(activeProjection*originalReadback p*originalJacobi p)*(originalChange p*originalInverse p):=by rw [original_change_inverse,mul_one]
    _=(activeProjection*canonicalAction p)*originalInverse p:=by unfold canonicalAction;noncomm_ring
    _=activeKernel p*originalInverse p:=by rw [canonicalAction_active_left,activeKernel_reflect]

private theorem block_commute_certificate :
    fastNormalizeTerms (productTerms (projectionTerms blockFlag) (planeTerms activeTerms)++
      negativeTerms (productTerms (planeTerms activeTerms) (projectionTerms blockFlag)))=[] :=by decide +kernel

theorem block_source_commutes (time space : ℂ) :
    blockProjection*activeKernel (planeMomentum time space)=activeKernel (planeMomentum time space)*blockProjection :=by
  have h:=normalization_equal _ _ block_commute_certificate (planeMomentum time space)
  rw [productTerms_value,productTerms_value,projectionTerms_value,planeTerms_generated] at h
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

def selectorTerms : List SourceTerm := [⟨0,83,⟨0,0,0,0⟩,1⟩,⟨1,85,⟨0,0,0,0⟩,1⟩]
def modeSelector : Matrix (Fin 289) (Fin 289) ℂ:=sourceMatrix selectorTerms 0

def blockCoordinates (field : Fin 289→ℂ) : Fin 289→ℂ:=modeSelector*ᵥfield

def blockComplement (p : Fin 4→ℂ) (field : Fin 289→ℂ) : Fin 289→ℂ:=field-kernelFrame p*ᵥblockCoordinates field

private theorem complement_support_certificate :
    fastNormalizeTerms ((projectionTerms blockFlag++negativeTerms (productTerms kernelTerms selectorTerms))++
      negativeTerms (productTerms (projectionTerms complementFlag)
        (projectionTerms blockFlag++negativeTerms (productTerms kernelTerms selectorTerms))))=[] :=by decide +kernel

theorem blockComplement_supported (p : Fin 4→ℂ) (field : Fin 289→ℂ)
    (inside : blockProjection*ᵥfield=field) : complementProjection*ᵥblockComplement p field=blockComplement p field :=by
  have h:=normalization_equal _ _ complement_support_certificate p
  simp only [sourceMatrix_append,negativeTerms_value,productTerms_value,projectionTerms_value] at h
  have selector : sourceMatrix selectorTerms p=modeSelector:=rfl
  rw [selector] at h
  have returned:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A*ᵥfield) h
  have insideLiteral : projectionMatrix blockFlag*ᵥfield=field:=inside
  simp only [Matrix.add_mulVec,Matrix.neg_mulVec,←Matrix.mulVec_mulVec,insideLiteral] at returned
  simpa only [blockComplement,blockCoordinates,kernelFrame,complementProjection,sub_eq_add_neg] using returned.symm

/-- Exact reconstruction of the actual complementary field from the source equation. -/
theorem blockComplement_generated (p : complementRegular) (field forcing : Fin 289→ℂ)
    (inside : blockProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    blockComplement p.val field=complementGreen p*ᵥ(forcing-activeKernel p.val*ᵥ(kernelFrame p.val*ᵥblockCoordinates field)) :=by
  apply complement_response p _ _ (blockComplement_supported p.val field inside)
  rw [blockComplement,Matrix.mulVec_sub,equation]

theorem effective_actual_equation (p : complementRegular) (field forcing : Fin 289→ℂ)
    (inside : blockProjection*ᵥfield=field) (equation : activeKernel p.val*ᵥfield=forcing) :
    effectiveKernel p*ᵥblockCoordinates field=effectiveReader p*ᵥforcing :=by
  have split : field=kernelFrame p.val*ᵥblockCoordinates field+blockComplement p.val field:=by
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
            (kernelFrame (planeMomentum time (Complex.I*(momentum:ℂ)))*ᵥ
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

end LowEnergy.PreparationVacuumMixedEffective
