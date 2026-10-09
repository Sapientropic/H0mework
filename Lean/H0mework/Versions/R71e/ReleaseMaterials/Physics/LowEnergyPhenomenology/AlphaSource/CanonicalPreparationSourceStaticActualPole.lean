import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticOriginalGreen

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticPoleResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumWholeOrigin
open PreparationVacuumFullOriginResponse PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalZeroRead PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumCurrentSignalOperator SourcePropagationConstrainedPoleReturn
open Filter
open CanonicalGradedSpatialSource
open PreparationVacuumMixedEffective (activeKernel_reflect)
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel fullKernelFrame originalChange originalInverse originalReadback originalRowLift
  sourcePoleCurrentWindow sourceActualCurrentCosource

private theorem frame_support_certificate :
    fastNormalizeTerms (productTerms fullKernelTerms fiveProjectionTerms++negativeTerms fullKernelTerms)=[] ∧
    fastNormalizeTerms (productTerms (projectionTerms activeFlag) fullKernelTerms++negativeTerms fullKernelTerms)=[]:=by decide +kernel

theorem fullKernel_five : fullKernelFrame*fiveProjection=fullKernelFrame:=by
  have h:=normalization_equal _ _ frame_support_certificate.1 (0:Fin 4→ℂ)
  simpa only [productTerms_value,fullKernel_generated,fiveProjection] using h

theorem fullKernel_active : activeProjection*fullKernelFrame=fullKernelFrame:=by
  have h:=normalization_equal _ _ frame_support_certificate.2 (0:Fin 4→ℂ)
  simpa only [productTerms_value,fullKernel_generated,projectionTerms_value,activeProjection] using h

private theorem five_transpose : fiveProjection.transpose=fiveProjection:=by
  have checked : reflectedTerms fiveProjectionTerms=fiveProjectionTerms:=by decide +kernel
  have h:=reflectedTerms_value fiveProjectionTerms (0:Fin 4→ℂ)
  rw [checked,neg_zero] at h
  exact h.symm

theorem fullKernelTranspose_five : fiveProjection*fullKernelFrame.transpose=fullKernelFrame.transpose:=by
  have h:=congrArg Matrix.transpose fullKernel_five
  simpa only [Matrix.transpose_mul,five_transpose] using h

theorem effectiveReader_supported (p : complementRegular) : fiveProjection*effectiveReader p=effectiveReader p:=by
  unfold effectiveReader
  simp only [mul_sub,←mul_assoc,fullKernelTranspose_five]

def staticSourceReader (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  effectiveReader (staticPoint κ)*ᵥstaticActiveForcing κ forcing

theorem staticSourceReader_supported (κ : staticDomain) (forcing : Fin 289→ℂ) :
    fiveProjection*ᵥstaticSourceReader κ forcing=staticSourceReader κ forcing:=by
  rw [staticSourceReader,Matrix.mulVec_mulVec,effectiveReader_supported]

def staticPoleCoefficient (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  nativeEffectiveFrame (staticPoint κ)*ᵥ(staticInverse*ᵥstaticSourceReader κ forcing)

def staticRegularField (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  staticContactField κ forcing+originalChange (staticMomentum κ.val)*ᵥ
    (complementGreen (staticPoint κ)*ᵥstaticActiveForcing κ forcing)

theorem staticNativeField_pole_factor (κ : staticDomain) (forcing : Fin 289→ℂ) :
    (-(κ.val:ℂ)^2) • (staticNativeField κ forcing-staticRegularField κ forcing)=
      nativeEffectiveFrame (staticPoint κ)*ᵥ((normalizedKernel κ)⁻¹*ᵥstaticSourceReader κ forcing):=by
  have nonzero : (-(κ.val:ℂ)^2)≠0:=by
    exact neg_ne_zero.mpr (pow_ne_zero 2 (by exact_mod_cast ne_of_gt κ.property.1))
  have returned:=staticNativeField_schur κ forcing
  have difference : staticNativeField κ forcing-staticRegularField κ forcing=
      (-(κ.val:ℂ)^2)⁻¹ • (nativeEffectiveFrame (staticPoint κ)*ᵥ((normalizedKernel κ)⁻¹*ᵥstaticSourceReader κ forcing)):=by
    rw [returned]
    unfold staticRegularField staticSourceReader
    abel
  rw [difference,smul_smul,mul_inv_cancel₀ nonzero,one_smul]

theorem staticNativeField_pole_price (κ : staticDomain) (forcing : Fin 289→ℂ) :
    ‖(-(κ.val:ℂ)^2) • (staticNativeField κ forcing-staticRegularField κ forcing)-staticPoleCoefficient κ forcing‖ ≤
      ‖nativeEffectiveFrame (staticPoint κ)‖*(2*staticInverseBudget^2*effectiveErrorBudget*κ.val)*‖staticSourceReader κ forcing‖:=by
  have padded : paddedStaticInverse*ᵥstaticSourceReader κ forcing=staticInverse*ᵥstaticSourceReader κ forcing:=by
    rw [paddedStaticInverse,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,staticSourceReader_supported,sub_self,add_zero]
  rw [staticNativeField_pole_factor,staticPoleCoefficient,←padded,←Matrix.mulVec_sub,←Matrix.sub_mulVec]
  calc
    _ ≤ ‖nativeEffectiveFrame (staticPoint κ)‖*‖((normalizedKernel κ)⁻¹-paddedStaticInverse)*ᵥstaticSourceReader κ forcing‖:=Matrix.linfty_opNorm_mulVec _ _
    _ ≤ ‖nativeEffectiveFrame (staticPoint κ)‖*((2*staticInverseBudget^2*effectiveErrorBudget*κ.val)*‖staticSourceReader κ forcing‖):=by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right (normalizedKernel_inverse_delta κ) (norm_nonneg _))
    _= _:=by ring

theorem actual_static_momentum (p : PhysicalMomentum) (κ : ℝ) :
    actualMomentum (sourceAxisLeft p κ) p 0=staticMomentum κ:=by
  rw [actualMomentum,sourceAxis_same_transfer]
  exact sourceAxis_same_Fourier 0 κ

def actualStaticCurrent (q : PhysicalResponsePoint) (p : PhysicalMomentum) (κ : staticDomain)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=actualCurrent q (sourceAxisLeft p κ.val) p left right 0 T

def actualStaticCosource (q : PhysicalResponsePoint) (p : PhysicalMomentum) (κ : staticDomain)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=actualCosource q (sourceAxisLeft p κ.val) p left right 0 T

def actualStaticField (q : PhysicalResponsePoint) (p : PhysicalMomentum) (κ : staticDomain)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=staticNativeField κ (actualStaticCurrent q p κ left right T)

theorem actualStaticCurrent_ward (q : PhysicalResponsePoint) (p : PhysicalMomentum) (κ : staticDomain)
    (left right : RestStateIndex) (T : ℝ) : originalReadback (staticMomentum κ.val)*ᵥactualStaticCurrent q p κ left right T=
      actualStaticCosource q p κ left right T:=by
  have h:=actual_current_ward q (sourceAxisLeft p κ.val) p left right 0 T
  rw [actual_static_momentum] at h
  exact h

theorem actualStaticField_whole (q : PhysicalResponsePoint) (p : PhysicalMomentum) (κ : staticDomain)
    (left right : RestStateIndex) (T : ℝ) : originalJacobi (staticMomentum κ.val)*ᵥactualStaticField q p κ left right T=
      actualStaticCurrent q p κ left right T-originalRowLift (staticMomentum κ.val)*ᵥ(nullProjection*ᵥactualStaticCosource q p κ left right T):=by
  rw [actualStaticField,staticNativeField_whole,actualStaticCurrent_ward]

theorem actualStaticField_schur (q : PhysicalResponsePoint) (p : PhysicalMomentum) (κ : staticDomain)
    (left right : RestStateIndex) (T : ℝ) : actualStaticField q p κ left right T=
      staticContactField κ (actualStaticCurrent q p κ left right T)+
      (-(κ.val:ℂ)^2)⁻¹ • (nativeEffectiveFrame (staticPoint κ)*ᵥ((normalizedKernel κ)⁻¹*ᵥ
        (effectiveReader (staticPoint κ)*ᵥ(activeProjection*ᵥactualStaticCosource q p κ left right T))))+
      originalChange (staticMomentum κ.val)*ᵥ(complementGreen (staticPoint κ)*ᵥ(activeProjection*ᵥactualStaticCosource q p κ left right T)):=by
  rw [actualStaticField,staticNativeField_schur,staticActiveForcing,actualStaticCurrent_ward]

theorem actualStaticField_pole_price (q : PhysicalResponsePoint) (p : PhysicalMomentum) (κ : staticDomain)
    (left right : RestStateIndex) (T : ℝ) :
    ‖(-(κ.val:ℂ)^2) • (actualStaticField q p κ left right T-staticRegularField κ (actualStaticCurrent q p κ left right T))-
      staticPoleCoefficient κ (actualStaticCurrent q p κ left right T)‖ ≤
      ‖nativeEffectiveFrame (staticPoint κ)‖*(2*staticInverseBudget^2*effectiveErrorBudget*κ.val)*
        ‖effectiveReader (staticPoint κ)*ᵥ(activeProjection*ᵥactualStaticCosource q p κ left right T)‖:=by
  have h:=staticNativeField_pole_price κ (actualStaticCurrent q p κ left right T)
  rw [staticSourceReader,staticActiveForcing,actualStaticCurrent_ward] at h
  exact h

def staticApproach : Filter staticDomain:=Filter.comap Subtype.val (𝓝[>] (0:ℝ))

theorem staticApproach_nonempty : staticApproach.NeBot:=by
  apply Filter.NeBot.comap_of_range_mem (inferInstance : (𝓝[>] (0:ℝ)).NeBot)
  have near : ∀ᶠ κ in 𝓝 (0:ℝ),κ<staticRadius:=continuous_id.continuousAt.eventually_lt_const staticRadius_pos
  filter_upwards [self_mem_nhdsWithin,near.filter_mono nhdsWithin_le_nhds] with κ positive small
  exact ⟨⟨κ,positive,small.le⟩,rfl⟩

theorem staticVal_tendsto : Tendsto (Subtype.val : staticDomain→ℝ) staticApproach (𝓝 0):=
  (tendsto_comap : Tendsto (Subtype.val : staticDomain→ℝ) staticApproach (𝓝[>] (0:ℝ))).mono_right nhdsWithin_le_nhds

theorem normalizedInverse_tendsto : Tendsto (fun κ : staticDomain=>(normalizedKernel κ)⁻¹) staticApproach (𝓝 paddedStaticInverse):=by
  have upper : Tendsto (fun κ : staticDomain=>2*staticInverseBudget^2*effectiveErrorBudget*κ.val) staticApproach (𝓝 (0:ℝ)):=by
    simpa only [mul_zero] using tendsto_const_nhds.mul staticVal_tendsto
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _))
    (Eventually.of_forall normalizedKernel_inverse_delta) upper

private theorem sourceMatrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms):=by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix:=by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value;fun_prop
      · exact continuous_const
    exact term.add ih

theorem staticMomentum_tendsto : Tendsto (fun κ : staticDomain=>staticMomentum κ.val) staticApproach (𝓝 0):=by
  have continuous : Continuous staticMomentum:=by unfold staticMomentum;fun_prop
  have zero : staticMomentum 0=0:=by ext i;fin_cases i <;> simp [staticMomentum]
  have h:=continuous.continuousAt.tendsto.comp staticVal_tendsto
  rw [zero] at h
  exact h

private theorem originalChange_continuous : Continuous originalChange:=by
  unfold originalChange
  exact sourceMatrix_continuous originalChangeTerms
private theorem originalReadback_continuous : Continuous originalReadback:=by
  unfold originalReadback
  exact (originalChange_continuous.comp continuous_neg).matrix_transpose
private theorem activeKernel_continuous : Continuous activeKernel:=by
  unfold activeKernel
  exact sourceMatrix_continuous activeTerms
private theorem contactInverse_continuous : Continuous contactInverse:=sourceMatrix_continuous contactInverseTerms

theorem complementGreen_tendsto : Tendsto (fun κ : staticDomain=>complementGreen (staticPoint κ)) staticApproach (𝓝 fullInverse):=by
  have inverseAt : ContinuousAt Ring.inverse (complementKernel 0).det:=by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ origin_determinant
  have inverse:=((continuousAt_matrix_inv (complementKernel 0) inverseAt).tendsto.comp
    (complementKernel_continuous.continuousAt.tendsto.comp staticMomentum_tendsto))
  have result:= ((tendsto_const_nhds (x:=fullComplementProjection)).mul inverse).mul (tendsto_const_nhds (x:=fullComplementProjection))
  rw [←complementGreen_origin]
  exact result

private theorem kernel_left_zero : fullKernelFrame.transpose*activeKernel 0=0:=by
  have h:=congrArg Matrix.transpose fullKernel_origin
  have symmetric : (activeKernel 0).transpose=activeKernel 0:=by
    simpa only [neg_zero] using activeKernel_reflect (0:Fin 4→ℂ)
  simpa only [Matrix.transpose_mul,Matrix.transpose_zero,symmetric] using h

theorem effectiveFrame_tendsto : Tendsto (fun κ : staticDomain=>effectiveFrame (staticPoint κ)) staticApproach (𝓝 fullKernelFrame):=by
  have kernel:=activeKernel_continuous.continuousAt.tendsto.comp staticMomentum_tendsto
  have result:=(tendsto_const_nhds (x:=fullKernelFrame)).sub ((complementGreen_tendsto.mul kernel).mul (tendsto_const_nhds (x:=fullKernelFrame)))
  have zero : fullInverse*activeKernel 0*fullKernelFrame=0:=by rw [mul_assoc,fullKernel_origin,mul_zero]
  simpa only [zero,sub_zero,effectiveFrame,Function.comp_def,staticPoint,controlledPoint] using result

theorem nativeEffectiveFrame_tendsto : Tendsto (fun κ : staticDomain=>nativeEffectiveFrame (staticPoint κ)) staticApproach (𝓝 fullNativeOrigin):=by
  exact (originalChange_continuous.continuousAt.tendsto.comp staticMomentum_tendsto).mul effectiveFrame_tendsto

theorem effectiveReader_tendsto : Tendsto (fun κ : staticDomain=>effectiveReader (staticPoint κ)) staticApproach (𝓝 fullKernelFrame.transpose):=by
  have kernel:=activeKernel_continuous.continuousAt.tendsto.comp staticMomentum_tendsto
  have result:=(tendsto_const_nhds (x:=fullKernelFrame.transpose)).sub (((tendsto_const_nhds (x:=fullKernelFrame.transpose)).mul kernel).mul complementGreen_tendsto)
  simpa only [kernel_left_zero,zero_mul,sub_zero,effectiveReader,Function.comp_def,staticPoint,controlledPoint] using result

private theorem kernelTranspose_active : fullKernelFrame.transpose*activeProjection=fullKernelFrame.transpose:=by
  have h:=congrArg Matrix.transpose fullKernel_active
  simpa only [Matrix.transpose_mul,activeProjection,projectionMatrix,Matrix.diagonal_transpose] using h

private theorem tendsto_mulVec {A : Type*} {f : Filter A}
    {M : A→Matrix (Fin 289) (Fin 289) ℂ} {v : A→Fin 289→ℂ}
    {M0 : Matrix (Fin 289) (Fin 289) ℂ} {v0 : Fin 289→ℂ}
    (hm : Tendsto M f (𝓝 M0)) (hv : Tendsto v f (𝓝 v0)) : Tendsto (fun a=>M a*ᵥv a) f (𝓝 (M0*ᵥv0)):=
  (continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp (hm.prodMk_nhds hv)

theorem staticSourceReader_tendsto (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>staticSourceReader κ forcing) staticApproach (𝓝 (fullNativeOrigin.transpose*ᵥforcing)):=by
  have readback:=originalReadback_continuous.continuousAt.tendsto.comp staticMomentum_tendsto
  have result:=tendsto_mulVec effectiveReader_tendsto
    (tendsto_mulVec (tendsto_const_nhds (x:=activeProjection)) (tendsto_mulVec readback (tendsto_const_nhds (x:=forcing))))
  have returned : fullKernelFrame.transpose*ᵥ(activeProjection*ᵥ(originalReadback 0*ᵥforcing))=fullNativeOrigin.transpose*ᵥforcing:=by
    rw [Matrix.mulVec_mulVec (originalReadback 0*ᵥforcing),kernelTranspose_active]
    simp only [fullNativeOrigin,Matrix.transpose_mul,originalReadback,neg_zero,Matrix.mulVec_mulVec]
  simpa only [staticSourceReader,staticActiveForcing,returned,Function.comp_def] using result

private theorem fullNativeOriginTranspose_supported (forcing : Fin 289→ℂ) :
    fiveProjection*ᵥ(fullNativeOrigin.transpose*ᵥforcing)=fullNativeOrigin.transpose*ᵥforcing:=by
  rw [fullNativeOrigin,Matrix.transpose_mul]
  simp only [Matrix.mulVec_mulVec,←mul_assoc,fullKernelTranspose_five]

def staticResidue (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  fullNativeOrigin*ᵥ(staticInverse*ᵥ(fullNativeOrigin.transpose*ᵥforcing))

theorem staticPoleCoefficient_tendsto (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>staticPoleCoefficient κ forcing) staticApproach (𝓝 (staticResidue forcing)):=
  tendsto_mulVec nativeEffectiveFrame_tendsto (tendsto_mulVec tendsto_const_nhds (staticSourceReader_tendsto forcing))

theorem staticPoleFactor_tendsto (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • (staticNativeField κ forcing-staticRegularField κ forcing))
      staticApproach (𝓝 (staticResidue forcing)):=by
  have result:=tendsto_mulVec nativeEffectiveFrame_tendsto (tendsto_mulVec normalizedInverse_tendsto (staticSourceReader_tendsto forcing))
  have padded : paddedStaticInverse*ᵥ(fullNativeOrigin.transpose*ᵥforcing)=staticInverse*ᵥ(fullNativeOrigin.transpose*ᵥforcing):=by
    rw [paddedStaticInverse,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,fullNativeOriginTranspose_supported,sub_self,add_zero]
  simpa only [staticNativeField_pole_factor,padded,staticResidue] using result

theorem staticRegularField_tendsto (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>staticRegularField κ forcing) staticApproach
      (𝓝 (originalChange 0*ᵥ(contactInverse 0*ᵥ(originalReadback 0*ᵥforcing))+
        originalChange 0*ᵥ(fullInverse*ᵥ(activeProjection*ᵥ(originalReadback 0*ᵥforcing))))):=by
  have change:=originalChange_continuous.continuousAt.tendsto.comp staticMomentum_tendsto
  have contact:=contactInverse_continuous.continuousAt.tendsto.comp staticMomentum_tendsto
  have readback:=originalReadback_continuous.continuousAt.tendsto.comp staticMomentum_tendsto
  exact (tendsto_mulVec change (tendsto_mulVec contact (tendsto_mulVec readback tendsto_const_nhds))).add
    (tendsto_mulVec change (tendsto_mulVec complementGreen_tendsto
      (tendsto_mulVec tendsto_const_nhds (tendsto_mulVec readback tendsto_const_nhds))))

/-- The original, uncleared whole-field Green has this source-generated static pole coefficient on a nonempty physical domain. -/
theorem staticNativeField_residue (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • staticNativeField κ forcing) staticApproach (𝓝 (staticResidue forcing)):=by
  have scalar : Tendsto (fun κ : staticDomain=>-(κ.val:ℂ)^2) staticApproach (𝓝 (0:ℂ)):=by
    simpa only [Function.comp_def,Complex.ofReal_zero,zero_pow (by decide : 2≠0),neg_zero] using (Complex.continuous_ofReal.continuousAt.tendsto.comp staticVal_tendsto).pow 2 |>.neg
  have regular:=scalar.smul (staticRegularField_tendsto forcing)
  have result:=(staticPoleFactor_tendsto forcing).add regular
  have split (κ : staticDomain) : (-(κ.val:ℂ)^2) • (staticNativeField κ forcing-staticRegularField κ forcing)+
      (-(κ.val:ℂ)^2) • staticRegularField κ forcing=(-(κ.val:ℂ)^2) • staticNativeField κ forcing:=by rw [smul_sub];abel
  simpa only [split,zero_smul,add_zero] using result

def actualOriginWeight (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) : ℂ:=
  (3/10:ℂ)*rootTwo*(actualCurrent q pL pR left right lambda T 21-actualCurrent q pL pR left right lambda T 34)

private theorem staticInverse_weight (w : ℂ) : staticInverse*ᵥ(Pi.single 0 w+Pi.single 1 w)=
    Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*w)+Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*w):=by
  norm_num [staticInverse,staticInverseTerms,sourceMatrix,SourceTerm.matrix,Powers.value,coefficientValue,
    Matrix.add_mulVec,Matrix.zero_mulVec,Matrix.single_mulVec,Pi.add_apply,Pi.single_apply,Fin.ext_iff]
  congr 1

/-- The actual held current couples to both canonical source modes with its original spatial current weight. -/
theorem actualCurrent_staticResidue (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    staticResidue (actualCurrent q pL pR left right lambda T)=fullNativeOrigin*ᵥ
      (Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*actualOriginWeight q pL pR left right lambda T)+
       Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*actualOriginWeight q pL pR left right lambda T)):=by
  rw [staticResidue,actual_origin_kernel_read,staticInverse_weight]
  rfl

end LowEnergy.PreparationVacuumStaticPoleResponse
