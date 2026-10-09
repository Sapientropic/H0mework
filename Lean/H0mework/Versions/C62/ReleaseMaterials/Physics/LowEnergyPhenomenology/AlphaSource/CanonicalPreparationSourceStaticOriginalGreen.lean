import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticPoleDomain

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticPoleResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal
open PreparationVacuumWholeOrigin PreparationVacuumFullOriginResponse SourcePropagationConstrainedPoleReturn
open PreparationVacuumMixedEffective (original_active_field)
open SourcePropagationNativeActionHessian
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel fullKernelFrame originalInverse originalReadback originalRowLift

private theorem selector_support_certificate :
    fastNormalizeTerms (productTerms fiveProjectionTerms selectorTerms++negativeTerms selectorTerms)=[]:=by decide +kernel

theorem blockCoordinates_supported (field : Fin 289→ℂ) : fiveProjection*ᵥblockCoordinates field=blockCoordinates field:=by
  have h:=normalization_equal _ _ selector_support_certificate (0:Fin 4→ℂ)
  have matrices : fiveProjection*modeSelector=modeSelector:=by
    simpa only [productTerms_value,fiveProjection,modeSelector] using h
  rw [blockCoordinates,Matrix.mulVec_mulVec,matrices]

theorem source_static_kernel_zero (κ : staticDomain) (field : Fin 289→ℂ)
    (inside : activeProjection*ᵥfield=field) (kernel : activeKernel (staticMomentum κ.val)*ᵥfield=0) : field=0:=by
  have reduced:=effective_actual_equation (staticPoint κ) field 0 inside kernel
  rw [Matrix.mulVec_zero] at reduced
  have padded : normalizedKernel κ*ᵥblockCoordinates field=0:=by
    rw [normalizedKernel,Matrix.add_mulVec,Matrix.smul_mulVec,reduced,smul_zero,
      Matrix.sub_mulVec,Matrix.one_mulVec,blockCoordinates_supported,sub_self,add_zero]
  have coordinates : blockCoordinates field=0:=by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr (normalizedKernel_isUnit κ))
    simpa only [Matrix.mulVec_zero] using padded
  have reconstructed:=effective_field_reconstruction (staticPoint κ) field 0 inside kernel
  simpa only [coordinates,Matrix.mulVec_zero,add_zero] using reconstructed

theorem source_static_extended_kernel_zero (κ : staticDomain) (field : Fin 289→ℂ)
    (kernel : extendedKernel (staticMomentum κ.val)*ᵥfield=0) : field=0:=by
  have projected:=congrArg (fun v=>activeProjection*ᵥv) kernel
  rw [Matrix.mulVec_mulVec,original_active_extended,Matrix.mulVec_zero] at projected
  have inside : activeProjection*ᵥ(activeProjection*ᵥfield)=activeProjection*ᵥfield:=by
    rw [Matrix.mulVec_mulVec,active_square]
  have zero : activeProjection*ᵥfield=0:=by
    apply source_static_kernel_zero κ _ inside
    rw [Matrix.mulVec_mulVec,activeKernel_right]
    exact projected
  rw [extendedKernel,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,projected,zero,sub_zero,zero_add] at kernel
  exact kernel

theorem source_static_regular (κ : staticDomain) : staticMomentum κ.val∈regularSource:=by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro left right same
  apply sub_eq_zero.mp
  apply source_static_extended_kernel_zero κ
  rw [Matrix.mulVec_sub,same,sub_self]

def staticRegularPoint (κ : staticDomain) : regularSource:=⟨staticMomentum κ.val,source_static_regular κ⟩

theorem staticDenominator_nonzero (κ : staticDomain) : originalFieldDenominator (staticMomentum κ.val)≠0:=
  isUnit_iff_ne_zero.mp (source_static_regular κ)

theorem staticDomain_nonempty_regular : ∃κ : ℝ,0<κ ∧ κ ≤ staticRadius ∧ originalFieldDenominator (staticMomentum κ)≠0:=
  ⟨staticWitness.val,staticWitness.property.1,staticWitness.property.2,staticDenominator_nonzero staticWitness⟩

def staticNativeField (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=sourceField (staticRegularPoint κ) forcing

def staticActiveField (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  activeProjection*ᵥ(originalInverse (staticMomentum κ.val)*ᵥstaticNativeField κ forcing)

def staticActiveForcing (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  activeProjection*ᵥ(originalReadback (staticMomentum κ.val)*ᵥforcing)

theorem staticNativeField_uncleared (κ : staticDomain) (forcing : Fin 289→ℂ) :
    originalFieldDenominator (staticMomentum κ.val) • staticNativeField κ forcing=
      originalClearedGreen (staticMomentum κ.val)*ᵥforcing:=by
  have h:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥforcing) (originalGreen_denominator (staticRegularPoint κ))
  simpa only [Matrix.smul_mulVec,staticNativeField,sourceField,staticRegularPoint] using h

theorem staticNativeField_whole (κ : staticDomain) (forcing : Fin 289→ℂ) :
    originalJacobi (staticMomentum κ.val)*ᵥstaticNativeField κ forcing=
      forcing-originalRowLift (staticMomentum κ.val)*ᵥ(nullProjection*ᵥ(originalReadback (staticMomentum κ.val)*ᵥforcing)):=
  original_forced_field (staticRegularPoint κ) forcing

private theorem readback_row (p : Fin 4→ℂ) : originalReadback p*originalRowLift p=1:=by
  have h:=congrArg Matrix.transpose (original_inverse_change (-p))
  simpa only [Matrix.transpose_mul,Matrix.transpose_one,originalReadback,originalRowLift] using h

theorem staticActiveField_inside (κ : staticDomain) (forcing : Fin 289→ℂ) :
    activeProjection*ᵥstaticActiveField κ forcing=staticActiveField κ forcing:=by
  rw [staticActiveField,Matrix.mulVec_mulVec,active_square]

theorem staticActiveField_source (κ : staticDomain) (forcing : Fin 289→ℂ) :
    activeKernel (staticMomentum κ.val)*ᵥstaticActiveField κ forcing=staticActiveForcing κ forcing:=by
  let p:=staticMomentum κ.val
  have projected:=congrArg (fun v=>activeProjection*ᵥ(originalReadback p*ᵥv)) (staticNativeField_whole κ forcing)
  have nullRead (c : Fin 289→ℂ) : activeProjection*ᵥ(originalReadback p*ᵥ(originalRowLift p*ᵥ(nullProjection*ᵥc)))=0:=by
    rw [Matrix.mulVec_mulVec (nullProjection*ᵥc) (originalReadback p) (originalRowLift p),readback_row,Matrix.one_mulVec,
      Matrix.mulVec_mulVec,active_null,Matrix.zero_mulVec]
  simp only [Matrix.mulVec_sub] at projected
  rw [nullRead,sub_zero] at projected
  unfold staticActiveField staticActiveForcing
  rw [Matrix.mulVec_mulVec,activeKernel_right]
  simp only [Matrix.mulVec_mulVec] at projected ⊢
  rw [←mul_assoc] at projected
  have converted : activeProjection*originalReadback p*originalJacobi p=activeKernel p*originalInverse p:=by
    simpa only [nativeActionFourierHessian_original] using original_active_field p
  rw [converted] at projected
  simpa only [p,mul_assoc] using projected

theorem static_coordinates_return (κ : staticDomain) (forcing : Fin 289→ℂ) :
    blockCoordinates (staticActiveField κ forcing)=
      (-(κ.val:ℂ)^2)⁻¹ • ((normalizedKernel κ)⁻¹*ᵥ(effectiveReader (staticPoint κ)*ᵥstaticActiveForcing κ forcing)):=by
  have reduced:=effective_actual_equation (staticPoint κ) _ _ (staticActiveField_inside κ forcing) (staticActiveField_source κ forcing)
  have padded : normalizedKernel κ*ᵥblockCoordinates (staticActiveField κ forcing)=
      (-(κ.val:ℂ)^2)⁻¹ • (effectiveReader (staticPoint κ)*ᵥstaticActiveForcing κ forcing):=by
    rw [normalizedKernel,Matrix.add_mulVec,Matrix.smul_mulVec,reduced,Matrix.sub_mulVec,
      Matrix.one_mulVec,blockCoordinates_supported,sub_self,add_zero]
  have returned:=congrArg (fun v=>(normalizedKernel κ)⁻¹*ᵥv) padded
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (normalizedKernel_isUnit κ)),
    Matrix.one_mulVec,Matrix.mulVec_smul] at returned
  exact returned

theorem static_field_schur (κ : staticDomain) (forcing : Fin 289→ℂ) : staticActiveField κ forcing=
    (-(κ.val:ℂ)^2)⁻¹ • (effectiveFrame (staticPoint κ)*ᵥ((normalizedKernel κ)⁻¹*ᵥ
      (effectiveReader (staticPoint κ)*ᵥstaticActiveForcing κ forcing)))+
      complementGreen (staticPoint κ)*ᵥstaticActiveForcing κ forcing:=by
  have h:=effective_field_reconstruction (staticPoint κ) _ _ (staticActiveField_inside κ forcing) (staticActiveField_source κ forcing)
  rw [static_coordinates_return,Matrix.mulVec_smul] at h
  exact h

private theorem active_contact_certificate :
    fastNormalizeTerms (productTerms (projectionTerms activeFlag) contactInverseTerms)=[]:=by decide +kernel

theorem active_contact_inverse_zero (p : Fin 4→ℂ) : activeProjection*contactInverse p=0:=by
  have h:=fastNormalizeTerms_value (productTerms (projectionTerms activeFlag) contactInverseTerms) p
  rw [active_contact_certificate,sourceMatrix_nil] at h
  simpa only [productTerms_value,projectionTerms_value,activeProjection,contactInverse] using h.symm

def staticContactField (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  originalChange (staticMomentum κ.val)*ᵥ(contactInverse (staticMomentum κ.val)*ᵥ
    (originalReadback (staticMomentum κ.val)*ᵥforcing))

theorem staticNativeField_contact_active (κ : staticDomain) (forcing : Fin 289→ℂ) :
    staticNativeField κ forcing=staticContactField κ forcing+
      originalChange (staticMomentum κ.val)*ᵥstaticActiveField κ forcing:=by
  let p:=staticMomentum κ.val
  have inverseRead : originalInverse p*ᵥstaticNativeField κ forcing=
      (contactInverse p+activeProjection*(extendedKernel p)⁻¹)*ᵥ(originalReadback p*ᵥforcing):=by
    change originalInverse p*ᵥ((originalChange p*(contactInverse p+activeProjection*(extendedKernel p)⁻¹)*originalReadback p)*ᵥforcing)=_
    simp only [Matrix.mulVec_mulVec]
    rw [←mul_assoc,←mul_assoc,original_inverse_change,one_mul]
  have activeRead : staticActiveField κ forcing=
      (activeProjection*(extendedKernel p)⁻¹)*ᵥ(originalReadback p*ᵥforcing):=by
    change activeProjection*ᵥ(originalInverse p*ᵥstaticNativeField κ forcing)=_
    rw [inverseRead,Matrix.mulVec_mulVec,mul_add,active_contact_inverse_zero,zero_add,
      ←mul_assoc,active_square]
  rw [activeRead]
  change (originalChange p*(contactInverse p+activeProjection*(extendedKernel p)⁻¹)*originalReadback p)*ᵥforcing=
    originalChange p*ᵥ(contactInverse p*ᵥ(originalReadback p*ᵥforcing))+
      originalChange p*ᵥ((activeProjection*(extendedKernel p)⁻¹)*ᵥ(originalReadback p*ᵥforcing))
  simp only [mul_add,add_mul,Matrix.add_mulVec,Matrix.mulVec_mulVec,mul_assoc]

theorem staticNativeField_schur (κ : staticDomain) (forcing : Fin 289→ℂ) : staticNativeField κ forcing=
    staticContactField κ forcing+
      (-(κ.val:ℂ)^2)⁻¹ • (nativeEffectiveFrame (staticPoint κ)*ᵥ((normalizedKernel κ)⁻¹*ᵥ
        (effectiveReader (staticPoint κ)*ᵥstaticActiveForcing κ forcing)))+
      originalChange (staticMomentum κ.val)*ᵥ(complementGreen (staticPoint κ)*ᵥstaticActiveForcing κ forcing):=by
  rw [staticNativeField_contact_active,static_field_schur,Matrix.mulVec_add,Matrix.mulVec_smul]
  simp only [nativeEffectiveFrame,←Matrix.mulVec_mulVec]
  change staticContactField κ forcing+(_+_)=staticContactField κ forcing+_+_
  dsimp only [staticPoint,controlledPoint]
  abel

end LowEnergy.PreparationVacuumStaticPoleResponse
