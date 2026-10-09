import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticSpatialTensor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumStaticPoleResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumWholeOrigin PreparationVacuumFullOriginResponse PreparationVacuumMixedPrincipal
open SourcePropagationConstrainedPoleReturn
open SourcePropagationNativeActionHessian CanonicalGradedSpatialSource
open PreparationVacuumPhysicalCharacteristic Electromagnetic.CanonicalCoframe
open PreparationPhysicalDressedPhotonCouplingReturn PreparationVacuumFullFieldRiesz
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open GaussComposite GaussComposite.SourceGraph CanonicalPhysicalYResolvent GaussCoreHilbert
open GaussUnitaryHistory (Index)
open MeasureTheory Filter Set
open scoped Matrix BigOperators Topology InnerProductSpace Matrix.Norms.Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] activeKernel fullKernelFrame originalInverse originalReadback originalRowLift

theorem sourceSpatialSourceStaticKernelZero (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (field : Fin 289→ℂ)
    (inside : activeProjection*ᵥfield=field) (kernel : activeKernel (sourceStaticSpatialMomentum n κ.val)*ᵥfield=0) : field=0:=by
  have reduced:=effective_actual_equation (sourceStaticSpatialPoint n unit κ) field 0 inside kernel
  rw [Matrix.mulVec_zero] at reduced
  have padded : sourceStaticSpatialKernel n unit κ*ᵥblockCoordinates field=0:=by
    rw [sourceStaticSpatialKernel,Matrix.add_mulVec,Matrix.smul_mulVec,reduced,smul_zero,
      Matrix.sub_mulVec,Matrix.one_mulVec,blockCoordinates_supported,sub_self,add_zero]
  have coordinates : blockCoordinates field=0:=by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr (sourceStaticSpatialKernel_isUnit n unit κ))
    simpa only [Matrix.mulVec_zero] using padded
  have reconstructed:=effective_field_reconstruction (sourceStaticSpatialPoint n unit κ) field 0 inside kernel
  simpa only [coordinates,Matrix.mulVec_zero,add_zero] using reconstructed

theorem sourceSpatialSourceStaticExtendedKernelZero (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (field : Fin 289→ℂ)
    (kernel : extendedKernel (sourceStaticSpatialMomentum n κ.val)*ᵥfield=0) : field=0:=by
  have projected:=congrArg (fun v=>activeProjection*ᵥv) kernel
  rw [Matrix.mulVec_mulVec,original_active_extended,Matrix.mulVec_zero] at projected
  have inside : activeProjection*ᵥ(activeProjection*ᵥfield)=activeProjection*ᵥfield:=by
    rw [Matrix.mulVec_mulVec,active_square]
  have zero : activeProjection*ᵥfield=0:=by
    apply sourceSpatialSourceStaticKernelZero n unit κ _ inside
    rw [Matrix.mulVec_mulVec,activeKernel_right]
    exact projected
  rw [extendedKernel,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,projected,zero,sub_zero,zero_add] at kernel
  exact kernel

theorem sourceSpatialSourceStaticRegular (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) : sourceStaticSpatialMomentum n κ.val∈regularSource:=by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro left right same
  apply sub_eq_zero.mp
  apply sourceSpatialSourceStaticExtendedKernelZero n unit κ
  rw [Matrix.mulVec_sub,same,sub_self]

def sourceSpatialStaticRegularPoint (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) : regularSource:=⟨sourceStaticSpatialMomentum n κ.val,sourceSpatialSourceStaticRegular n unit κ⟩

theorem sourceSpatialStaticDenominatorNonzero (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) : originalFieldDenominator (sourceStaticSpatialMomentum n κ.val)≠0:=
  isUnit_iff_ne_zero.mp (sourceSpatialSourceStaticRegular n unit κ)

def sourceSpatialStaticNativeField (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=sourceField (sourceSpatialStaticRegularPoint n unit κ) forcing

def sourceSpatialStaticActiveField (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  activeProjection*ᵥ(originalInverse (sourceStaticSpatialMomentum n κ.val)*ᵥsourceSpatialStaticNativeField n unit κ forcing)

def sourceSpatialStaticActiveForcing (n : PhysicalMomentum) (_unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  activeProjection*ᵥ(originalReadback (sourceStaticSpatialMomentum n κ.val)*ᵥforcing)

theorem sourceSpatialStaticNativeFieldUncleared (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) :
    originalFieldDenominator (sourceStaticSpatialMomentum n κ.val) • sourceSpatialStaticNativeField n unit κ forcing=
      originalClearedGreen (sourceStaticSpatialMomentum n κ.val)*ᵥforcing:=by
  have h:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥforcing) (originalGreen_denominator (sourceSpatialStaticRegularPoint n unit κ))
  simpa only [Matrix.smul_mulVec,sourceSpatialStaticNativeField,sourceField,sourceSpatialStaticRegularPoint] using h

theorem sourceSpatialStaticNativeFieldWhole (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) :
    originalJacobi (sourceStaticSpatialMomentum n κ.val)*ᵥsourceSpatialStaticNativeField n unit κ forcing=
      forcing-originalRowLift (sourceStaticSpatialMomentum n κ.val)*ᵥ(nullProjection*ᵥ(originalReadback (sourceStaticSpatialMomentum n κ.val)*ᵥforcing)):=
  original_forced_field (sourceSpatialStaticRegularPoint n unit κ) forcing

private theorem readback_row (p : Fin 4→ℂ) : originalReadback p*originalRowLift p=1:=by
  have h:=congrArg Matrix.transpose (original_inverse_change (-p))
  simpa only [Matrix.transpose_mul,Matrix.transpose_one,originalReadback,originalRowLift] using h

theorem sourceSpatialStaticActiveFieldInside (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) :
    activeProjection*ᵥsourceSpatialStaticActiveField n unit κ forcing=sourceSpatialStaticActiveField n unit κ forcing:=by
  rw [sourceSpatialStaticActiveField,Matrix.mulVec_mulVec,active_square]

theorem sourceSpatialStaticActiveFieldSource (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) :
    activeKernel (sourceStaticSpatialMomentum n κ.val)*ᵥsourceSpatialStaticActiveField n unit κ forcing=sourceSpatialStaticActiveForcing n unit κ forcing:=by
  let p:=sourceStaticSpatialMomentum n κ.val
  have projected:=congrArg (fun v=>activeProjection*ᵥ(originalReadback p*ᵥv)) (sourceSpatialStaticNativeFieldWhole n unit κ forcing)
  have nullRead (c : Fin 289→ℂ) : activeProjection*ᵥ(originalReadback p*ᵥ(originalRowLift p*ᵥ(nullProjection*ᵥc)))=0:=by
    rw [Matrix.mulVec_mulVec (nullProjection*ᵥc) (originalReadback p) (originalRowLift p),readback_row,Matrix.one_mulVec,
      Matrix.mulVec_mulVec,active_null,Matrix.zero_mulVec]
  simp only [Matrix.mulVec_sub] at projected
  rw [nullRead,sub_zero] at projected
  unfold sourceSpatialStaticActiveField sourceSpatialStaticActiveForcing
  rw [Matrix.mulVec_mulVec,activeKernel_right]
  simp only [Matrix.mulVec_mulVec] at projected ⊢
  rw [←mul_assoc] at projected
  have converted : activeProjection*originalReadback p*originalJacobi p=activeKernel p*originalInverse p:=by
    simpa only [nativeActionFourierHessian_original] using PreparationVacuumMixedEffective.original_active_field p
  rw [converted] at projected
  simpa only [p,mul_assoc] using projected

theorem sourceSpatialStaticCoordinatesReturn (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) :
    blockCoordinates (sourceSpatialStaticActiveField n unit κ forcing)=
      (-(κ.val:ℂ)^2)⁻¹ • ((sourceStaticSpatialKernel n unit κ)⁻¹*ᵥ(effectiveReader (sourceStaticSpatialPoint n unit κ)*ᵥsourceSpatialStaticActiveForcing n unit κ forcing)):=by
  have reduced:=effective_actual_equation (sourceStaticSpatialPoint n unit κ) _ _ (sourceSpatialStaticActiveFieldInside n unit κ forcing) (sourceSpatialStaticActiveFieldSource n unit κ forcing)
  have padded : sourceStaticSpatialKernel n unit κ*ᵥblockCoordinates (sourceSpatialStaticActiveField n unit κ forcing)=
      (-(κ.val:ℂ)^2)⁻¹ • (effectiveReader (sourceStaticSpatialPoint n unit κ)*ᵥsourceSpatialStaticActiveForcing n unit κ forcing):=by
    rw [sourceStaticSpatialKernel,Matrix.add_mulVec,Matrix.smul_mulVec,reduced,Matrix.sub_mulVec,
      Matrix.one_mulVec,blockCoordinates_supported,sub_self,add_zero]
  have returned:=congrArg (fun v=>(sourceStaticSpatialKernel n unit κ)⁻¹*ᵥv) padded
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (sourceStaticSpatialKernel_isUnit n unit κ)),
    Matrix.one_mulVec,Matrix.mulVec_smul] at returned
  exact returned

theorem sourceSpatialStaticFieldSchur (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) : sourceSpatialStaticActiveField n unit κ forcing=
    (-(κ.val:ℂ)^2)⁻¹ • (effectiveFrame (sourceStaticSpatialPoint n unit κ)*ᵥ((sourceStaticSpatialKernel n unit κ)⁻¹*ᵥ
      (effectiveReader (sourceStaticSpatialPoint n unit κ)*ᵥsourceSpatialStaticActiveForcing n unit κ forcing)))+
      complementGreen (sourceStaticSpatialPoint n unit κ)*ᵥsourceSpatialStaticActiveForcing n unit κ forcing:=by
  have h:=effective_field_reconstruction (sourceStaticSpatialPoint n unit κ) _ _ (sourceSpatialStaticActiveFieldInside n unit κ forcing) (sourceSpatialStaticActiveFieldSource n unit κ forcing)
  rw [sourceSpatialStaticCoordinatesReturn,Matrix.mulVec_smul] at h
  exact h

def sourceSpatialStaticContactField (n : PhysicalMomentum) (_unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  originalChange (sourceStaticSpatialMomentum n κ.val)*ᵥ(contactInverse (sourceStaticSpatialMomentum n κ.val)*ᵥ
    (originalReadback (sourceStaticSpatialMomentum n κ.val)*ᵥforcing))

theorem sourceSpatialStaticNativeFieldContactActive (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) :
    sourceSpatialStaticNativeField n unit κ forcing=sourceSpatialStaticContactField n unit κ forcing+
      originalChange (sourceStaticSpatialMomentum n κ.val)*ᵥsourceSpatialStaticActiveField n unit κ forcing:=by
  let p:=sourceStaticSpatialMomentum n κ.val
  have inverseRead : originalInverse p*ᵥsourceSpatialStaticNativeField n unit κ forcing=
      (contactInverse p+activeProjection*(extendedKernel p)⁻¹)*ᵥ(originalReadback p*ᵥforcing):=by
    change originalInverse p*ᵥ((originalChange p*(contactInverse p+activeProjection*(extendedKernel p)⁻¹)*originalReadback p)*ᵥforcing)=_
    simp only [Matrix.mulVec_mulVec]
    rw [←mul_assoc,←mul_assoc,original_inverse_change,one_mul]
  have activeRead : sourceSpatialStaticActiveField n unit κ forcing=
      (activeProjection*(extendedKernel p)⁻¹)*ᵥ(originalReadback p*ᵥforcing):=by
    change activeProjection*ᵥ(originalInverse p*ᵥsourceSpatialStaticNativeField n unit κ forcing)=_
    rw [inverseRead,Matrix.mulVec_mulVec,mul_add,active_contact_inverse_zero,zero_add,
      ←mul_assoc,active_square]
  rw [activeRead]
  change (originalChange p*(contactInverse p+activeProjection*(extendedKernel p)⁻¹)*originalReadback p)*ᵥforcing=
    originalChange p*ᵥ(contactInverse p*ᵥ(originalReadback p*ᵥforcing))+
      originalChange p*ᵥ((activeProjection*(extendedKernel p)⁻¹)*ᵥ(originalReadback p*ᵥforcing))
  simp only [mul_add,add_mul,Matrix.add_mulVec,Matrix.mulVec_mulVec,mul_assoc]

theorem sourceSpatialStaticNativeFieldSchur (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) : sourceSpatialStaticNativeField n unit κ forcing=
    sourceSpatialStaticContactField n unit κ forcing+
      (-(κ.val:ℂ)^2)⁻¹ • (nativeEffectiveFrame (sourceStaticSpatialPoint n unit κ)*ᵥ((sourceStaticSpatialKernel n unit κ)⁻¹*ᵥ
        (effectiveReader (sourceStaticSpatialPoint n unit κ)*ᵥsourceSpatialStaticActiveForcing n unit κ forcing)))+
      originalChange (sourceStaticSpatialMomentum n κ.val)*ᵥ(complementGreen (sourceStaticSpatialPoint n unit κ)*ᵥsourceSpatialStaticActiveForcing n unit κ forcing):=by
  rw [sourceSpatialStaticNativeFieldContactActive,sourceSpatialStaticFieldSchur,Matrix.mulVec_add,Matrix.mulVec_smul]
  simp only [nativeEffectiveFrame,←Matrix.mulVec_mulVec]
  change sourceSpatialStaticContactField n unit κ forcing+(_+_)=sourceSpatialStaticContactField n unit κ forcing+_+_
  dsimp only [sourceStaticSpatialPoint,controlledPoint]
  abel

def sourceSpatialStaticSourceReader (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  effectiveReader (sourceStaticSpatialPoint n unit κ)*ᵥsourceSpatialStaticActiveForcing n unit κ forcing

theorem sourceSpatialStaticSourceReaderSupported (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) :
    fiveProjection*ᵥsourceSpatialStaticSourceReader n unit κ forcing=sourceSpatialStaticSourceReader n unit κ forcing:=by
  rw [sourceSpatialStaticSourceReader,Matrix.mulVec_mulVec,effectiveReader_supported]

def sourceSpatialStaticPoleCoefficient (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  nativeEffectiveFrame (sourceStaticSpatialPoint n unit κ)*ᵥ(staticInverse*ᵥsourceSpatialStaticSourceReader n unit κ forcing)

def sourceSpatialStaticRegularField (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) : Fin 289→ℂ:=
  sourceSpatialStaticContactField n unit κ forcing+originalChange (sourceStaticSpatialMomentum n κ.val)*ᵥ
    (complementGreen (sourceStaticSpatialPoint n unit κ)*ᵥsourceSpatialStaticActiveForcing n unit κ forcing)

theorem sourceSpatialStaticNativeFieldPoleFactor (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) :
    (-(κ.val:ℂ)^2) • (sourceSpatialStaticNativeField n unit κ forcing-sourceSpatialStaticRegularField n unit κ forcing)=
      nativeEffectiveFrame (sourceStaticSpatialPoint n unit κ)*ᵥ((sourceStaticSpatialKernel n unit κ)⁻¹*ᵥsourceSpatialStaticSourceReader n unit κ forcing):=by
  have nonzero : (-(κ.val:ℂ)^2)≠0:=by
    exact neg_ne_zero.mpr (pow_ne_zero 2 (by exact_mod_cast ne_of_gt κ.property.1))
  have returned:=sourceSpatialStaticNativeFieldSchur n unit κ forcing
  have difference : sourceSpatialStaticNativeField n unit κ forcing-sourceSpatialStaticRegularField n unit κ forcing=
      (-(κ.val:ℂ)^2)⁻¹ • (nativeEffectiveFrame (sourceStaticSpatialPoint n unit κ)*ᵥ((sourceStaticSpatialKernel n unit κ)⁻¹*ᵥsourceSpatialStaticSourceReader n unit κ forcing)):=by
    rw [returned]
    unfold sourceSpatialStaticRegularField sourceSpatialStaticSourceReader
    abel
  rw [difference,smul_smul,mul_inv_cancel₀ nonzero,one_smul]

theorem sourceSpatialStaticNativeFieldPolePrice (n : PhysicalMomentum) (unit : spatialSquare n=1) (κ : staticDomain) (forcing : Fin 289→ℂ) :
    ‖(-(κ.val:ℂ)^2) • (sourceSpatialStaticNativeField n unit κ forcing-sourceSpatialStaticRegularField n unit κ forcing)-sourceSpatialStaticPoleCoefficient n unit κ forcing‖  ≤
      ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit κ)‖*(2*staticInverseBudget^2*effectiveErrorBudget*κ.val)*‖sourceSpatialStaticSourceReader n unit κ forcing‖:=by
  have padded : paddedStaticInverse*ᵥsourceSpatialStaticSourceReader n unit κ forcing=staticInverse*ᵥsourceSpatialStaticSourceReader n unit κ forcing:=by
    rw [paddedStaticInverse,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,sourceSpatialStaticSourceReaderSupported,sub_self,add_zero]
  rw [sourceSpatialStaticNativeFieldPoleFactor,sourceSpatialStaticPoleCoefficient,←padded,←Matrix.mulVec_sub,←Matrix.sub_mulVec]
  calc
    _  ≤  ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit κ)‖*‖((sourceStaticSpatialKernel n unit κ)⁻¹-paddedStaticInverse)*ᵥsourceSpatialStaticSourceReader n unit κ forcing‖:=Matrix.linfty_opNorm_mulVec _ _
    _  ≤  ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit κ)‖*((2*staticInverseBudget^2*effectiveErrorBudget*κ.val)*‖sourceSpatialStaticSourceReader n unit κ forcing‖):=by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right (sourceStaticSpatialKernel_inverse_delta n unit κ) (norm_nonneg _))
    _= _:=by ring

theorem sourceSpatialNormalizedInverseTendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) : Tendsto (fun κ : staticDomain=>(sourceStaticSpatialKernel n unit κ)⁻¹) staticApproach (𝓝 paddedStaticInverse):=by
  have upper : Tendsto (fun κ : staticDomain=>2*staticInverseBudget^2*effectiveErrorBudget*κ.val) staticApproach (𝓝 (0:ℝ)):=by
    simpa only [mul_zero] using tendsto_const_nhds.mul staticVal_tendsto
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _))
    (Eventually.of_forall (sourceStaticSpatialKernel_inverse_delta n unit)) upper

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

theorem sourceSpatialStaticMomentumTendsto (n : PhysicalMomentum) : Tendsto (fun κ : staticDomain=>sourceStaticSpatialMomentum n κ.val) staticApproach (𝓝 0):=by
  have continuous : Continuous (sourceStaticSpatialMomentum n):=by unfold sourceStaticSpatialMomentum;fun_prop
  have zero : sourceStaticSpatialMomentum n 0=0:=by ext i;fin_cases i <;> simp [sourceStaticSpatialMomentum]
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

theorem sourceSpatialComplementGreenTendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) : Tendsto (fun κ : staticDomain=>complementGreen (sourceStaticSpatialPoint n unit κ)) staticApproach (𝓝 fullInverse):=by
  have inverseAt : ContinuousAt Ring.inverse (complementKernel 0).det:=by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ origin_determinant
  have inverse:=((continuousAt_matrix_inv (complementKernel 0) inverseAt).tendsto.comp
    (complementKernel_continuous.continuousAt.tendsto.comp (sourceSpatialStaticMomentumTendsto n)))
  have result:= ((tendsto_const_nhds (x:=fullComplementProjection)).mul inverse).mul (tendsto_const_nhds (x:=fullComplementProjection))
  rw [←complementGreen_origin]
  exact result

private theorem kernel_left_zero : fullKernelFrame.transpose*activeKernel 0=0:=by
  have h:=congrArg Matrix.transpose fullKernel_origin
  have symmetric : (activeKernel 0).transpose=activeKernel 0:=by
    simpa only [neg_zero] using PreparationVacuumMixedEffective.activeKernel_reflect (0:Fin 4→ℂ)
  simpa only [Matrix.transpose_mul,Matrix.transpose_zero,symmetric] using h

theorem sourceSpatialEffectiveFrameTendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) : Tendsto (fun κ : staticDomain=>effectiveFrame (sourceStaticSpatialPoint n unit κ)) staticApproach (𝓝 fullKernelFrame):=by
  have kernel:=activeKernel_continuous.continuousAt.tendsto.comp (sourceSpatialStaticMomentumTendsto n)
  have result:=(tendsto_const_nhds (x:=fullKernelFrame)).sub (((sourceSpatialComplementGreenTendsto n unit).mul kernel).mul (tendsto_const_nhds (x:=fullKernelFrame)))
  have zero : fullInverse*activeKernel 0*fullKernelFrame=0:=by rw [mul_assoc,fullKernel_origin,mul_zero]
  simpa only [zero,sub_zero,effectiveFrame,Function.comp_def,sourceStaticSpatialPoint,controlledPoint] using result

theorem sourceSpatialNativeEffectiveFrameTendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) : Tendsto (fun κ : staticDomain=>nativeEffectiveFrame (sourceStaticSpatialPoint n unit κ)) staticApproach (𝓝 fullNativeOrigin):=by
  exact (originalChange_continuous.continuousAt.tendsto.comp (sourceSpatialStaticMomentumTendsto n)).mul (sourceSpatialEffectiveFrameTendsto n unit)

theorem sourceSpatialEffectiveReaderTendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) : Tendsto (fun κ : staticDomain=>effectiveReader (sourceStaticSpatialPoint n unit κ)) staticApproach (𝓝 fullKernelFrame.transpose):=by
  have kernel:=activeKernel_continuous.continuousAt.tendsto.comp (sourceSpatialStaticMomentumTendsto n)
  have result:=(tendsto_const_nhds (x:=fullKernelFrame.transpose)).sub (((tendsto_const_nhds (x:=fullKernelFrame.transpose)).mul kernel).mul (sourceSpatialComplementGreenTendsto n unit))
  simpa only [kernel_left_zero,zero_mul,sub_zero,effectiveReader,Function.comp_def,sourceStaticSpatialPoint,controlledPoint] using result

private theorem kernelTranspose_active : fullKernelFrame.transpose*activeProjection=fullKernelFrame.transpose:=by
  have h:=congrArg Matrix.transpose fullKernel_active
  simpa only [Matrix.transpose_mul,activeProjection,projectionMatrix,Matrix.diagonal_transpose] using h

private theorem tendsto_mulVec {A : Type*} {f : Filter A}
    {M : A→Matrix (Fin 289) (Fin 289) ℂ} {v : A→Fin 289→ℂ}
    {M0 : Matrix (Fin 289) (Fin 289) ℂ} {v0 : Fin 289→ℂ}
    (hm : Tendsto M f (𝓝 M0)) (hv : Tendsto v f (𝓝 v0)) : Tendsto (fun a=>M a*ᵥv a) f (𝓝 (M0*ᵥv0)):=
  (continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp (hm.prodMk_nhds hv)

theorem sourceSpatialStaticSourceReaderTendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>sourceSpatialStaticSourceReader n unit κ forcing) staticApproach (𝓝 (fullNativeOrigin.transpose*ᵥforcing)):=by
  have readback:=originalReadback_continuous.continuousAt.tendsto.comp (sourceSpatialStaticMomentumTendsto n)
  have result:=tendsto_mulVec (sourceSpatialEffectiveReaderTendsto n unit)
    (tendsto_mulVec (tendsto_const_nhds (x:=activeProjection)) (tendsto_mulVec readback (tendsto_const_nhds (x:=forcing))))
  have returned : fullKernelFrame.transpose*ᵥ(activeProjection*ᵥ(originalReadback 0*ᵥforcing))=fullNativeOrigin.transpose*ᵥforcing:=by
    rw [Matrix.mulVec_mulVec (originalReadback 0*ᵥforcing),kernelTranspose_active]
    simp only [fullNativeOrigin,Matrix.transpose_mul,originalReadback,neg_zero,Matrix.mulVec_mulVec]
  simpa only [sourceSpatialStaticSourceReader,sourceSpatialStaticActiveForcing,returned,Function.comp_def] using result

private theorem fullNativeOriginTranspose_supported (forcing : Fin 289→ℂ) :
    fiveProjection*ᵥ(fullNativeOrigin.transpose*ᵥforcing)=fullNativeOrigin.transpose*ᵥforcing:=by
  rw [fullNativeOrigin,Matrix.transpose_mul]
  simp only [Matrix.mulVec_mulVec,←mul_assoc,fullKernelTranspose_five]

theorem sourceSpatialStaticPoleCoefficientTendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>sourceSpatialStaticPoleCoefficient n unit κ forcing) staticApproach (𝓝 (staticResidue forcing)):=
  tendsto_mulVec (sourceSpatialNativeEffectiveFrameTendsto n unit) (tendsto_mulVec tendsto_const_nhds (sourceSpatialStaticSourceReaderTendsto n unit forcing))

theorem sourceSpatialStaticPoleFactorTendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • (sourceSpatialStaticNativeField n unit κ forcing-sourceSpatialStaticRegularField n unit κ forcing))
      staticApproach (𝓝 (staticResidue forcing)):=by
  have result:=tendsto_mulVec (sourceSpatialNativeEffectiveFrameTendsto n unit) (tendsto_mulVec (sourceSpatialNormalizedInverseTendsto n unit) (sourceSpatialStaticSourceReaderTendsto n unit forcing))
  have padded : paddedStaticInverse*ᵥ(fullNativeOrigin.transpose*ᵥforcing)=staticInverse*ᵥ(fullNativeOrigin.transpose*ᵥforcing):=by
    rw [paddedStaticInverse,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,fullNativeOriginTranspose_supported,sub_self,add_zero]
  simpa only [sourceSpatialStaticNativeFieldPoleFactor,padded,staticResidue] using result

theorem sourceSpatialStaticRegularFieldTendsto (n : PhysicalMomentum) (unit : spatialSquare n=1) (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>sourceSpatialStaticRegularField n unit κ forcing) staticApproach
      (𝓝 (originalChange 0*ᵥ(contactInverse 0*ᵥ(originalReadback 0*ᵥforcing))+
        originalChange 0*ᵥ(fullInverse*ᵥ(activeProjection*ᵥ(originalReadback 0*ᵥforcing))))):=by
  have change:=originalChange_continuous.continuousAt.tendsto.comp (sourceSpatialStaticMomentumTendsto n)
  have contact:=contactInverse_continuous.continuousAt.tendsto.comp (sourceSpatialStaticMomentumTendsto n)
  have readback:=originalReadback_continuous.continuousAt.tendsto.comp (sourceSpatialStaticMomentumTendsto n)
  exact (tendsto_mulVec change (tendsto_mulVec contact (tendsto_mulVec readback tendsto_const_nhds))).add
    (tendsto_mulVec change (tendsto_mulVec (sourceSpatialComplementGreenTendsto n unit)
      (tendsto_mulVec tendsto_const_nhds (tendsto_mulVec readback tendsto_const_nhds))))

/-- The original, uncleared whole-field Green has this source-generated static pole coefficient on a nonempty physical domain. -/
theorem sourceSpatialStaticNativeFieldResidue (n : PhysicalMomentum) (unit : spatialSquare n=1) (forcing : Fin 289→ℂ) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • sourceSpatialStaticNativeField n unit κ forcing) staticApproach (𝓝 (staticResidue forcing)):=by
  have scalar : Tendsto (fun κ : staticDomain=>-(κ.val:ℂ)^2) staticApproach (𝓝 (0:ℂ)):=by
    simpa only [Function.comp_def,Complex.ofReal_zero,zero_pow (by decide : 2≠0),neg_zero] using (Complex.continuous_ofReal.continuousAt.tendsto.comp staticVal_tendsto).pow 2 |>.neg
  have regular:=scalar.smul (sourceSpatialStaticRegularFieldTendsto n unit forcing)
  have result:=(sourceSpatialStaticPoleFactorTendsto n unit forcing).add regular
  have split (κ : staticDomain) : (-(κ.val:ℂ)^2) • (sourceSpatialStaticNativeField n unit κ forcing-sourceSpatialStaticRegularField n unit κ forcing)+
      (-(κ.val:ℂ)^2) • sourceSpatialStaticRegularField n unit κ forcing=(-(κ.val:ℂ)^2) • sourceSpatialStaticNativeField n unit κ forcing:=by rw [smul_sub];abel
  simpa only [split,zero_smul,add_zero] using result

private theorem contraction_price (J v : Fin 289→ℂ) :
    ‖∑i,J i*v i‖ ≤ (∑i,‖J i‖)*‖v‖ := by
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (norm_nonneg _)

/-- The original O(kappa) field error controls every complete current contraction uniformly in the spatial direction. -/
theorem sourceStaticSpatialContraction_price (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (kappa : staticDomain) (source detector : Fin 289→ℂ) :
    ‖∑i,detector i*((-(kappa.val:ℂ)^2)*
      (sourceSpatialStaticNativeField direction unit kappa source i-sourceSpatialStaticRegularField direction unit kappa source i)-
      sourceSpatialStaticPoleCoefficient direction unit kappa source i)‖ ≤
      (∑i,‖detector i‖)*‖nativeEffectiveFrame (sourceStaticSpatialPoint direction unit kappa)‖*
        (2*staticInverseBudget^2*effectiveErrorBudget*kappa.val)*‖sourceSpatialStaticSourceReader direction unit kappa source‖ := by
  have generated:=sourceSpatialStaticNativeFieldPolePrice direction unit kappa source
  have actual:=contraction_price detector
    ((-(kappa.val:ℂ)^2) • (sourceSpatialStaticNativeField direction unit kappa source-sourceSpatialStaticRegularField direction unit kappa source)-
      sourceSpatialStaticPoleCoefficient direction unit kappa source)
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at actual
  apply actual.trans
  exact (mul_le_mul_of_nonneg_left generated (Finset.sum_nonneg (fun i _=>norm_nonneg _))).trans_eq
    (by ring)

/-- Original source and detector preparations remain independent on the whole Green. -/
def sourceStaticSpatialInteraction (direction : PhysicalMomentum) (unit : spatialSquare direction=1) (kappa : staticDomain)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  ∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
    sourceSpatialStaticNativeField direction unit kappa
      (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i

/-- The source-produced whole static residue, with every source current coordinate and both original detector inverses. -/
theorem sourceStaticSpatialInteraction_generated (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    Tendsto (fun kappa : staticDomain=> (-(kappa.val:ℂ)^2)*
      sourceStaticSpatialInteraction direction unit kappa
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)
      staticApproach (𝓝 (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
        staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)) := by
  have produced:=sourceSpatialStaticNativeFieldResidue direction unit
    (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)
  have reader : Continuous (fun v : Fin 289→ℂ=>
      ∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*v i) := by fun_prop
  have actual:=reader.continuousAt.tendsto.comp produced
  convert actual using 1
  funext kappa
  simp only [sourceStaticSpatialInteraction,Function.comp_def,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn
