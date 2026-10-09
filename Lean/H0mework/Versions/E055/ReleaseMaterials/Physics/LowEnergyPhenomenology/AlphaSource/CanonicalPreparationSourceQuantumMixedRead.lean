import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticNativeMode
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePoleQuantumWard
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMovingCurrentConservation
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationOriginalFieldPoleReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalFieldChannel
open PreparationVacuumOriginalGreenFeedback SourcePropagationNativeActionHessian
open PreparationVacuumElectromagneticIdentity PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumCurrentSignalOperator CanonicalGradedSpatialSource SourcePropagationConstrainedPoleReturn
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalJacobi originalChange originalInverse originalReadback
  originalRowLift PreparationVacuumOriginalGreenFeedback.sourceField nativeHessian sourcePoleQuantumWindow sourcePoleQuantumCosource

private theorem staticAxis_neg (k : ℂ) : staticAxis (-k)= -staticAxis k :=by
  ext i;fin_cases i <;> simp [staticAxis]
private theorem channelDenominator_neg (k : ℂ) : channelDenominator (-k)=channelDenominator k :=by
  unfold channelDenominator channelFactor;ring

private theorem numerator_null_certificate :
    fastNormalizeTerms (productTerms (projectionTerms nullFlag) channelNumeratorTerms)=[] :=by decide +kernel

private theorem channel_null (k : ℂ) : nullProjection*ᵥchannelNumerator k=0 :=by
  have actual:=fastNormalizeTerms_value (productTerms (projectionTerms nullFlag) channelNumeratorTerms) (staticAxis k)
  rw [numerator_null_certificate,sourceMatrix_nil,productTerms_value,projectionTerms_value] at actual
  exact (congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>fun i=>A i 0) actual).symm

private theorem source_pairing (k : ℂ) (forcing : Fin 289→ℂ) :
    channelNativeNumerator (-k) ⬝ᵥ forcing=
      channelNumerator (-k) ⬝ᵥ (originalReadback (staticAxis k)*ᵥforcing) :=by
  rw [channelNativeNumerator,originalReadback,←staticAxis_neg]
  rw [Matrix.dotProduct_transpose_mulVec,dotProduct_comm]

private theorem source_pairing_null (k : ℂ) (forcing : Fin 289→ℂ) :
    channelNativeNumerator (-k) ⬝ᵥ
      (originalRowLift (staticAxis k)*ᵥ(nullProjection*ᵥforcing))=0 :=by
  rw [source_pairing,Matrix.mulVec_mulVec]
  have inverse : originalReadback (staticAxis k)*originalRowLift (staticAxis k)=1:=by
    unfold originalReadback originalRowLift
    rw [←Matrix.transpose_mul,original_inverse_change,Matrix.transpose_one]
  rw [inverse,Matrix.one_mulVec]
  have symm : nullProjection.transpose=nullProjection:=by simp [nullProjection,projectionMatrix]
  rw [←symm,Matrix.dotProduct_transpose_mulVec,channel_null,dotProduct_zero]

/-- Exact reciprocity is the original reflected transpose law, not self-adjointness. -/
theorem channel_actual_forcing_read (k : ℂ) (regular : staticAxis k∈regularSource)
    (forcing : Fin 289→ℂ) :
    channelDenominator k*(originalInverse (staticAxis k)*ᵥsourceField ⟨staticAxis k,regular⟩ forcing) 21=
      channelNumerator (-k) ⬝ᵥ (originalReadback (staticAxis k)*ᵥforcing) :=by
  let response:=PreparationVacuumOriginalGreenFeedback.sourceField ⟨staticAxis k,regular⟩ forcing
  have equation:=original_forced_field (⟨staticAxis k,regular⟩:regularSource) forcing
  have paired:=congrArg (fun v : Fin 289→ℂ=>channelNativeNumerator (-k) ⬝ᵥv) equation
  simp only [sourceCompatibility] at paired
  have reciprocal : originalJacobi (staticAxis k)=(originalJacobi (staticAxis (-k))).transpose:=by
    rw [staticAxis_neg,original_jacobi_reciprocity]
  rw [reciprocal,Matrix.dotProduct_transpose_mulVec] at paired
  have mode:=channel_native_equation (-k)
  rw [nativeActionFourierHessian_original] at mode
  rw [mode,dotProduct_smul,channelDenominator_neg,dotProduct_sub,source_pairing,source_pairing_null] at paired
  rw [sub_zero] at paired
  have leg : response ⬝ᵥ (originalRowLift (staticAxis (-k))*ᵥ(Pi.single 21 1 : Fin 289→ℂ))=
      (originalInverse (staticAxis k)*ᵥresponse) 21 :=by
    rw [originalRowLift,staticAxis_neg,neg_neg,Matrix.dotProduct_transpose_mulVec,single_one_dotProduct]
  change channelDenominator k*(response ⬝ᵥ (originalRowLift (staticAxis (-k))*ᵥ(Pi.single 21 1 : Fin 289→ℂ)))=_ at paired
  rw [leg] at paired
  exact paired

private theorem source_matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) :=by
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

private theorem staticAxis_continuous : Continuous staticAxis :=by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [staticAxis] <;> fun_prop

theorem channel_native_continuous : Continuous channelNativeNumerator :=by
  unfold channelNativeNumerator originalChange
  apply Continuous.matrix_mulVec ((source_matrix_continuous originalChangeTerms).comp staticAxis_continuous)
  apply continuous_pi
  intro i
  exact (((source_matrix_continuous channelNumeratorTerms).comp staticAxis_continuous).matrix_elem i 0)

/-- Source-generated leading normalization; no pole location or residue is supplied. -/
def channelNormalizedNative (k : ℂ) : Fin 289→ℂ := (channelFactor k)⁻¹ • channelNativeNumerator k

theorem channel_normalized_limit : Filter.Tendsto channelNormalizedNative (𝓝 (0:ℂ)) (𝓝 (channelNativeNumerator 0)) :=by
  have c : ContinuousAt channelNormalizedNative 0:=
    (channel_factor_continuous.continuousAt.inv₀ (by rw [channel_factor_at_zero];exact one_ne_zero)).smul
      channel_native_continuous.continuousAt
  simpa only [channelNormalizedNative,channel_factor_at_zero,inv_one,one_smul] using c.tendsto

def channelNativeResponse (k : ℂ) : Fin 289→ℂ := (channelDenominator k)⁻¹ • channelNativeNumerator k

theorem channel_native_response (k : ℂ) (regular : channelDenominator k≠0) :
    nativeFourierHessian nativeHessian (staticAxis k)*ᵥchannelNativeResponse k=
      originalRowLift (staticAxis k)*ᵥ(Pi.single 21 1 : Fin 289→ℂ) :=by
  rw [channelNativeResponse,Matrix.mulVec_smul,channel_native_equation,smul_smul,
    inv_mul_cancel₀ regular,one_smul]

theorem channel_double_pole_generated :
    Filter.Tendsto (fun k : ℂ=>k^2 • channelNativeResponse k) (𝓝[≠] (0:ℂ))
      (𝓝 (channelNativeNumerator 0)) :=by
  have normalized : Filter.Tendsto channelNormalizedNative (𝓝[≠] (0:ℂ)) (𝓝 (channelNativeNumerator 0)):=
    channel_normalized_limit.mono_left nhdsWithin_le_nhds
  apply normalized.congr'
  have factor : ∀ᶠ k in 𝓝 (0:ℂ),channelFactor k≠0:=
    channel_factor_continuous.continuousAt.eventually_ne (by rw [channel_factor_at_zero];exact one_ne_zero)
  have off : ∀ᶠ k in 𝓝[≠] (0:ℂ),k≠0:=by
    filter_upwards [self_mem_nhdsWithin] with k hk
    exact hk
  filter_upwards [factor.filter_mono nhdsWithin_le_nhds,off] with k hk hk0
  simp only [channelNormalizedNative,channelNativeResponse,channelDenominator,smul_smul]
  congr 1
  field_simp [hk,hk0]

def staticSpatial (k : ℂ) : Fin 3→ℂ := ![k,0,0]
private theorem static_fullMomentum (k : ℂ) : fullMomentum (staticSpatial k) 0=staticAxis k :=by
  ext i;fin_cases i <;> rfl

/-- Same actual two-wave event, full Gauss material legs, and both actual history quadratures. -/
def actualChannelWindow (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ :=
  sourcePoleQuantumWindow q pL pR left right (sourcePhysicalFourier pL pR left right)
    (sourcePhysicalCurrentAmplitude pL pR left right) 0 T

def actualChannelCosource (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ :=
  sourcePoleQuantumCosource q pL pR left right (sourcePhysicalFourier pL pR left right)
    (sourcePhysicalCurrentAmplitude pL pR left right) (physicalSpatial (sourcePhysicalTransfer pL pR)) 0 T

theorem actualChannel_read (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (k : ℂ) (T : ℝ) (axis : physicalSpatial (sourcePhysicalTransfer pL pR)=staticSpatial k)
    (regular : staticAxis k∈regularSource) :
    channelDenominator k*(originalInverse (staticAxis k)*ᵥ
      PreparationVacuumOriginalGreenFeedback.sourceField ⟨staticAxis k,regular⟩ (actualChannelWindow q pL pR left right T)) 21=
      channelNumerator (-k) ⬝ᵥactualChannelCosource q pL pR left right T :=by
  rw [channel_actual_forcing_read]
  have ward:=sourcePoleQuantumWindow_ward q pL pR left right (sourcePhysicalFourier pL pR left right)
    (sourcePhysicalCurrentAmplitude pL pR left right) (staticSpatial k) 0 T
  rw [static_fullMomentum] at ward
  rw [actualChannelWindow,ward]
  simp only [actualChannelCosource,axis]

theorem actualChannel_whole_native (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (k : ℂ) (T : ℝ) (axis : physicalSpatial (sourcePhysicalTransfer pL pR)=staticSpatial k)
    (regular : staticAxis k∈regularSource) :
    nativeFourierHessian nativeHessian (staticAxis k)*ᵥ
      PreparationVacuumOriginalGreenFeedback.sourceField ⟨staticAxis k,regular⟩ (actualChannelWindow q pL pR left right T)=
      actualChannelWindow q pL pR left right T-
        originalRowLift (staticAxis k)*ᵥ(nullProjection*ᵥactualChannelCosource q pL pR left right T) :=by
  have returned:=sourcePoleQuantumWindow_native q pL pR left right (sourcePhysicalFourier pL pR left right)
    (sourcePhysicalCurrentAmplitude pL pR left right) (staticSpatial k) 0 T
    (by simpa only [static_fullMomentum] using regular)
  simpa only [static_fullMomentum,actualChannelWindow,actualChannelCosource,axis] using returned

/-- This numerator consumer is valid even on the full field singular locus. -/
theorem channel_cleared_forcing_read (k : ℂ) (forcing : Fin 289→ℂ) :
    channelDenominator k*(originalInverse (staticAxis k)*ᵥ(originalClearedGreen (staticAxis k)*ᵥforcing)) 21=
      originalFieldDenominator (staticAxis k)*(channelNumerator (-k) ⬝ᵥ (originalReadback (staticAxis k)*ᵥforcing)) :=by
  let response:=originalClearedGreen (staticAxis k)*ᵥforcing
  have equation : originalJacobi (staticAxis k)*ᵥresponse=
      originalFieldDenominator (staticAxis k) •
        (forcing-originalRowLift (staticAxis k)*ᵥ(sourceCompatibility (staticAxis k) forcing)) :=by
    dsimp [response]
    rw [Matrix.mulVec_mulVec,originalClearedGreen_equation,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec]
    simp only [sourceCompatibility,Matrix.mulVec_mulVec,mul_assoc]
  have paired:=congrArg (fun v : Fin 289→ℂ=>channelNativeNumerator (-k) ⬝ᵥv) equation
  have reciprocal : originalJacobi (staticAxis k)=(originalJacobi (staticAxis (-k))).transpose:=by
    rw [staticAxis_neg,original_jacobi_reciprocity]
  rw [reciprocal,Matrix.dotProduct_transpose_mulVec] at paired
  have mode:=channel_native_equation (-k)
  rw [nativeActionFourierHessian_original] at mode
  simp only [sourceCompatibility] at paired
  rw [mode,dotProduct_smul,channelDenominator_neg,dotProduct_smul,dotProduct_sub,
    source_pairing,source_pairing_null,sub_zero] at paired
  have leg : response ⬝ᵥ (originalRowLift (staticAxis (-k))*ᵥ(Pi.single 21 1 : Fin 289→ℂ))=
      (originalInverse (staticAxis k)*ᵥresponse) 21 :=by
    rw [originalRowLift,staticAxis_neg,neg_neg,Matrix.dotProduct_transpose_mulVec,single_one_dotProduct]
  change channelDenominator k*(response ⬝ᵥ (originalRowLift (staticAxis (-k))*ᵥ(Pi.single 21 1 : Fin 289→ℂ)))=_ at paired
  rw [leg] at paired
  exact paired

theorem actualChannel_cleared_read (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (k : ℂ) (T : ℝ)
    (axis : physicalSpatial (sourcePhysicalTransfer pL pR)=staticSpatial k) :
    channelDenominator k*(originalInverse (staticAxis k)*ᵥ(originalClearedGreen (staticAxis k)*ᵥ
      actualChannelWindow q pL pR left right T)) 21=
      originalFieldDenominator (staticAxis k)*
        (channelNumerator (-k) ⬝ᵥactualChannelCosource q pL pR left right T) :=by
  rw [channel_cleared_forcing_read]
  have ward:=sourcePoleQuantumWindow_ward q pL pR left right (sourcePhysicalFourier pL pR left right)
    (sourcePhysicalCurrentAmplitude pL pR left right) (staticSpatial k) 0 T
  rw [static_fullMomentum] at ward
  rw [actualChannelWindow,ward]
  simp only [actualChannelCosource,axis]

theorem actualChannel_cleared_whole_native (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (k : ℂ) (T : ℝ)
    (axis : physicalSpatial (sourcePhysicalTransfer pL pR)=staticSpatial k) :
    nativeFourierHessian nativeHessian (staticAxis k)*ᵥ
      (originalClearedGreen (staticAxis k)*ᵥactualChannelWindow q pL pR left right T)=
      originalFieldDenominator (staticAxis k) •
        (actualChannelWindow q pL pR left right T-
          originalRowLift (staticAxis k)*ᵥ(nullProjection*ᵥactualChannelCosource q pL pR left right T)) :=by
  rw [nativeActionFourierHessian_original,Matrix.mulVec_mulVec,originalClearedGreen_equation,
    Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec]
  have ward:=sourcePoleQuantumWindow_ward q pL pR left right (sourcePhysicalFourier pL pR left right)
    (sourcePhysicalCurrentAmplitude pL pR left right) (staticSpatial k) 0 T
  rw [static_fullMomentum] at ward
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,actualChannelWindow,ward]
  simp only [actualChannelCosource,axis]

end LowEnergy.PreparationVacuumPhysicalFieldChannel
