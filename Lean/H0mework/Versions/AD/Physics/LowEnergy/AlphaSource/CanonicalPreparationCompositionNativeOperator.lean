import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionOperator
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLocalizedFactor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCompositionNative
open PreparationVacuumCompositionBounded PreparationVacuumFrequencyN2
open PreparationVacuumWeyl PreparationVacuumWeylDomain PreparationVacuumRemainder
open PreparationVacuumNativeClosure CanonicalPreparationSquareCutoff
open GaussDensityCore MeasureTheory
open scoped ComplexConjugate FourierTransform SchwartzMap

def sourceNativeComposition : sourceLocalSpace →L[ℂ] sourceLocalSpace :=
  (localInput.adjoint.comp sourceCompositionOperator).comp localInput

theorem sourceNativeComposition_isSelfAdjoint : IsSelfAdjoint sourceNativeComposition :=
  sourceCompositionOperator_isSelfAdjoint.adjoint_conj localInput

def sourceNativeCompositionBound : ℝ :=
  ‖localInput‖ * sourceCompositionSchurBound * ‖localInput‖

theorem sourceNativeCompositionBound_nonnegative : 0 ≤ sourceNativeCompositionBound := by
  unfold sourceNativeCompositionBound
  exact mul_nonneg (mul_nonneg (norm_nonneg localInput) sourceCompositionSchurBound_nonnegative)
    (norm_nonneg localInput)

theorem sourceNativeComposition_norm_bound :
    ‖sourceNativeComposition‖ ≤ sourceNativeCompositionBound := by
  calc
    _ ≤ ‖localInput.adjoint.comp sourceCompositionOperator‖*‖localInput‖ :=
      (localInput.adjoint.comp sourceCompositionOperator).opNorm_comp_le localInput
    _ ≤ (‖localInput.adjoint‖*‖sourceCompositionOperator‖)*‖localInput‖ :=
      mul_le_mul_of_nonneg_right (localInput.adjoint.opNorm_comp_le sourceCompositionOperator)
        (norm_nonneg localInput)
    _ = (‖localInput‖*‖sourceCompositionOperator‖)*‖localInput‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left sourceCompositionOperator_norm_bound (norm_nonneg localInput))
      (norm_nonneg localInput)

theorem sourceNativeComposition_readback (g f : sourceLocalSpace) :
    inner ℂ g (sourceNativeComposition f)=∫ xy : PhysicalMomentum × PhysicalMomentum,
      conj (localInput g xy.1)*actualFullCompositionKernelDefect xy.1 xy.2*
        localInput f xy.2 ∂volume.prod volume := by
  rw [sourceNativeComposition,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,sourceCompositionOperator_readback]

def sourceSignedComposition : sourceLocalSpace →L[ℂ] sourceLocalSpace :=
  -sourceNativeComposition

theorem sourceSignedComposition_isSelfAdjoint : IsSelfAdjoint sourceSignedComposition := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro g f
  change inner ℂ (-(sourceNativeComposition g)) f = inner ℂ g (-(sourceNativeComposition f))
  rw [inner_neg_left,inner_neg_right]
  exact congrArg Neg.neg (sourceNativeComposition_isSelfAdjoint.isSymmetric g f)

theorem sourceSignedComposition_norm_bound :
    ‖sourceSignedComposition‖ ≤ sourceNativeCompositionBound := by
  rw [sourceSignedComposition,ContinuousLinearMap.opNorm_neg]
  exact sourceNativeComposition_norm_bound

theorem sourceSignedComposition_readback (g f : sourceLocalSpace) :
    inner ℂ g (sourceSignedComposition f)=-(∫ xy : PhysicalMomentum × PhysicalMomentum,
      conj (localInput g xy.1)*actualFullCompositionKernelDefect xy.1 xy.2*
        localInput f xy.2 ∂volume.prod volume) := by
  rw [sourceSignedComposition,neg_apply,inner_neg_right,
    sourceNativeComposition_readback]

theorem localInput_original (f : ScalarTest) :
    localInput (localCore f)=(sourceVacuumInputFrequency (sourceVacuumInputCore f)).toLp 2 := by
  have same := localInput_core (localCore.rangeRestrict f)
  rw [localCoreInclusion_original,coreFrequencyInput_original] at same
  exact same

end LowEnergy.PreparationVacuumCompositionNative
