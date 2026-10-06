import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionForm

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCompositionBounded
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumRemainder PreparationVacuumWeylDomain
open PreparationVacuumFrequencyN2 CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped SchwartzMap ComplexConjugate FourierTransform ENNReal InnerProductSpace

def sourceCompositionOperator : FourierHilbert →L[ℂ] FourierHilbert :=
  InnerProductSpace.continuousLinearMapOfBilin sourceContinuousForm

theorem sourceCompositionOperator_left_readback (g f : FourierHilbert) :
    inner ℂ (sourceCompositionOperator g) f = sourceForm g f :=
  InnerProductSpace.continuousLinearMapOfBilin_apply sourceContinuousForm g f

theorem sourceCompositionOperator_readback (g f : FourierHilbert) :
    inner ℂ g (sourceCompositionOperator f) = ∫ xy, conj (g xy.1) *
      actualFullCompositionKernelDefect xy.1 xy.2 * f xy.2 ∂pairVolume := by
  rw [← inner_conj_symm, sourceCompositionOperator_left_readback, sourceForm_hermitian]
  rfl

theorem sourceCompositionOperator_isSelfAdjoint : IsSelfAdjoint sourceCompositionOperator := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro g f
  change inner ℂ (sourceCompositionOperator g) f = inner ℂ g (sourceCompositionOperator f)
  rw [sourceCompositionOperator_left_readback, sourceCompositionOperator_readback]
  rfl

theorem sourceCompositionOperator_norm_bound :
    ‖sourceCompositionOperator‖ ≤ sourceCompositionSchurBound := by
  apply sourceCompositionOperator.opNorm_le_bound sourceCompositionSchurBound_nonnegative
  intro g
  change ‖(InnerProductSpace.toDual ℂ FourierHilbert).symm (sourceContinuousForm g)‖ ≤ _
  rw [(InnerProductSpace.toDual ℂ FourierHilbert).symm.norm_map]
  exact (ContinuousLinearMap.le_opNorm sourceContinuousForm g).trans
    (mul_le_mul_of_nonneg_right sourceContinuousForm_norm_bound (norm_nonneg g))

end LowEnergy.PreparationVacuumCompositionBounded
