import H0mework.Fock.HistoryConditional.InformationLossChain

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInformationLoss

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors positive)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem amount_nonnegative (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    0 ≤ amount runtime read forget := by
  rw [← conditional_is_amount]
  exact SourceConditionalNext.conditionalEntropy_nonnegative _ _ _ _

theorem amount_zero_iff_gap (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    amount runtime read forget = 0 ↔ SourceConditionalMergeLoss.gap runtime read forget = 0 := by
  rw [← conditional_is_amount, ← gap_zero_iff_information]

theorem amount_positive_iff_gap (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    0 < amount runtime read forget ↔ 0 < SourceConditionalMergeLoss.gap runtime read forget := by
  constructor
  · intro paid
    apply lt_of_le_of_ne (SourceConditionalMergeLoss.gap_nonnegative runtime read forget)
    intro zero
    exact paid.ne' ((amount_zero_iff_gap runtime read forget).mpr zero.symm)
  · intro paid
    apply lt_of_le_of_ne (amount_nonnegative runtime read forget)
    intro zero
    exact paid.ne' ((amount_zero_iff_gap runtime read forget).mp zero.symm)

theorem amount_lossless_iff (runtime : LivingRuntimeState process) (read : Nat → Fine) (forget : Fine → Coarse) :
    amount runtime read forget = 0 ↔
      ∀ left right : Actors runtime, forget (read left.val) = forget (read right.val) → read left.val = read right.val := by
  rw [amount_zero_iff_gap, SourceConditionalMergeLoss.lossless_iff]

end
end SourceConditionalInformationLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
