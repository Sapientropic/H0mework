import H0mework.Versions.R2.Fock.PrimeField.RecoveryWord

/-! The original complete prime-field observation model retains every finite source-word coefficient. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeHistoryRecovery

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory

noncomputable section

theorem history_separates (owner : GlobalParentOwner)
    (left right : SourceOperationNative.Carrier process)
    (same : ∀ stage : Nat, observation ((nativeAction ^ stage) left) =
      observation ((nativeAction ^ stage) right)) : left = right := by
  ext index
  rw [← recovers_source_word owner index left, ← recovers_source_word owner index right]
  change primeRead (selectedPrime owner index)
    (observation ((nativeAction ^ (delay owner index + 1)) left) -
      observation ((nativeAction ^ delay owner index) left)) =
    primeRead (selectedPrime owner index)
    (observation ((nativeAction ^ (delay owner index + 1)) right) -
      observation ((nativeAction ^ delay owner index) right))
  rw [same, same]

theorem sourceMap_injective (owner : GlobalParentOwner) :
    Function.Injective (sourceMap nativeAction observation) := by
  intro left right same
  exact history_separates owner left right
    ((source_fibre_iff nativeAction observation left right).mp same)

theorem kernel_zero (owner : GlobalParentOwner) :
    LinearMap.ker (sourceMap nativeAction observation) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (sourceMap_injective owner)

theorem original_model_fibre (owner : GlobalParentOwner)
    (left right : SourceOperationNative.Carrier process) :
    projection nativeAction observation left = projection nativeAction observation right ↔ left = right := by
  constructor
  · intro same
    exact history_separates owner left right
      ((model_fibre_iff nativeAction observation left right).mp same)
  · exact congrArg (projection nativeAction observation)

end
end SourcePrimeHistoryRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
