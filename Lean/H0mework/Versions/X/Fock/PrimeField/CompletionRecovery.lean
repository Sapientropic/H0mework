import H0mework.Versions.X.Fock.PrimeField.CompletionRange

/-! All source-generated coefficients separate the entire original completion, including its retained unit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem complete_zero_of_reads_zero (value : Field) (invisible : ∀ stage, read stage value = 0) : value = 0 := by
  apply Limits.Concrete.limit_ext ((data nativeAction observation).quotientTower (compatible nativeAction observation))
  intro stage
  apply (data nativeAction observation).stageRealization_injective stage.unop
  change stageRead nativeAction observation stage.unop value = stageRead nativeAction observation stage.unop 0
  rw [map_zero]
  funext index
  obtain ⟨word, agrees⟩ := finite_source_prefixes value stage.unop
  have high := congrFun (agrees stage.unop le_rfl) index
  have low := congrFun (agrees index.val (Nat.le_of_lt_succ index.isLt)) (Fin.last index.val)
  exact high.symm.trans (low.trans (invisible index.val))

theorem zero_of_coefficients_zero (owner : GlobalParentOwner) (value : Field)
    (invisible : ∀ index, coefficient owner index value = 0) : value = 0 := by
  apply complete_zero_of_reads_zero
  intro stage
  apply read_zero_of_prime_reads_zero
  intro prime
  exact (prime_read_is_mass_of_coefficients_zero owner value invisible prime stage).trans
    (mass_zero_of_coefficients_zero owner value invisible)

def coefficients (owner : GlobalParentOwner) : Field →ₗ[ℤ] (Nat → ℤ) := LinearMap.pi (coefficient owner)

theorem coefficients_injective (owner : GlobalParentOwner) : Function.Injective (coefficients owner) := by
  intro left right same
  apply sub_eq_zero.mp
  apply zero_of_coefficients_zero owner
  intro index
  have atIndex := congrFun same index
  change coefficient owner index left = coefficient owner index right at atIndex
  rw [map_sub, atIndex, sub_self]

theorem coefficients_source (owner : GlobalParentOwner) (word : SourceOperationNative.Carrier process) :
    coefficients owner (sourceMap nativeAction observation word) = fun index => word index := by
  funext index
  exact coefficient_source owner index word

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
