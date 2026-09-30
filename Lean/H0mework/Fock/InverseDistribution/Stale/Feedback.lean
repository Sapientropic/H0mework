import H0mework.Fock.InverseDistribution.Stale.Clock

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionStale

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceInverseDistributionOptimalBirth
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem penalty_positive {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    0 < penalty runtime depth word read := by
  rw [penalty]
  exact div_pos (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (projected_born_ne runtime depth word read))) 2) (by positivity)

theorem stale_strict {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    total runtime.tick.next depth word read <
      ∑ actor : Actors runtime.tick.next, ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        decoder runtime depth word read (read actor.val)‖ ^ 2 := by
  rw [stale_loss]
  exact lt_add_of_pos_right _ (penalty_positive runtime depth word read)

theorem field_stale_strict (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) :
    SourceConditionalVector.dynamicError runtime.tick.next depth
      (fun observed => project depth word (SourceConditionalNativeKeys.decoder runtime.tick.next depth observed)) <
    SourceConditionalVector.dynamicError runtime.tick.next depth
      (fun observed => project depth word (SourceConditionalNativeKeys.decoder runtime depth observed)) := by
  have paid := stale_strict runtime depth word (fun index : Nat => (index : ZMod 2))
  rw [field_total runtime.tick.next depth word] at paid
  have atNext (actor : Actors runtime.tick.next) :
      project depth word (SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalModel.dynamicRead runtime.tick.next depth actor)) =
        decoder runtime depth word (fun index : Nat => (index : ZMod 2)) (actor.val : ZMod 2) := by
    change project depth word (SourceConditionalNativeKeys.decoder runtime depth
      (SourceConditionalInventory.observation (inventoryBound runtime.tick.next) depth actor)) = _
    rw [SourceConditionalNativeKeys.source_observed, SourceConditionalNativePosterior.parity_decoder]
    rfl
  have right : ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) *
      SourceConditionalVector.dynamicError runtime.tick.next depth
        (fun observed => project depth word (SourceConditionalNativeKeys.decoder runtime depth observed)) =
      ∑ actor : Actors runtime.tick.next, ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        decoder runtime depth word (fun index : Nat => (index : ZMod 2)) (actor.val : ZMod 2)‖ ^ 2 := by
    rw [SourceConditionalVector.dynamicError, SourceConditionalInventory.sum_count]
    simp only [atNext, ← SourceConditionalInventory.values_original]
  rw [← right] at paid
  exact (mul_lt_mul_iff_right₀ (by positivity : (0 : ℝ) < (inventoryBound runtime.tick.next + 1 : Nat))).mp paid

end
end SourceInverseDistributionStale
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
