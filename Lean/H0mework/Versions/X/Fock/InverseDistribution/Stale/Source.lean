import H0mework.Versions.X.Fock.InverseBirth.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionStale

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceInverseDistributionOptimalBirth
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def penalty (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) : ℝ :=
  ‖project depth word (SourceConditionalInventory.born (inventoryBound runtime)) -
    decoder runtime depth word read (read (inventoryBound runtime + 1))‖ ^ 2 /
      ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 + 1)

theorem stale_loss (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    (∑ actor : Actors runtime.tick.next, ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
      decoder runtime depth word read (read actor.val)‖ ^ 2) =
      total runtime.tick.next depth word read + penalty runtime depth word read := by
  rw [SourceConditionalNativeBirth.total_append]
  change total runtime depth word read + _ = _
  have born_error : ‖SourceConditionalInventory.born (inventoryBound runtime) -
      decoder runtime depth word read (read (inventoryBound runtime + 1))‖ ^ 2 =
      ‖SourceGWordInverse.residual depth word (SourceConditionalInventory.born (inventoryBound runtime))‖ ^ 2 +
        ‖project depth word (SourceConditionalInventory.born (inventoryBound runtime)) -
          decoder runtime depth word read (read (inventoryBound runtime + 1))‖ ^ 2 := by
    change ‖SourceConditionalInventory.born (inventoryBound runtime) - SourceCompiledGWord.effect depth word
      (SourceGWordInverse.recover depth word
        (SourceConditionalNativePosterior.decoder runtime read (read (inventoryBound runtime + 1)) ))‖ ^ 2 = _
    rw [SourceInverseDistributionOptimal.error_decomposition, map_sub]
    rfl
  rw [born_error, minimum_update, increment, penalty]
  have nonzero : ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1 : ℝ) + 1 ≠ 0 := by
    positivity
  field_simp
  ring

omit [DecidableEq Key] in
theorem project_clock (depth : Nat) (word : List (Fock.Letter depth)) (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (project depth word value) = SourceJointClockGraph.clock value := by
  change SourceJointClockGraph.clock (SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word value)) = _
  rw [SourceInverseDistributionOptimal.roundtrip]
  rfl

omit [DecidableEq Key] in
theorem actor_clock (bound : Nat) (actor : Fin (bound + 1)) :
    SourceJointClockGraph.clock (SourceConditionalInventory.values bound actor) = ((actor.val + 2 : Nat) : ℂ) := by
  rw [← SourceConditionalWordStream.source_read, SourceConditionalWordStream.source_single,
    SourceJointClockGraph.clock_source, SourceClockComplex.clock_single]
  norm_num [SourceClockModel.rawClock]
  ring

omit [DecidableEq Key] in
theorem born_clock (bound : Nat) :
    SourceJointClockGraph.clock (SourceConditionalInventory.born bound) = ((bound + 3 : Nat) : ℂ) := by
  exact actor_clock (bound + 1) (Fin.last (bound + 1))

end
end SourceInverseDistributionStale
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
