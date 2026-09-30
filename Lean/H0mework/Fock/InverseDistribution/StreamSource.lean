import H0mework.Fock.InverseDistribution.StreamNative
import H0mework.Fock.InverseDistribution.BirthSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionStream

theorem weight_split (program : Nat × Nat) (target : Nat) (value : ℚ) :
    weight (SourceNativeInverseDistribution.splitEntry program target value) = value := by
  cases computed : SourceNativeProgramInverse.decode program target <;>
    simp only [weight, SourceNativeInverseDistribution.splitEntry, computed, Option.map_none,
      Option.map_some, Option.getD_none, Option.getD_some, zero_add, add_zero]

theorem source_split {Key : Type*} (bound : Nat) (program : Nat × Nat)
    (previous : SourceConditionalNativeObservers.State Key bound) :
    source bound (fun key => ((previous key).1, SourceNativeInverseDistribution.split bound program (previous key).2)) = previous := by
  funext key
  apply Prod.ext
  · rfl
  · funext actor
    exact weight_split program (actor.val + 1) _

theorem step_source {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat)
    (previous : SourceConditionalNativeObservers.State Key bound) :
    step read bound program
      (fun key => ((previous key).1, SourceNativeInverseDistribution.split bound program (previous key).2)) =
      fun key => ((SourceConditionalNativeObservers.advance read bound previous key).1,
        SourceNativeInverseDistribution.split (bound + 1) program (SourceConditionalNativeObservers.advance read bound previous key).2) := by
  dsimp only [step]
  rw [source_split, SourceInverseDistributionBirth.advance_source]

theorem generated_source {Key : Type*} [DecidableEq Key] (read : Nat → Key) (program : Nat × Nat) (bound : Nat) :
    generate read program bound =
      fun key => ((SourceConditionalNativeObservers.generate read bound key).1,
        SourceNativeInverseDistribution.split bound program (SourceConditionalNativeObservers.generate read bound key).2) := by
  induction bound with
  | zero => rfl
  | succ bound previous =>
    rw [generated_next, previous, step_source, ← SourceConditionalNativeObservers.generated_next]

theorem source_generated {Key : Type*} [DecidableEq Key] (read : Nat → Key) (program : Nat × Nat) (bound : Nat) :
    source bound (generate read program bound) = SourceConditionalNativeObservers.generate read bound := by
  rw [generated_source, source_split]

end SourceInverseDistributionStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
