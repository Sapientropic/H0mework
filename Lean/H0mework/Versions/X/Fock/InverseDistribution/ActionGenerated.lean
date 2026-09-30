import H0mework.Versions.X.Fock.InverseDistribution.ActionSource
import H0mework.Fock.InverseDistribution.StreamSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionAction

theorem refine_generated {Key : Type*} [DecidableEq Key] (read : Nat → Key) (letter : Option Nat)
    (word : List (Option Nat)) (bound : Nat) :
    refine bound letter (SourceInverseDistributionStream.generate read (SourceCopyWordAffine.compile word) bound) =
      SourceInverseDistributionStream.generate read (SourceCopyWordAffine.compile (letter :: word)) bound := by
  rw [SourceInverseDistributionStream.generated_source, SourceInverseDistributionStream.generated_source]
  funext key
  apply Prod.ext
  · rfl
  · funext actor
    exact refine_split letter word (actor.val + 1) _

theorem generated_source {Key : Type*} [DecidableEq Key] (read : Nat → Key) (word : List (Option Nat)) (bound : Nat) :
    generate read word bound = SourceInverseDistributionStream.generate read (SourceCopyWordAffine.compile word) bound := by
  induction word with
  | nil => rfl
  | cons letter word previous =>
    change refine bound letter (generate read word bound) = _
    rw [previous, refine_generated]

theorem source_generated {Key : Type*} [DecidableEq Key] (read : Nat → Key) (word : List (Option Nat)) (bound : Nat) :
    SourceInverseDistributionStream.source bound (generate read word bound) = SourceConditionalNativeObservers.generate read bound := by
  rw [generated_source, SourceInverseDistributionStream.source_generated]

theorem shift_root_residual (weight remainder : ℚ) :
    refineEntry none (some (0, weight), remainder) = (none, remainder + weight) := rfl

end SourceInverseDistributionAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
