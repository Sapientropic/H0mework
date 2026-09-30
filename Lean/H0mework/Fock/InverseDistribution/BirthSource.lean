import H0mework.Fock.InverseDistribution.BirthNative
import Mathlib.Data.Rat.Lemmas

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionBirth

theorem scale_split (scale : ℚ) (program : Nat × Nat) (target : Nat) (weight : ℚ) :
    scaleEntry scale (SourceNativeInverseDistribution.splitEntry program target weight) =
      SourceNativeInverseDistribution.splitEntry program target (scale * weight) := by
  cases computed : SourceNativeProgramInverse.decode program target <;>
    simp only [scaleEntry, SourceNativeInverseDistribution.splitEntry, computed, Option.map_none, Option.map_some, mul_zero]

theorem advance_source {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat)
    (previous : SourceConditionalNativeObservers.State Key bound) :
    advance read bound program (fun key => (previous key).1)
      (fun key => SourceNativeInverseDistribution.split bound program (previous key).2) =
        fun key => SourceNativeInverseDistribution.split (bound + 1) program
          (SourceConditionalNativeObservers.advance read bound previous key).2 := by
  funext key actor
  by_cases selected : key = read (bound + 1)
  · simp only [advance, selected, if_true, SourceConditionalNativeObservers.advance]
    refine Fin.lastCases ?_ (fun earlier => ?_) actor
    · simp only [Fin.lastCases_last, SourceNativeInverseDistribution.split]
      rfl
    · simp only [Fin.lastCases_castSucc, Fin.val_castSucc, SourceNativeInverseDistribution.split, scale_split]
  · simp only [advance, selected, if_false, SourceConditionalNativeObservers.advance]
    refine Fin.lastCases ?_ (fun earlier => ?_) actor
    · simp only [Fin.lastCases_last, SourceNativeInverseDistribution.split]
      rfl
    · simp only [Fin.lastCases_castSucc, Fin.val_castSucc, SourceNativeInverseDistribution.split]

theorem generated_next {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat) :
    advance read bound program (fun key => (SourceConditionalNativeObservers.generate read bound key).1)
      (fun key => SourceNativeInverseDistribution.split bound program (SourceConditionalNativeObservers.generate read bound key).2) =
        fun key => SourceNativeInverseDistribution.split (bound + 1) program
          (SourceConditionalNativeObservers.generate read (bound + 1) key).2 := by
  rw [advance_source, ← SourceConditionalNativeObservers.generated_next]

end SourceInverseDistributionBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
