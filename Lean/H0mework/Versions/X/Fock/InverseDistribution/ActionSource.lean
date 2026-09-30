import H0mework.Fock.InverseDistribution.ActionNative
import H0mework.Versions.X.Fock.HistoryConditional.NativeInverseSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionAction

theorem execute_cons (letter : Option Nat) (word : List (Option Nat)) (state : Nat) :
    SourceCopyWordAffine.execute (SourceCopyWordAffine.compile (letter :: word)) state =
      SourceCopyWordAffine.execute (SourceCopyWordAffine.compile word)
        (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile [letter]) state) := by
  rw [SourceCopyWordAffine.execute_original, SourceCopyWordAffine.execute_original, SourceCopyWordAffine.execute_original]
  rfl

theorem decode_cons (letter : Option Nat) (word : List (Option Nat)) (target : Nat) :
    SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile (letter :: word)) target =
      (SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile word) target).bind
        (SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile [letter])) := by
  cases old : SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile word) target with
  | none =>
    simp only [Option.bind_none]
    apply (SourceNativeProgramInverse.decode_none_iff _ (SourceCompiledWordOperator.slope_positive _) target).mpr
    rintro ⟨state, generated⟩
    have existed := (SourceNativeProgramInverse.decode_some_iff _ (SourceCompiledWordOperator.slope_positive word) target
      (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile [letter]) state)).mpr
        ((execute_cons letter word state).symm.trans generated)
    rw [old] at existed
    cases existed
  | some middle =>
    simp only [Option.bind_some]
    cases next : SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile [letter]) middle with
    | none =>
      apply (SourceNativeProgramInverse.decode_none_iff _ (SourceCompiledWordOperator.slope_positive _) target).mpr
      rintro ⟨state, generated⟩
      have existed := (SourceNativeProgramInverse.decode_some_iff _ (SourceCompiledWordOperator.slope_positive word) target
        (SourceCopyWordAffine.execute (SourceCopyWordAffine.compile [letter]) state)).mpr
          ((execute_cons letter word state).symm.trans generated)
      rw [old] at existed
      rw [Option.some.inj existed, SourceNativeProgramInverse.decode_execute _ (SourceCompiledWordOperator.slope_positive _)] at next
      cases next
    | some state =>
      apply (SourceNativeProgramInverse.decode_some_iff _ (SourceCompiledWordOperator.slope_positive _) target state).mpr
      rw [execute_cons,
        (SourceNativeProgramInverse.decode_some_iff _ (SourceCompiledWordOperator.slope_positive _) middle state).mp next,
        (SourceNativeProgramInverse.decode_some_iff _ (SourceCompiledWordOperator.slope_positive _) target middle).mp old]

theorem refine_split (letter : Option Nat) (word : List (Option Nat)) (target : Nat) (weight : ℚ) :
    refineEntry letter (SourceNativeInverseDistribution.splitEntry (SourceCopyWordAffine.compile word) target weight) =
      SourceNativeInverseDistribution.splitEntry (SourceCopyWordAffine.compile (letter :: word)) target weight := by
  unfold SourceNativeInverseDistribution.splitEntry
  rw [decode_cons]
  cases old : SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile word) target with
  | none => rfl
  | some middle =>
    simp only [refineEntry, SourceNativeInverseDistribution.splitEntry, Option.bind_some]
    cases next : SourceNativeProgramInverse.decode (SourceCopyWordAffine.compile [letter]) middle <;>
      simp only [zero_add]

end SourceInverseDistributionAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
