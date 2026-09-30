import H0mework.Fock.HistoryConditional.WordAffineNative
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyWordAffine

theorem equation (word : List (Option Nat)) (state : Nat) :
    SourceCopyNativeWord.run word state + 1 = (compile word).1 * (state + 1) + (compile word).2 := by
  induction word generalizing state with
  | nil => simp [SourceCopyNativeWord.run, compile]
  | cons letter rest previous =>
      change SourceCopyNativeWord.run rest (SourceCopyNativeWord.step letter state) + 1 = _
      rw [previous]
      cases letter with
      | none =>
          simp only [compile, List.foldr_cons, SourceCopyNativeWord.step]
          ring
      | some materialIndex =>
          have positive : 1 ≤ (state + 1) * (materialIndex + 1) :=
            Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos state) (Nat.succ_pos materialIndex))
          simp only [compile, List.foldr_cons, SourceCopyNativeWord.step, Nat.sub_add_cancel positive]
          ring

theorem execute_original (word : List (Option Nat)) (state : Nat) :
    execute (compile word) state = SourceCopyNativeWord.run word state := by
  rw [execute, ← equation]
  omega

theorem action_kernel (left right : List (Option Nat)) :
    compile left = compile right ↔ ∀ state, SourceCopyNativeWord.run left state = SourceCopyNativeWord.run right state := by
  constructor
  · intro same state
    rw [← execute_original, ← execute_original, same]
  · intro same
    have first := congrArg (fun value : Nat => value + 1) (same 0)
    have second := congrArg (fun value : Nat => value + 1) (same 1)
    rw [equation, equation] at first second
    simp only [Nat.zero_add, Nat.mul_one, Nat.reduceAdd] at first second
    apply Prod.ext <;> omega

end SourceCopyWordAffine
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
