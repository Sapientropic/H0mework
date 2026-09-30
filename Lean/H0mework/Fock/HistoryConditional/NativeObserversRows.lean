import H0mework.Fock.HistoryConditional.NativeObserversSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeObservers

theorem generated_outside {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (key : Key)
    (outside : ∀ index : Fin (bound + 1), key ≠ read index.val) :
    generate read bound key = (0, fun _ => 0) := by
  induction bound with
  | zero => exact if_neg (outside 0)
  | succ bound previous =>
      have lastAbsent : key ≠ read (bound + 1) := outside (Fin.last (bound + 1))
      rw [generated_next, advance, if_neg lastAbsent,
        previous (fun index => outside index.castSucc)]
      apply Prod.ext
      · rfl
      funext index
      refine Fin.lastCases ?_ (fun retained => ?_) index <;> simp

theorem generated_injective {Key : Type*} [DecidableEq Key] (read : Nat → Key)
    (injective : Function.Injective read) (bound : Nat) (actor : Fin (bound + 1)) :
    generate read bound (read actor.val) = (1, fun candidate => if candidate = actor then 1 else 0) := by
  induction bound with
  | zero =>
      change seed read (read actor.val) = _
      have actorZero : actor.val = 0 := by omega
      rw [seed, actorZero, if_pos rfl]
      apply Prod.ext
      · rfl
      funext candidate
      exact (if_pos (Fin.ext (by omega))).symm
  | succ bound previous =>
      refine Fin.lastCases ?_ (fun actor => ?_) actor
      · have fresh : ∀ index : Fin (bound + 1), read (bound + 1) ≠ read index.val := by
          intro index same
          have := injective same
          omega
        rw [generated_next, advance]
        simp only [Fin.val_last, ite_true, generated_outside read bound _ fresh]
        apply Prod.ext (by rfl)
        funext candidate
        refine Fin.lastCases ?_ (fun retained => ?_) candidate
        · simp
        · simp
      · have distinct : read actor.val ≠ read (bound + 1) := by
          intro same
          have := injective same
          omega
        rw [generated_next, advance]
        simp only [Fin.val_castSucc, if_neg distinct, previous actor]
        apply Prod.ext
        · rfl
        funext candidate
        refine Fin.lastCases ?_ (fun retained => ?_) candidate
        · simp only [Fin.lastCases_last]
          rw [if_neg (by intro same; have := congrArg Fin.val same; simp only [Fin.val_last, Fin.val_castSucc] at this; omega)]
        · simp

end SourceConditionalNativeObservers
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
