import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Feedback
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Words
import H0mework.Realization.ObservationActions.Algebraic
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace Lower.SourceFamily.Foresight.Tail
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
local instance tailGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
abbrev State := Sigma (Lower.SourceFamily.Packet (W := W) (X := X) (s := s))
variable (binding : ∀ t, X t → Expr W X t)
def advance (state : State (W := W) (X := X) (s := s)) : State (W := W) (X := X) (s := s) :=
  ⟨state.1 + 1, Lower.SourceFamily.step (Lower.SourceFamily.Replay.factory (s := s) binding) state.1 state.2⟩
def tail (state : State (W := W) (X := X) (s := s)) (k : Nat) : State (W := W) (X := X) (s := s) :=
  Nat.rec state (fun _ prior => advance binding prior) k
@[simp] theorem tail_zero (state : State (W := W) (X := X) (s := s)) : tail binding state 0 = state := rfl
@[simp] theorem tail_succ (state : State (W := W) (X := X) (s := s)) (k : Nat) :
  tail binding state (k + 1) = advance binding (tail binding state k) := rfl
theorem tail_index (state : State (W := W) (X := X) (s := s)) (k : Nat) :
  (tail binding state k).1 = state.1 + k := by
  induction k with
  | zero => rfl
  | succ k prior => exact congrArg (· + 1) prior
theorem tail_after_actual_step (state : State (W := W) (X := X) (s := s)) (k : Nat) :
  tail binding (advance binding state) k = tail binding state (k + 1) := by
  induction k with
  | zero => rfl
  | succ k prior => exact congrArg (advance binding) prior
@[simp] theorem advanced_depth (state : State (W := W) (X := X) (s := s)) :
  (advance binding state).2.1.depth = 0 := rfl
theorem cast_depth {Y Z : S → Type u} (same : Y = Z) (n : Nat)
    (data : Lower.SourceFamily.Packet (W := W) (X := Y) (s := s) n) :
    (same ▸ data : Lower.SourceFamily.Packet (W := W) (X := Z) (s := s) n).1.depth = data.1.depth := by
  cases same
  rfl
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (firstCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : firstCfg.LowVar = X)
abbrev global (n : Nat) := Lower.SourceFamily.tailData (Lower.SourceFamily.Replay.factory (s := s) binding) initial firstCfg language n
theorem exact_actual_tail (n k : Nat) :
  tail binding ⟨n + 1, global binding initial firstCfg language n⟩ k =
    ⟨n + k + 1, global binding initial firstCfg language (n + k)⟩ := by
  induction k with
  | zero => rfl
  | succ k prior =>
    change advance binding (tail binding ⟨n + 1, global binding initial firstCfg language n⟩ k) = _
    rw [prior]
    rfl
@[simp] theorem native_depth (n : Nat) : (global binding initial firstCfg language n).1.depth = 0 := by
  cases n with
  | zero =>
      exact (cast_depth language 1
        (⟨Lower.Stock.receiver initial firstCfg language, Lower.Stock.seed initial firstCfg language⟩ :
          Lower.SourceFamily.Packet (W := W) (X := firstCfg.LowVar) (s := s) 1)).trans rfl
  | succ _ => rfl
end Lower.SourceFamily.Foresight.Tail
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
