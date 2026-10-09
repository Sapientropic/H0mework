import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Births

open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (configuration : Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (initial : M.Frame (Value := Value) (Var := Var) (sort := sort))

/-- Stopping indices are read from receipts in the same existing history. -/
def startIndex : Nat → Nat
  | 0 => 0
  | ordinal + 1 =>
      startIndex ordinal + (receipt configuration initial (startIndex ordinal)).1 + 1
def birthIndex (ordinal : Nat) : Nat :=
  startIndex configuration initial ordinal +
    (receipt configuration initial (startIndex configuration initial ordinal)).1
theorem startIndex_succ (ordinal : Nat) : startIndex configuration initial (ordinal + 1) =
    birthIndex configuration initial ordinal + 1 := rfl
theorem birthIndex_succ (ordinal : Nat) : birthIndex configuration initial (ordinal + 1) =
    birthIndex configuration initial ordinal + 1 +
      (receipt configuration initial (birthIndex configuration initial ordinal + 1)).1 := rfl
theorem birthIndex_step (ordinal : Nat) :
    birthIndex configuration initial ordinal < birthIndex configuration initial (ordinal + 1) := by
  rw [birthIndex_succ]
  omega
theorem birthIndex_strictMono : StrictMono (birthIndex configuration initial) :=
  strictMono_nat_of_lt_succ (birthIndex_step configuration initial)
theorem ordinal_le (ordinal : Nat) : ordinal ≤ birthIndex configuration initial ordinal := by
  induction ordinal with
  | zero => exact Nat.zero_le _
  | succ ordinal previous =>
      have grows := birthIndex_step configuration initial ordinal
      omega
def cover (bound : Nat) : Σ ordinal : Nat, PLift (bound ≤ birthIndex configuration initial ordinal) :=
  ⟨bound, ⟨ordinal_le configuration initial bound⟩⟩
abbrev settled (ordinal : Nat) :
    SourceOperationExecutionDebt.Settlement (frames initial configuration (birthIndex configuration initial ordinal)).event.state :=
  (receipt configuration initial (startIndex configuration initial ordinal)).2.1
theorem actual_action (ordinal : Nat) :
    (frames initial configuration (birthIndex configuration initial ordinal)).action =
      .inl (settled configuration initial ordinal) :=
  (receipt configuration initial (startIndex configuration initial ordinal)).2.2.2
theorem actual_next (ordinal : Nat) : type_of%
    (receipt_next configuration initial (startIndex configuration initial ordinal)) :=
  receipt_next configuration initial (startIndex configuration initial ordinal)
theorem actual_compiles (ordinal : Nat) : type_of%
    (receipt_compiles configuration initial (startIndex configuration initial ordinal)) :=
  receipt_compiles configuration initial (startIndex configuration initial ordinal)


end SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Births
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
