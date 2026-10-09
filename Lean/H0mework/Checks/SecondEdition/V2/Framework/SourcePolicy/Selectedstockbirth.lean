import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Stock.Birth
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicySelectedStockBirthControls
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
namespace B
export SourceOperationInquiry.Context.Native.Frame.Stock.Birth
  (index current after generated target selected_action selected_compile after_birth macro_answer macro_next
   macro_next_current actual_root actual_complete_stock current_complete_stock macro_receipt)
end B
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (state query resultFace compiles_paid)
end A
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (programme)
end I
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (initial : SourceOperationInquiry.Context.Native.Frame.SourceFrame (Value := Value) (Var := Var) (sort := sort))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

theorem selected_macro_answer (ordinal : Nat) : type_of% (B.macro_answer initial configuration ordinal) :=
  B.macro_answer initial configuration ordinal
theorem selected_macro_current (ordinal : Nat) : type_of% (B.macro_next_current initial configuration ordinal) :=
  B.macro_next_current initial configuration ordinal
theorem selected_actual_stock (ordinal : Nat) : type_of% (B.actual_complete_stock initial configuration ordinal) :=
  B.actual_complete_stock initial configuration ordinal
theorem selected_current_stock (ordinal : Nat) : type_of% (B.current_complete_stock initial configuration ordinal) :=
  B.current_complete_stock initial configuration ordinal
def selected_receipt (ordinal : Nat) := B.macro_receipt initial configuration ordinal

theorem canonical_visit (ordinal : Nat) : type_of%
    ((B.target initial configuration ordinal).targetAnswerAndNext_next_eq) :=
  (B.target initial configuration ordinal).targetAnswerAndNext_next_eq
theorem initial_ne_first_next (ordinal : Nat) :
    (B.target initial configuration ordinal).targetInitialVisit.current ≠
      (B.target initial configuration ordinal).targetVisit.current := by
  let target := B.target initial configuration ordinal
  intro same
  have support := congrArg
    (fun current => target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (target.targetRoot.emitted current)) same
  change target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (target.targetRoot.emitted target.targetRoot.toAuthoritativeRoot.toRoot.source.initial) =
    target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      target.firstSuccessor.targetOccurrence at support
  have states := Option.some.inj (congrArg Prod.snd
    (target.initialSupport_eq.symm.trans (support.trans target.firstSupport_eq)))
  have strict := target.law.step_budget_lt target.stepEvent.step
  exact (Nat.ne_of_lt strict) (congrArg target.law.budget states).symm

theorem actual_paid_after_birth (ordinal : Nat) :
    ∃ paid, (B.after initial configuration ordinal).action = .inr paid := by
  rw [B.after_birth initial configuration ordinal]
  let frame := B.current initial configuration ordinal
  let born := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame (I.programme configuration)
  change ∃ paid, born.action = .inr paid
  have budget := SourceRegisteredClaimClock.remainder_generated born
  change remaining born.event.state.1 = remaining frame.request.input.expression - 1 at budget
  have growth := frame.request_budget
  have positive : 0 < remaining born.event.state.1 := by omega
  cases born.action with
  | inr paid => exact ⟨paid, rfl⟩
  | inl settled =>
      have zero : remaining born.event.state.1 = 0 := by rw [settled.2.down]; rfl
      omega
theorem actual_paid_compiler (ordinal : Nat) :
    (A.state (B.after initial configuration ordinal) (I.programme configuration)).compileInquiry
      (A.query (B.after initial configuration ordinal) (I.programme configuration)) =
      .answered (A.resultFace (B.after initial configuration ordinal) (I.programme configuration))
        (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumer
          (B.after initial configuration ordinal) (I.programme configuration)) := by
  rcases actual_paid_after_birth initial configuration ordinal with ⟨paid, actual⟩
  exact A.compiles_paid (B.after initial configuration ordinal) (I.programme configuration) paid actual

#print axioms B.selected_action
#print axioms B.selected_compile
#print axioms B.macro_next
#print axioms B.actual_root
#print axioms selected_macro_answer
#print axioms selected_macro_current
#print axioms selected_actual_stock
#print axioms selected_current_stock
#print axioms selected_receipt
#print axioms canonical_visit
#print axioms initial_ne_first_next
#print axioms actual_paid_after_birth
#print axioms actual_paid_compiler
end SourcePolicySelectedStockBirthControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
