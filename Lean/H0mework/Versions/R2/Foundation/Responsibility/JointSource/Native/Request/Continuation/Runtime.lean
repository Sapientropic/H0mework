import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Continuation.Policy
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Continuation.Inventory

/-! Source-recursive frames form the registry of the existing macro engine.
Its actual tick generates the next frame and its unique activation; the
registry index carries no occurrence authority. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Continuation

open SourceOperationEffects RootInquiryCompletion

noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (initial : Frame (Value := Value) (Var := Var) (sort := sort))

def inquiryProcess : SourceNativeInquiryEngineProcess.{u} where
  State := ULift.{u} Nat
  stateAt := fun count => .active (frames initial count.down).presentation
  erase_injective := by
    intro first second firstState secondState firstActive secondActive same
    cases firstActive
    cases secondActive
    exact congrArg ULift.up (frames_erase_injective initial same)
  initial := .up 0
  successorAt := fun count query =>
    ⟨.up (count.down + 1), (frames initial count.down).successor_valid query⟩

def nextQuery (count : (inquiryProcess initial).State)
    (_query : ((inquiryProcess initial).stateAt count).Query) :
    ((inquiryProcess initial).stateAt ⟨count.down + 1⟩).Query :=
  (frames initial (count.down + 1)).query

def runtime : SourceNativeInquiryRuntime (inquiryProcess initial) where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    initial.query (fun candidate => initial.query_unique candidate)
    (nextQuery initial)
    (fun count _query candidate => (frames initial (count.down + 1)).query_unique candidate)

private theorem next_node (count : Nat) (engine : Engine (inquiryProcess initial))
    (same : engine.node = .active (frames initial count).presentation)
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    (engine.ask activation).next.node = .active (frames initial (count + 1)).presentation := by
  rcases engine with ⟨state⟩
  have stateEq : state = .up count := (inquiryProcess initial).erase_injective rfl rfl
    (congrArg RootInquiryProcessNode.erase same)
  subst state
  rfl

theorem actual_node (count : Nat) :
    ((runtime initial).stateAt count).engine.node = .active (frames initial count).presentation := by
  induction count with
  | zero => rfl
  | succ count prior =>
      exact next_node initial count ((runtime initial).stateAt count).engine prior
        ((runtime initial).stateAt count).activation

theorem actual_current (count : Nat) : ((runtime initial).stateAt count).engine.node.erase =
    (frames initial count).currentPresentation.erase :=
  (congrArg RootInquiryProcessNode.erase (actual_node initial count)).trans
    (frames initial count).presentation_erase

theorem macro_next (count : Nat) :
    ((runtime initial).tickAt count).next.node = .active (frames initial (count + 1)).presentation :=
  actual_node initial (count + 1)

theorem macro_next_preserves (count : Nat) :
    ((runtime initial).stateAt count).engine.node.PreservesGeneratedLivingLawAt
      ((runtime initial).stateAt count).activation.query
      ((runtime initial).tickAt count).next.node :=
  ((runtime initial).tickAt count).next_preservesGeneratedLivingLaw

end
end RootGeneratedDebtActivationJointSource.Native.Request.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
