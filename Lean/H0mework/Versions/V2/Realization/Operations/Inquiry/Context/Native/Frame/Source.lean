import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Frame
open SourceOperationEffects RootInquiryCompletion
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (frames process runtime actual_node frames_erase_injective next)
end A
namespace I
export SourceOperationInquiry (Carrier point sourceAction)
end I
namespace Q
export SourceOperationInquiry.Context
  (actions completeRead completionPoint completionAction readCompletion read_completion_point
   actual_completion_action completionPoint_injective)
end Q
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
abbrev SourceFrame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Value) (Var := Var) (sort := sort)
variable (initial : SourceFrame (Value := Value) (Var := Var) (sort := sort))
variable (configuration : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

def read (state : (A.runtime initial configuration).State) :
    SourceFrame (Value := Value) (Var := Var) (sort := sort) := by
  rcases state with ⟨⟨registered⟩, activation⟩
  exact A.frames initial configuration registered.down

theorem actual (stage : Nat) : read initial configuration ((A.runtime initial configuration).stateAt stage) =
    A.frames initial configuration stage := by
  have node := A.actual_node initial configuration stage
  generalize stateEq : (A.runtime initial configuration).stateAt stage = state at node ⊢
  rcases state with ⟨⟨registered⟩, activation⟩
  have registeredEq : registered = ULift.up stage :=
    (A.process initial configuration).erase_injective rfl rfl (congrArg RootInquiryProcessNode.erase node)
  subst registered
  rfl

/-- Restrict the existing complete sealed source to its original full Frame. -/
def observer : I.Carrier (A.runtime initial configuration) →ₗ[ℤ]
    (SourceFrame (Value := Value) (Var := Var) (sort := sort) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun state => Finsupp.single (read initial configuration state) 1)

theorem fullword_read (word : I.Carrier (A.runtime initial configuration)) :
    Q.readCompletion (A.runtime initial configuration)
      (SourceGeneratedActionObservationHistory.sourceMap
        (I.sourceAction (A.runtime initial configuration))
        (SourceGeneratedActionWords.inventory (Q.actions (A.runtime initial configuration))
          (Q.completeRead (A.runtime initial configuration))) word) = word :=
  SourceGeneratedActionWords.complete_read_source (Q.actions (A.runtime initial configuration))
    (Q.completeRead (A.runtime initial configuration)) PUnit.unit [] word

theorem model_read (stage : Nat) :
    observer initial configuration (Q.readCompletion (A.runtime initial configuration)
      (Q.completionPoint (A.runtime initial configuration) ((A.runtime initial configuration).stateAt stage))) =
        Finsupp.single (A.frames initial configuration stage) 1 := by
  rw [Q.read_completion_point]
  simp only [observer, I.point, SourceOwnedObservationHistory.sourcePoint,
    Finsupp.linearCombination_single, one_smul]
  exact congrArg (fun frame => Finsupp.single frame (1 : ℤ)) (actual initial configuration stage)

theorem model_next (stage : Nat) :
    observer initial configuration (Q.readCompletion (A.runtime initial configuration)
      (Q.completionAction (A.runtime initial configuration)
        (Q.completionPoint (A.runtime initial configuration) ((A.runtime initial configuration).stateAt stage)))) =
        Finsupp.single (A.frames initial configuration (stage + 1)) 1 := by
  rw [Q.actual_completion_action]
  exact model_read initial configuration (stage + 1)

theorem model_stage_injective {first second : Nat}
    (same : Q.completionPoint (A.runtime initial configuration) ((A.runtime initial configuration).stateAt first) =
      Q.completionPoint (A.runtime initial configuration) ((A.runtime initial configuration).stateAt second)) : first = second := by
  have states := Q.completionPoint_injective (A.runtime initial configuration) same
  have nodes := congrArg (fun state : (A.runtime initial configuration).State => state.engine.node) states
  rw [A.actual_node, A.actual_node] at nodes
  exact A.frames_erase_injective initial configuration (congrArg RootInquiryProcessNode.erase nodes)

theorem model_ne_next (stage : Nat) :
    Q.completionPoint (A.runtime initial configuration) ((A.runtime initial configuration).stateAt stage) ≠
      Q.completionPoint (A.runtime initial configuration) ((A.runtime initial configuration).stateAt (stage + 1)) := by
  intro same
  have indices := model_stage_injective initial configuration same
  omega

theorem inventory_next (stage : Nat) :
    (observer initial configuration (Q.readCompletion (A.runtime initial configuration)
      (Q.completionAction (A.runtime initial configuration)
        (Q.completionPoint (A.runtime initial configuration) ((A.runtime initial configuration).stateAt stage))))).mapDomain
      (fun frame => (frame.inventory, frame.pairInventory)) =
    Finsupp.single ((A.frames initial configuration (stage + 1)).inventory,
      (A.frames initial configuration (stage + 1)).pairInventory) 1 := by
  rw [model_next, Finsupp.mapDomain_single]

theorem paid_depth_next (stage : Nat)
    {paid : DebtActivationWorld.GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law
        (A.frames initial configuration stage).registered.input.environment
        (A.frames initial configuration stage).registered.input.expression)
      (A.frames initial configuration stage).event.state}
    (actual : (A.frames initial configuration stage).action = .inr paid) :
    (observer initial configuration (Q.readCompletion (A.runtime initial configuration)
      (Q.completionAction (A.runtime initial configuration)
        (Q.completionPoint (A.runtime initial configuration) ((A.runtime initial configuration).stateAt stage))))).mapDomain
      (fun frame => frame.depth) = Finsupp.single ((A.frames initial configuration stage).depth + 1) 1 := by
  rw [model_next, Finsupp.mapDomain_single]
  change Finsupp.single (A.next (A.frames initial configuration stage) configuration).depth 1 = _
  unfold A.next
  rw [actual]
  rfl

end SourceOperationInquiry.Context.Native.Frame
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
