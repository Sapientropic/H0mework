import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime

/-! The programme's sealed macro state reads the original physical source
family. Private engine elimination recovers its already generated registry
coordinate; neither the activation nor a future environment is reconstructed. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
open RootInquiryCompletion SourceOperationEffects
namespace D
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (process runtime frames actual_node actual_next actual_query actual_answer)
end D
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (initial : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable (configuration : A.Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

def rawSource (state : (D.runtime initial configuration).State) :
    Context.RawAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
      (D.runtime initial configuration) state := by
  rcases state with ⟨⟨count⟩, activation⟩
  exact rawRestriction (D.frames initial configuration count.down) configuration

private def index (engine : Engine (D.process initial configuration)) : Nat := by
  rcases engine with ⟨count⟩
  exact count.down

private theorem raw_state (state : (D.runtime initial configuration).State) :
    Context.raw (D.runtime initial configuration) (rawSource initial configuration) state =
      (D.frames initial configuration (index initial configuration state.engine)).rawRead := by
  rcases state with ⟨⟨count⟩, activation⟩
  exact raw_restriction (D.frames initial configuration count.down) configuration

theorem raw_actual (count : Nat) :
    Context.raw (D.runtime initial configuration) (rawSource initial configuration)
      ((D.runtime initial configuration).stateAt count) =
        (D.frames initial configuration count).rawRead := by
  have indexEq : index initial configuration ((D.runtime initial configuration).stateAt count).engine = count := by
    have same := D.actual_node initial configuration count
    generalize engineEq : ((D.runtime initial configuration).stateAt count).engine = engine at same ⊢
    rcases engine with ⟨hidden⟩
    have hiddenEq : hidden = ULift.up count := (D.process initial configuration).erase_injective rfl rfl
      (congrArg RootInquiryProcessNode.erase same)
    subst hidden
    rfl
  exact (raw_state initial configuration _).trans
    (congrArg (fun count => (D.frames initial configuration count).rawRead) indexEq)

theorem environment_actual (count : Nat) :
    Context.readEnv (D.runtime initial configuration) (rawSource initial configuration)
      ((D.runtime initial configuration).stateAt count) =
        (D.frames initial configuration count).rawRead.environment :=
  congrArg (fun raw => raw.environment) (raw_actual initial configuration count)

theorem increment_actual (count : Nat) :
    Context.increment (D.runtime initial configuration) (rawSource initial configuration)
      ((D.runtime initial configuration).stateAt count) =
        (D.frames initial configuration (count + 1)).rawRead.environment -
          (D.frames initial configuration count).rawRead.environment := by
  change Context.readEnv (D.runtime initial configuration) (rawSource initial configuration)
    ((D.runtime initial configuration).stateAt (count + 1)) -
      Context.readEnv (D.runtime initial configuration) (rawSource initial configuration)
        ((D.runtime initial configuration).stateAt count) = _
  rw [environment_actual, environment_actual]

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
