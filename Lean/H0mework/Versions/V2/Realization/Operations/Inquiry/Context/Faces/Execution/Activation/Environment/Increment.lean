import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Environment
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Runtime

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.Increment
open SourceOperationEffects
variable {Sorts : Type u} {Value Var : Sorts → Type u}
 [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (configuration : Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

/-- The actual source action determines the raw registration delta. -/
theorem actual (initial : M.Frame (Value := Value) (Var := Var) (sort := sort)) (stage : Nat) :
    Context.increment (runtime initial configuration)
      (Context.Native.Orbit.Installation.Activation.Observation.rawSource initial configuration)
      ((runtime initial configuration).stateAt stage) =
      match (frames initial configuration stage).action with
      | .inl _ => (frames initial configuration stage).activeEnvironment -
          (frames initial configuration stage).rawRead.environment
      | .inr _ => 0 := by
  rw [Context.Native.Orbit.Installation.Activation.Observation.increment_actual]
  change (next (frames initial configuration stage) configuration).rawRead.environment -
    (frames initial configuration stage).rawRead.environment = _
  unfold next
  cases (frames initial configuration stage).action with
  | inl settled => rw [Environment.born_raw]
  | inr paid => exact sub_self _
end SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.Increment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
