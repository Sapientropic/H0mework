import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime

set_option autoImplicit false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment

open SourceOperationEffects
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {frame : M.Frame (Value := Value) (Var := Var) (sort := sort)}
variable {env : Env Value Var}
variable (configuration : Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

/-- This is a property of the supplied environment function, not of arbitrary frames. -/
def At (frame : M.Frame (Value := Value) (Var := Var) (sort := sort)) (env : Env Value Var) : Prop :=
  ∀ {current : frame.V.Current}
    (occurrence : frame.old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current),
      frame.environment occurrence = env

theorem active (same : At frame env) : frame.activeEnvironment = env := same _
theorem epoch (same : At frame env) : (Activation.epoch frame).activeEnvironment = env := same _
theorem rebase (same : At frame env) : At frame frame.activeEnvironment := by
  rw [active same]
  exact same
theorem mathNext (same : At frame env) : At frame.mathNext env := same

/-- Registration reads the old actual environment; the decoder separately supplies the new one. -/
theorem born_raw (frame : M.Frame (Value := Value) (Var := Var) (sort := sort)) :
    (nextBorn frame configuration).rawRead.environment = frame.activeEnvironment :=
  (nextBorn frame configuration).raw_environment.trans
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.request_environment
      frame.old frame.registered frame.packetAt frame.environment frame.depth)

theorem born_constant (same : At frame env) :
    At (nextBorn frame configuration) (nextBorn frame configuration).activeEnvironment := by
  cases selectedAt : (datum frame configuration).nextEnvironmentReadAt with
  | some read =>
      apply rebase (env := read (actualOccurrence frame) ((resultFace frame configuration).rootRead.2.2.1))
      intro current occurrence
      change (match (datum frame configuration).nextEnvironmentReadAt with
        | some read => read (actualOccurrence frame) ((resultFace frame configuration).rootRead.2.2.1)
        | none => _) = _
      rw [selectedAt]
  | none =>
      cases selected : (datum frame configuration).nextEnvironmentRead with
      | some read =>
          apply rebase (env := read ((resultFace frame configuration).rootRead.2.2.1))
          intro current occurrence
          change (match (datum frame configuration).nextEnvironmentReadAt with
            | some read => read (actualOccurrence frame) ((resultFace frame configuration).rootRead.2.2.1)
            | none => match (datum frame configuration).nextEnvironmentRead with
              | none => _
              | some read => read ((resultFace frame configuration).rootRead.2.2.1)) = _
          rw [selectedAt, selected]
      | none =>
          apply rebase (env := env)
          intro current occurrence
          change (match (datum frame configuration).nextEnvironmentReadAt with
            | some read => read (actualOccurrence frame) ((resultFace frame configuration).rootRead.2.2.1)
            | none => match (datum frame configuration).nextEnvironmentRead with
              | none => frame.environment _
              | some read => read ((resultFace frame configuration).rootRead.2.2.1)) = _
          rw [selectedAt, selected]
          exact same _

theorem frames_constant {initial : M.Frame (Value := Value) (Var := Var) (sort := sort)}
    (same : At initial env) (stage : Nat) :
    At (frames initial configuration stage) (frames initial configuration stage).activeEnvironment := by
  induction stage with
  | zero => exact rebase same
  | succ stage previous =>
      change At (next (frames initial configuration stage) configuration)
        (next (frames initial configuration stage) configuration).activeEnvironment
      unfold next
      cases (frames initial configuration stage).action with
      | inl settled => exact born_constant configuration previous
      | inr paid => exact rebase (mathNext previous)

end SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
