import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Births
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyBirthControls
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme M.Frame)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (next frames runtime presentation nextBorn)
end A
namespace B
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Births
  (birthIndex birthIndex_strictMono cover actual_action actual_next actual_compiles)
end B
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
  (rawSource character_source_read actual_source_receipt environment_actual stage_actual)
end O
open B
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (configuration : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (initial : A.M.Frame (Value := Value) (Var := Var) (sort := sort))

/-- The generated cover reads the entire prefix, including any intermediate tick. -/
theorem covered_tick_read (tick : Nat)
    (word : SourceOperationScalarRelations.Formal ℤ Value Var sort) :
    let generated := cover configuration initial tick
    let index : Fin (birthIndex configuration initial generated.1 + 1) :=
      ⟨tick, Nat.lt_succ_of_le generated.2.down⟩
    type_of% (O.character_source_read initial configuration 0
      (birthIndex configuration initial generated.1) word index) :=
  O.character_source_read initial configuration 0
    (birthIndex configuration initial (cover configuration initial tick).1) word
    ⟨tick, Nat.lt_succ_of_le (cover configuration initial tick).2.down⟩

/-- Source observations can be generated strictly after any supplied bound. -/
def cover_after (bound : Nat) : Σ ordinal : Nat, PLift (bound < birthIndex configuration initial ordinal) :=
  let generated := cover configuration initial (bound + 1)
  ⟨generated.1, ⟨lt_of_lt_of_le (Nat.lt_succ_self bound) generated.2.down⟩⟩

theorem actual_birth_receipt (ordinal : Nat) : type_of%
    (O.actual_source_receipt initial configuration (birthIndex configuration initial ordinal)) :=
  O.actual_source_receipt initial configuration (birthIndex configuration initial ordinal)

theorem born_raw_environment
    (frame : A.M.Frame (Value := Value) (Var := Var) (sort := sort)) :
    (A.nextBorn frame configuration).rawRead.environment = frame.activeEnvironment :=
  (A.nextBorn frame configuration).raw_environment.trans
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.request_environment
      frame.old frame.registered frame.packetAt frame.environment frame.depth)
theorem birth_raw_environment (ordinal : Nat) :
    (A.frames initial configuration (birthIndex configuration initial ordinal + 1)).rawRead.environment =
      (A.frames initial configuration (birthIndex configuration initial ordinal)).activeEnvironment := by
  have same : A.frames initial configuration (birthIndex configuration initial ordinal + 1) =
      A.nextBorn (A.frames initial configuration (birthIndex configuration initial ordinal)) configuration := by
    change A.next (A.frames initial configuration (birthIndex configuration initial ordinal)) configuration = _
    unfold A.next
    rw [actual_action]
  rw [same]
  exact born_raw_environment configuration _
theorem observed_after_birth (ordinal : Nat) :
    SourceOperationInquiry.Context.readEnv (A.runtime initial configuration) (O.rawSource initial configuration)
      ((A.runtime initial configuration).stateAt (birthIndex configuration initial ordinal + 1)) =
      (A.frames initial configuration (birthIndex configuration initial ordinal)).activeEnvironment :=
  (O.environment_actual initial configuration (birthIndex configuration initial ordinal + 1)).trans
    (birth_raw_environment configuration initial ordinal)
theorem birth_stage_delta (ordinal : Nat) :
    SourceOperationInquiry.Context.History.stageInventory (A.runtime initial configuration)
      (O.rawSource initial configuration) (birthIndex configuration initial ordinal) =
      SourceOperationScalarRelations.updateInventory (R := ℤ)
        (A.frames initial configuration (birthIndex configuration initial ordinal)).rawRead.environment
        ((A.frames initial configuration (birthIndex configuration initial ordinal)).activeEnvironment -
          (A.frames initial configuration (birthIndex configuration initial ordinal)).rawRead.environment) := by
  rw [O.stage_actual, birth_raw_environment]
#print axioms birthIndex_strictMono
#print axioms cover_after
#print axioms actual_action
#print axioms actual_next
#print axioms actual_compiles
#print axioms covered_tick_read
#print axioms actual_birth_receipt
#print axioms born_raw_environment
#print axioms observed_after_birth
#print axioms birth_stage_delta
end SourcePolicyBirthControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
