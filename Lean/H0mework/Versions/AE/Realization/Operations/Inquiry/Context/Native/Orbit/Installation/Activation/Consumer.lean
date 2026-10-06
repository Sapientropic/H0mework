import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Runtime

/-! Actual activated answers consume the complete orbit relation programme.
The same material face retains its typed old/next data and source certificate. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (resultFace resultAt baseRoot datum actualOccurrence compiles_paid compiles_settled targetAt target_root target_next)
end S
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (source_value source_history)
end O
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

theorem material_generated : (materialFace frame).rootRead =
    materialAt (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
      (S.actualOccurrence frame) := rfl

theorem actual_value : (S.resultFace frame programme).rootRead.2.2.1 =
    updateInventory (R := ℤ) (ofFrame frame).orbitEnvironment
      ((ofFrame frame).next.orbitEnvironment - (ofFrame frame).orbitEnvironment)
      (Relations.word (ofFrame frame)) := by
  apply (O.source_value (S.baseRoot frame programme).toAuthoritativeRoot
    ((S.datum frame programme).reader) (S.actualOccurrence frame)).trans
  exact Relations.pair_eval (ofFrame frame)

theorem actual_history : (S.resultFace frame programme).rootRead.2.1.2.length =
    remaining (S.query frame programme).raw.expression :=
  O.source_history (S.baseRoot frame programme).toAuthoritativeRoot
    ((S.datum frame programme).reader) (S.actualOccurrence frame)

def complex := SourceSubstitution.complexMorphism (R := ℤ) (s := sort) Orbit.binding
  (materialFace frame).rootRead.environment

theorem complex_generated : complex frame = Relations.complex (ofFrame frame) := rfl

variable (initial : A.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

theorem actual_tick (count : Nat) :
    HEq ((runtime initial).tickAt count).answer
      ((S.state (frames initial count) programme).compileInquiry
        (S.query (frames initial count) programme)).answerReadout ∧
    ((runtime initial).tickAt count).next.node =
      .active (S.presentation (frames initial (count + 1)) programme) :=
  ⟨actual_answer initial count, actual_next initial count⟩

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
