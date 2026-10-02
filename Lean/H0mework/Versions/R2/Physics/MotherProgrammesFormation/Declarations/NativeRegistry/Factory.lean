import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeRegistry.Operations

/-! The complete original process is formed from source operations. Registry
and successor checks are internal; the State carrier is retained verbatim,
including every answered or otherwise nonactivated state. -/

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeRegistry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical

noncomputable section

structure Fields (material : Material) (index : Base) where
  nodes : State material index → Node
  initial : State material index
  next : (state : State material index) → Query (nodes state) → State material index

def formFields (material : Material) (index initial : Base) (nodesOperation nextOperation : Material) :
    Option (Fields material index) :=
  match MotherSubquotient.formMember material index initial with
  | none => none
  | some first =>
      match formNodes material index nodesOperation with
      | none => none
      | some nodes =>
          match formSuccessors material index nodes nextOperation with
          | none => none
          | some next => some ⟨nodes, first, next⟩

theorem every_fields {material : Material} {index : Base} (target : Fields material index) :
    ∃ initial : Base, ∃ nodesOperation nextOperation : Material,
      formFields material index initial nodesOperation nextOperation = some target := by
  cases target with
  | mk nodes first next =>
      obtain ⟨nodesOperation, _, nodesFormed⟩ := every_node_family material index nodes
      obtain ⟨nextOperation, _, nextFormed⟩ := every_successor_family material index nodes next
      refine ⟨MotherSubquotient.address material index first, nodesOperation, nextOperation, ?_⟩
      unfold formFields
      rw [MotherSubquotient.address_recovers]
      dsimp only
      rw [nodesFormed]
      dsimp only
      rw [nextFormed]

def ActiveInjective {material : Material} {index : Base} (fields : Fields material index) : Prop :=
  ∀ {left right : State material index} {leftState rightState : RootInquiryStatePresentation},
    view (fields.nodes left) = .active leftState →
    view (fields.nodes right) = .active rightState →
    leftState.erase = rightState.erase → left = right

def SuccessorCompatible {material : Material} {index : Base} (fields : Fields material index) : Prop :=
  ∀ state query,
    (view (fields.nodes (fields.next state query))).erase = nextCurrent (view (fields.nodes state)) query ∧
    (view (fields.nodes state)).PreservesGeneratedLivingLawAt query
      (view (fields.nodes (fields.next state query)))

def Admissible {material : Material} {index : Base} (fields : Fields material index) : Prop :=
  ActiveInjective fields ∧ SuccessorCompatible fields

def assemble {material : Material} {index : Base} (fields : Fields material index)
    (checked : Admissible fields) : SourceNativeInquiryEngineProcess where
  State := State material index
  stateAt := fun state => view (fields.nodes state)
  erase_injective := checked.1
  initial := fields.initial
  successorAt := by
    intro state query
    refine ⟨fields.next state query, ?_, (checked.2 state query).2⟩
    apply (checked.2 state query).1.trans
    generalize source_eq : view (fields.nodes state) = source at query ⊢
    cases source with
    | active prior => rfl
    | answered prior oldQuery => exact nomatch query

def formProcess (material : Material) (index initial : Base) (nodesOperation nextOperation : Material) :
    Option SourceNativeInquiryEngineProcess :=
  match formFields material index initial nodesOperation nextOperation with
  | none => none
  | some fields => if checked : Admissible fields then some (assemble fields checked) else none

theorem every_process {material : Material} {index : Base}
    (target : Fields material index) (checked : Admissible target) :
    ∃ initial : Base, ∃ nodesOperation nextOperation : Material,
      formProcess material index initial nodesOperation nextOperation = some (assemble target checked) := by
  obtain ⟨initial, nodesOperation, nextOperation, fieldsFormed⟩ := every_fields target
  refine ⟨initial, nodesOperation, nextOperation, ?_⟩
  unfold formProcess
  rw [fieldsFormed]
  exact dif_pos checked

-- Transporting the original registry leaves beta-redexes inside its rfl receipts.
set_option backward.dsimp.proofs true in
/-- Coverage of the complete original record in this formed carrier/node
family. The original process supplies its already admitted contracts only
inside this proof; no target field or source table enters `formProcess`. -/
theorem every_original_process (material : Material) (index : Base)
    (target : SourceNativeInquiryEngineProcess)
    (sameState : target.State = State material index)
    (nodesFormed : ∀ state : target.State, ∃ node : Node, view node = target.stateAt state) :
    ∃ initial : Base, ∃ nodesOperation nextOperation : Material,
      formProcess material index initial nodesOperation nextOperation = some target := by
  cases target with
  | mk Carrier stateAt erase_injective initial successorAt =>
      dsimp only at sameState nodesFormed ⊢
      cases sameState
      choose nodes nodesExact using nodesFormed
      have decoded : stateAt = fun state => view (nodes state) := (funext nodesExact).symm
      subst stateAt
      let fields : Fields material index :=
        ⟨nodes, initial, fun state query => (successorAt state query).val⟩
      have checked : Admissible fields := by
        refine ⟨erase_injective, ?_⟩
        intro state query
        refine ⟨?_, (successorAt state query).property.2⟩
        apply (successorAt state query).property.1.trans
        dsimp only [fields] at query ⊢
        change (view (nodes state)).Query at query
        generalize source_eq : view (nodes state) = source at query ⊢
        cases source with
        | active prior => rfl
        | answered prior oldQuery => exact nomatch query
      obtain ⟨first, nodesOperation, nextOperation, formed⟩ := every_process fields checked
      exact ⟨first, nodesOperation, nextOperation, formed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeRegistry
