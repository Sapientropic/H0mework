import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeRegistry.Nodes

/-! Whole source operations on every formed state and every legal query.
Target functions occur only in coverage proofs; the factories read one
existing higher-law family at the source's injective member addresses. -/

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeRegistry

open scoped Classical

noncomputable section

abbrev State (material : Material) (index : Base) := MotherSubquotient.Fiber material index

private theorem every_addressed_family {Domain : Type}
    (address : Domain → Base) (injective : Function.Injective address) (target : Domain → Material) :
    ∃ operation : Material, ∀ value, MotherHigherLawFamily.family operation (address value) = target value := by
  obtain ⟨operation, formed⟩ := MotherHigherLawFamily.every_family
    (Function.extend address target (fun _ => MotherHigherLawValue.scalar 0))
  refine ⟨operation, fun value => ?_⟩
  rw [formed]
  exact injective.extend_apply _ _ value

def pointNode (material : Material) (index : Base) (operation : Material) (state : State material index) :
    Option Node :=
  formNode (MotherHigherLawFamily.family operation (MotherSubquotient.address material index state))

def formNodes (material : Material) (index : Base) (operation : Material) :
    Option (State material index → Node) :=
  if complete : ∀ state, ∃ node, pointNode material index operation state = some node then
    some (fun state => (complete state).choose)
  else none

theorem every_node_family (material : Material) (index : Base) (target : State material index → Node) :
    ∃ operation : Material,
      (∀ state, pointNode material index operation state = some (target state)) ∧
      formNodes material index operation = some target := by
  choose code codeExact using (fun state => every_node (target state))
  obtain ⟨operation, readExact⟩ := every_addressed_family (MotherSubquotient.address material index)
    (MotherSubquotient.address_injective material index) code
  have pointExact (state : State material index) :
      pointNode material index operation state = some (target state) := by
    unfold pointNode
    rw [readExact]
    exact codeExact state
  have complete : ∀ state, ∃ node, pointNode material index operation state = some node :=
    fun state => ⟨target state, pointExact state⟩
  refine ⟨operation, pointExact, ?_⟩
  unfold formNodes
  rw [dif_pos complete]
  apply congrArg some
  funext state
  exact Option.some.inj ((complete state).choose_spec.symm.trans (pointExact state))

abbrev Event (material : Material) (index : Base) (nodes : State material index → Node) :=
  Σ state : State material index, Query (nodes state)

def eventAddress (material : Material) (index : Base) (nodes : State material index → Node)
    (event : Event material index nodes) : Base :=
  MotherHigherLawFamily.pair
    (MotherSubquotient.address material index event.1, queryAddress (nodes event.1) event.2)

theorem eventAddress_injective (material : Material) (index : Base) (nodes : State material index → Node) :
    Function.Injective (eventAddress material index nodes) := by
  rintro ⟨first, firstQuery⟩ ⟨last, lastQuery⟩ same
  have paired := MotherHigherLawFamily.pair_injective same
  have sameState := MotherSubquotient.address_injective material index (congrArg Prod.fst paired)
  cases sameState
  have sameQuery := queryAddress_injective (nodes first) (congrArg Prod.snd paired)
  cases sameQuery
  rfl

def pointSuccessor (material : Material) (index : Base) (nodes : State material index → Node)
    (operation : Material) (event : Event material index nodes) : Option (State material index) :=
  MotherSubquotient.formMember material index (MotherHigherLawValue.readBase
    (MotherHigherLawFamily.family operation (eventAddress material index nodes event)))

def formSuccessors (material : Material) (index : Base) (nodes : State material index → Node)
    (operation : Material) : Option ((state : State material index) → Query (nodes state) → State material index) :=
  if complete : ∀ event, ∃ state, pointSuccessor material index nodes operation event = some state then
    some (fun state query => (complete ⟨state, query⟩).choose)
  else none

theorem every_successor_family (material : Material) (index : Base) (nodes : State material index → Node)
    (target : (state : State material index) → Query (nodes state) → State material index) :
    ∃ operation : Material,
      (∀ state query, pointSuccessor material index nodes operation ⟨state, query⟩ = some (target state query)) ∧
      formSuccessors material index nodes operation = some target := by
  have codes (event : Event material index nodes) : ∃ code : Material,
      MotherHigherLawValue.readBase code = MotherSubquotient.address material index (target event.1 event.2) :=
    MotherHigherLawValue.readBase_surjective _
  choose code codeExact using codes
  obtain ⟨operation, readExact⟩ := every_addressed_family (eventAddress material index nodes)
    (eventAddress_injective material index nodes) code
  have pointExact (event : Event material index nodes) :
      pointSuccessor material index nodes operation event = some (target event.1 event.2) := by
    unfold pointSuccessor
    rw [readExact, codeExact]
    exact MotherSubquotient.address_recovers material index (target event.1 event.2)
  have complete : ∀ event, ∃ state, pointSuccessor material index nodes operation event = some state :=
    fun event => ⟨target event.1 event.2, pointExact event⟩
  refine ⟨operation, fun state query => pointExact ⟨state, query⟩, ?_⟩
  unfold formSuccessors
  rw [dif_pos complete]
  apply congrArg some
  funext state query
  exact Option.some.inj ((complete ⟨state, query⟩).choose_spec.symm.trans (pointExact ⟨state, query⟩))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeRegistry
