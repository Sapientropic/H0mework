import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.Declarations.ParentCompletion.Trees

/-! The raw factory reads only the actual children stored by this node. Its
complete carrier has no caller-selected support or parent-index parameter.
A mother-source interpretation must still realize this entire carrier. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ParentCompletion
open MotherSmallSupport UniformSpace
open scoped Classical Topology
universe u
noncomputable section

/-- Addresses are computed from the node; the corresponding entire child
construction remains in the node and is recovered by childAt. -/
def Child : {result : W.{u}} → Build result → Type (u + 1)
  | _, .seed => PEmpty
  | result, .completed _ _ _ => {x : W.{u} // x ∈ result}

def childAt : {result : W.{u}} → (node : Build result) → Child node → Parent
  | _, .seed, child => nomatch child
  | _, .completed _ _ parents, child => ⟨child.val, parents child.val child.property⟩

abbrev Packet {result : W.{u}} (node : Build result) := List (Child node)

def parentValues {result : W.{u}} (node : Build result) : Set W :=
  Set.range (fun child : Child node => (childAt node child).1)

def packetSupport {result : W.{u}} (node : Build result) (packet : Packet node) : Finset W :=
  (packet.map (fun child => (childAt node child).1)).toFinset

def packetRead {result : W.{u}} (node : Build result) (packet : Packet node) : W.{u} → ℝ :=
  finiteProfile (packetSupport node packet)

theorem packetSupport_parents {result : W.{u}} (node : Build result) (packet : Packet node) :
    (↑(packetSupport node packet) : Set W) ⊆ parentValues node := by
  intro x member
  obtain ⟨child, _, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact ⟨child, same⟩

abbrev Raw {result : W.{u}} (node : Build result) := Set.range (packetRead node)
abbrev Completed {result : W.{u}} (node : Build result) := Completion (Raw node)

def toRelativeRaw {result : W.{u}} (node : Build result) (raw : Raw node) :
    MotherSmallSupport.Raw (parentValues node) :=
  ⟨raw.val, by
    obtain ⟨packet, same⟩ := raw.property
    exact ⟨packetSupport node packet, packetSupport_parents node packet, same⟩⟩

theorem every_relative_raw {result : W.{u}} (node : Build result)
    (raw : MotherSmallSupport.Raw (parentValues node)) :
    ∃ packet : Packet node, packetRead node packet = raw.val := by
  obtain ⟨support, supported, same⟩ := raw.property
  let address (x : support) : Child node := Classical.choose (supported x.property)
  have address_value (x : support) : (childAt node (address x)).1 = x.val :=
    Classical.choose_spec (supported x.property)
  let packet := support.attach.toList.map address
  have exactSupport : packetSupport node packet = support := by
    ext x
    simp only [packetSupport, packet, List.map_map, List.mem_toFinset, List.mem_map,
      Finset.mem_toList, Function.comp_apply, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨value, sameValue⟩
      rw [address_value] at sameValue
      exact sameValue ▸ value.property
    · intro member
      exact ⟨⟨x, member⟩, address_value ⟨x, member⟩⟩
  exact ⟨packet, (congrArg finiteProfile exactSupport).trans same⟩

def rawEquiv {result : W.{u}} (node : Build result) :
    Raw node ≃ᵤ MotherSmallSupport.Raw (parentValues node) where
  toFun := toRelativeRaw node
  invFun := fun raw => ⟨raw.val, every_relative_raw node raw⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl
  uniformContinuous_toFun := uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _

/-- The complete carrier correspondence retains all completed values. -/
def completedEquiv {result : W.{u}} (node : Build result) :
    Completed node ≃ᵤ Formed (parentValues node) :=
  Completion.mapEquiv (rawEquiv node)

def restoreCompletion {result : W.{u}} (node : Build result)
    (material : Completed node) : Material.{u} :=
  includeCompleted (Set.subset_univ (parentValues node)) (completedEquiv node material)

def collectNode {result : W.{u}} (node : Build result)
    (material : Completed node) : Option W.{u} :=
  formSmall Set.univ (restoreCompletion node material)

theorem parentValues_eq_members {result : W.{u}} (node : Build result) :
    parentValues node = (result : Set W) := by
  cases node with
  | seed =>
      ext x
      constructor
      · rintro ⟨child, _⟩
        exact nomatch child
      · intro impossible
        exact (ZFSet.notMem_empty x impossible).elim
  | completed material formed parents =>
      ext x
      constructor
      · rintro ⟨child, same⟩
        exact same ▸ child.property
      · intro member
        exact ⟨⟨x, member⟩, rfl⟩

theorem restored_uses_only_actual_parents {result : W.{u}} (node : Build result)
    (material : Completed node) (x : W.{u})
    (selected : read Set.univ (restoreCompletion node material) x = 1) : x ∈ result := by
  rw [restoreCompletion, read_includeCompleted] at selected
  have member : x ∈ parentValues node := by
    by_contra absent
    exact no_new_one (parentValues node) x absent (completedEquiv node material) selected
  rwa [parentValues_eq_members] at member

theorem completed_node_lift (material : Material.{u}) (result : W.{u})
    (formed : formSmall Set.univ material = some result)
    (parents : (x : W.{u}) → x ∈ result → Build x) :
    ∃! actual : Completed (.completed material formed parents),
      restoreCompletion (.completed material formed parents) actual = material := by
  let node : Build result := .completed material formed parents
  have supported (x : W.{u}) (one : read Set.univ material x = 1) :
      x ∈ parentValues node :=
    ⟨⟨x, (formed_members material result formed x).mp one⟩, rfl⟩
  obtain ⟨localMaterial, restored, unique⟩ :=
    localize (Set.subset_univ (parentValues node)) material supported
  refine ⟨(completedEquiv node).symm localMaterial, ?_, fun other same => ?_⟩
  · simpa only [node, restoreCompletion, UniformEquiv.apply_symm_apply] using restored
  · apply (completedEquiv node).injective
    rw [UniformEquiv.apply_symm_apply]
    exact unique (completedEquiv node other) same

theorem completed_node_collected (material : Material.{u}) (result : W.{u})
    (formed : formSmall Set.univ material = some result)
    (parents : (x : W.{u}) → x ∈ result → Build x) :
    ∃ actual : Completed (.completed material formed parents),
      restoreCompletion (.completed material formed parents) actual = material ∧
      collectNode (.completed material formed parents) actual = some result := by
  obtain ⟨actual, restored, _⟩ := completed_node_lift material result formed parents
  refine ⟨actual, restored, ?_⟩
  exact (congrArg (formSmall Set.univ) restored).trans formed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ParentCompletion
