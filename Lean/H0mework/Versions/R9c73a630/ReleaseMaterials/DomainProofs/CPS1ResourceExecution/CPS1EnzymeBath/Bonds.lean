import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Material

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath.Joint
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource

def addressPresentChemical (frame : CPS1Recycling.Frame) (state : State frame) (address : Address) : Bool :=
  (atoms frame state).any (fun atom => atom.address = address)

def dangling (frame : CPS1Recycling.Frame) (state : State frame) : List Bond :=
  (bonds frame state).filter (fun bond =>
    !(addressPresentChemical frame state bond.left && addressPresentChemical frame state bond.right))

theorem enzyme_atom_member (frame : CPS1Recycling.Frame) (state : State frame) (atom : Graph.Atom)
    (member : atom ∈ (Body.graph frame state.originBody).atoms) :
    Atom.mk (.enzyme atom) atom ∈ atoms frame state :=
  List.mem_append_left _ (List.mem_map.mpr ⟨atom,member,rfl⟩)

theorem bath_atom_member (frame : CPS1Recycling.Frame) (state : State frame)
    (component : Component) (member : component ∈ state.components)
    (atom : Primary.Atom) (source : atom ∈ (Primary.template component.kind).atoms) :
    bathAtom component atom ∈ atoms frame state :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨component,member,List.mem_map.mpr ⟨atom,source,rfl⟩⟩)

theorem source_bonds (frame : CPS1Recycling.Frame) (state : State frame) (bond : Bond)
    (member : bond ∈ bonds frame state) :
    (∃ original ∈ (Body.graph frame state.originBody).bonds,
      bond.origin = .enzyme original ∧ bond.left = .enzyme original.left ∧ bond.right = .enzyme original.right) ∨
    (∃ component ∈ state.components, ∃ original ∈ (Primary.template component.kind).bonds,
      bond.origin = .bath component original ∧ bond.left = .bath component.occurrence original.left ∧
      bond.right = .bath component.occurrence original.right) := by
  rcases List.mem_append.mp member with enzyme | bath
  · rcases List.mem_map.mp enzyme with ⟨original,present,same⟩
    subst bond
    exact .inl ⟨original,present,rfl,rfl,rfl⟩
  · rcases List.mem_flatMap.mp bath with ⟨component,present,member⟩
    rcases List.mem_map.mp member with ⟨original,source,same⟩
    subst bond
    exact .inr ⟨component,present,original,source,rfl,rfl,rfl⟩

theorem no_dangling (frame : CPS1Recycling.Frame) (state : State frame) : dangling frame state = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro bond member
  have sources := source_bonds frame state bond member
  have present : addressPresentChemical frame state bond.left = true ∧
      addressPresentChemical frame state bond.right = true := by
    rcases sources with ⟨original,member,origin,left,right⟩ | ⟨component,componentMember,original,member,origin,left,right⟩
    · have safe := CPS1AtomicSource.Current.chain_no_dangling frame state.originBody.source
      have endpoints : Graph.addressPresent (Body.graph frame state.originBody) original.left = true ∧
          Graph.addressPresent (Body.graph frame state.originBody) original.right = true := by
        have blocked := (List.filter_eq_nil_iff.mp safe) original member
        simpa [Body.graph] using blocked
      rcases List.any_eq_true.mp endpoints.1 with ⟨a,amember,same⟩
      rcases List.any_eq_true.mp endpoints.2 with ⟨b,bmember,both⟩
      constructor
      · apply List.any_eq_true.mpr
        exact ⟨_,enzyme_atom_member frame state a amember,by simpa [Atom.address,left] using same⟩
      · apply List.any_eq_true.mpr
        exact ⟨_,enzyme_atom_member frame state b bmember,by simpa [Atom.address,right] using both⟩
    · have endpoints := List.all_eq_true.mp (Primary.original_bond_endpoints component.kind) original member
      have two : ((Primary.template component.kind).atoms.any (fun atom => atom.ordinal = original.left)) = true ∧
          ((Primary.template component.kind).atoms.any (fun atom => atom.ordinal = original.right)) = true := by
        simpa using endpoints
      rcases List.any_eq_true.mp two.1 with ⟨a,amember,same⟩
      rcases List.any_eq_true.mp two.2 with ⟨b,bmember,both⟩
      constructor
      · apply List.any_eq_true.mpr
        exact ⟨_,bath_atom_member frame state component componentMember a amember,by simpa [Atom.address,bathAtom,left] using same⟩
      · apply List.any_eq_true.mpr
        exact ⟨_,bath_atom_member frame state component componentMember b bmember,by simpa [Atom.address,bathAtom,right] using both⟩
  simp [present]

end
end CPS1EnzymeBath.Joint
