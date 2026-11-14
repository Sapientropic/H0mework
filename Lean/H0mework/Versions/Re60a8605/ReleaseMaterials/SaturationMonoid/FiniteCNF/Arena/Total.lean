import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Arena.Cost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ArenaTotal
open InterferenceProgram
open FunctionalSubstitution (Free)

theorem mapRefs_free (address : Nat) (mapping : Nat → Nat) (node : Node)
    (free : FunctionalSubstitution.Node.Free address node) :
    FunctionalSubstitution.Node.Free address (node.mapRefs mapping) := by
  cases node <;> simp only [Node.mapRefs,FunctionalSubstitution.Node.Free]
  exact free

theorem cone_emit_free (address : Nat) (needed : List Nat) (frame : Cone.Frame) (node : Node)
    (before : Free address frame.code) (free : FunctionalSubstitution.Node.Free address node) :
    Free address (Cone.emit needed frame node).code := by
  unfold Cone.emit
  split
  · intro current member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · exact before current old
    · exact mapRefs_free address _ node free
  · exact before

theorem cone_fold_free (address : Nat) (needed : List Nat) (frame : Cone.Frame) (code : List Node)
    (before : Free address frame.code) (free : ∀ node ∈ code,FunctionalSubstitution.Node.Free address node) :
    Free address (Cone.fold needed frame code).code := by
  induction code generalizing frame with
  | nil => exact before
  | cons node rest ih =>
      exact ih _ (cone_emit_free address needed frame node before (free node (by simp)))
        (fun other member => free other (by simp [member]))

theorem cone_compact_free (address : Nat) (program : Program) (free : Free address program.code) :
    Free address (Cone.compact program).code :=
  cone_fold_free address _ Cone.empty program.code.toList (by simp [Free,Cone.empty]) free

theorem rewrite_free (address other body : Nat) (mapping : Array Nat) (node : Node)
    (free : FunctionalSubstitution.Node.Free other node) :
    FunctionalSubstitution.Node.Free other (ArenaAction.rewrite address body mapping node) := by
  cases node <;> try trivial
  rename_i i
  by_cases same : i=address <;> simp_all [ArenaAction.rewrite,FunctionalSubstitution.Node.Free]

theorem step_free (address other body index : Nat) (needed : List Nat) (frame : Cone.Frame) (node : Node)
    (before : Free other frame.code) (free : FunctionalSubstitution.Node.Free other node) :
    Free other (ArenaAction.step needed address body index frame node).code := by
  unfold ArenaAction.step
  split
  · exact before
  · intro current member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with old | rfl
    · exact before current old
    · exact rewrite_free address other body frame.mapping node free

theorem finish_free (address other body offset : Nat) (needed : List Nat) (frame : Cone.Frame) (code : List Node)
    (before : Free other frame.code) (free : ∀ node ∈ code,FunctionalSubstitution.Node.Free other node) :
    Free other (ArenaAction.finish needed address body offset frame code).code := by
  induction code generalizing offset frame with
  | nil => exact before
  | cons node rest ih =>
      exact ih _ _ (step_free address other body offset needed frame node before (free node (by simp)))
        (fun other member => free other (by simp [member]))

theorem rebuild_free (address other : Nat) (code : Array Node) (root : Fin code.size)
    (free : Free other code) : Free other (ArenaAction.rebuild code root address).code :=
  finish_free address other _ _ _ _ code.toList
    (cone_compact_free other (ArenaAction.focus code root) free) free

theorem apply_preserves_free (arena : ArenaAction.Arena) (address other : Nat) (root : Fin arena.code.size)
    (free : Free other arena.code) : Free other (ArenaAction.apply arena address root).arena.code := by
  dsimp only [ArenaAction.apply]
  split
  · exact rebuild_free address other arena.code root free
  · exact free

theorem apply_inputs_subset (arena : ArenaAction.Arena) (address : Nat) (root : Fin arena.code.size) :
    FunctionalSubstitution.inputs (ArenaAction.apply arena address root).arena.code ⊆
      FunctionalSubstitution.inputs arena.code := by
  intro other present
  by_contra absent
  have before := (FunctionalSubstitution.free_iff arena.code other).mpr absent
  exact FunctionalSubstitution.inputs_free _ other (apply_preserves_free arena address other root before) present

def support (state : ArenaSource.State) : Finset Nat := (FunctionalSubstitution.inputs state.arena.code).toFinset
def remaining (state : ArenaSource.State) : Nat := (support state).card

theorem remaining_le_nodes (state : ArenaSource.State) : remaining state ≤ state.arena.code.size :=
  (List.toFinset_card_le _).trans (FunctionalSubstitution.inputs_size _)

theorem choose_present (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena)
    (found : ArenaSource.choose state=some item) : item.address ∈ support state := by
  have selected := ArenaSource.choose_eligible state item found
  simp only [ArenaSource.eligible,Bool.and_eq_true,decide_eq_true_eq] at selected
  have node : state.arena.code[item.relation.left.val]=Node.input item.address := by
    simpa [Array.getD,item.relation.left.isLt] using selected.1
  have member := Array.getElem_mem_toList item.relation.left.isLt
  rw [node] at member
  exact List.mem_toFinset.mpr ((FunctionalSubstitution.input_member _ _).mpr member)

theorem next_support_subset (state : ArenaSource.State) (address : Nat) (root : Fin state.arena.code.size) :
    support (ArenaSource.next state address root) ⊆ support state := by
  intro other present
  exact List.mem_toFinset.mpr (apply_inputs_subset state.arena address root (List.mem_toFinset.mp present))

theorem chosen_absent (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena)
    (found : ArenaSource.choose state=some item) :
    item.address ∉ support (ArenaSource.next state item.address item.relation.right) := by
  have selected := ArenaSource.choose_eligible state item found
  simp only [ArenaSource.eligible,Bool.and_eq_true,decide_eq_true_eq] at selected
  have performed := (ArenaAction.apply_performed state.arena item.address item.relation.right).mpr selected.2
  have free := ArenaAction.apply_free state.arena item.address item.relation.right performed
  simpa only [support,ArenaSource.next,List.mem_toFinset] using FunctionalSubstitution.inputs_free _ item.address free

theorem next_decreases (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena)
    (found : ArenaSource.choose state=some item) :
    remaining (ArenaSource.next state item.address item.relation.right) < remaining state := by
  apply Finset.card_lt_card
  refine ⟨next_support_subset state item.address item.relation.right,?_⟩
  intro opposite
  exact chosen_absent state item found (opposite (choose_present state item found))

theorem drive_settled (fuel : Nat) (state : ArenaSource.State) (enough : remaining state ≤ fuel) :
    ArenaSource.choose (ArenaSource.drive fuel state).state=none := by
  induction fuel generalizing state with
  | zero =>
      cases found : ArenaSource.choose state with
      | none => exact found
      | some item =>
          have present := choose_present state item found
          have positive := Finset.card_pos.mpr ⟨item.address,present⟩
          change 0 < remaining state at positive
          omega
  | succ fuel ih =>
      cases found : ArenaSource.choose state with
      | none =>
          rw [ArenaSource.drive_none fuel state found]
          exact found
      | some item =>
          have fewer := next_decreases state item found
          have bound : remaining (ArenaSource.next state item.address item.relation.right) ≤ fuel := by omega
          rw [ArenaSource.drive_some fuel state item found]
          exact ih _ bound

theorem drive_nodes_settled (state : ArenaSource.State) :
    ArenaSource.choose (ArenaSource.drive state.arena.code.size state).state=none :=
  drive_settled state.arena.code.size state (remaining_le_nodes state)

end SaturationMonoid.ComplexityProjection.SATSource.ArenaTotal
