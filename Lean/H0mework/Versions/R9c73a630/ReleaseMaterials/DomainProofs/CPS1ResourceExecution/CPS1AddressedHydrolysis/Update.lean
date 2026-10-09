import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedHydrolysis.Water
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Incidence
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace CPS1AddressedHydrolysis
open CPS1LocalChemicalExecution CPS1AtomicSource CPS1ResourceExecution

def restored (edge residue : Nat) (atom : Primary.Atom) : Bool :=
  match atom.terminalLeave with
  | .none => false
  | .amino => residue = edge+1
  | .carboxyl => residue = edge

theorem survives_erase (edges : List Nat) (unique : edges.Nodup) (edge : Nat)
    (present : edge ∈ edges) (residue : Nat) (atom : Primary.Atom) :
    Graph.survives (edges.erase edge) residue atom =
      (Graph.survives edges residue atom || restored edge residue atom) := by
  cases leave : atom.terminalLeave with
  | none => simp only [Graph.survives,restored,leave,Bool.true_or]
  | carboxyl =>
    by_cases same : residue = edge
    · subst residue
      simp [Graph.survives,restored,leave,present,unique.not_mem_erase]
    · simp [Graph.survives,restored,leave,same,List.mem_erase_of_ne same]
  | amino =>
    cases residue with
    | zero => simp [Graph.survives,restored,leave]
    | succ residue =>
      by_cases same : residue = edge
      · subst residue
        simp [Graph.survives,restored,leave,present,unique.not_mem_erase]
      · simp [Graph.survives,restored,leave,same,List.mem_erase_of_ne same]

theorem restored_disjoint (edges : List Nat) (edge : Nat) (present : edge ∈ edges)
    (residue : Nat) (atom : Primary.Atom) (new : restored edge residue atom = true) :
    Graph.survives edges residue atom = false := by
  cases leave : atom.terminalLeave with
  | none => simp [restored,leave] at new
  | carboxyl =>
    have same : residue = edge := by simpa only [restored,leave,decide_eq_true_eq] using new
    subst residue
    simp [Graph.survives,leave,present]
  | amino =>
    have same : residue = edge+1 := by simpa only [restored,leave,decide_eq_true_eq] using new
    subst residue
    simp [Graph.survives,leave,present]

theorem filter_or_partition {A : Type} (rows : List A) (old new : A → Bool)
    (disjoint : ∀ atom, old atom = true → new atom = false) :
    (rows.filter (fun atom => old atom || new atom)).Perm (rows.filter old ++ rows.filter new) := by
  induction rows with
  | nil => exact List.Perm.refl _
  | cons atom rest ih =>
    cases previous : old atom <;> cases added : new atom
    · simpa [previous,added] using ih
    · simp only [List.filter_cons,previous,added,Bool.false_or]
      have move : (atom :: (rest.filter old ++ rest.filter new)).Perm
          (rest.filter old ++ atom :: rest.filter new) := by
        simpa only [List.cons_append,List.nil_append,List.append_assoc] using
          ((List.perm_append_comm : ([atom] ++ rest.filter old).Perm (rest.filter old ++ [atom])).append_right
            (rest.filter new))
      exact (ih.cons atom).trans move
    · simpa [previous,added] using ih.cons atom
    · have impossible := disjoint atom previous
      rw [added] at impossible
      cases impossible

def gainedRow (edge : Nat) (row : AA × Nat) : List Graph.Atom :=
  ((Primary.template row.1).atoms.filter (restored edge row.2)).map
    (fun atom => ⟨⟨row.2,atom.name⟩,atom⟩)

def gainedAtoms (word : List AA) (edge : Nat) : List Graph.Atom := word.zipIdx.flatMap (gainedRow edge)

theorem residue_atom_update (edges : List Nat) (unique : edges.Nodup) (edge : Nat)
    (present : edge ∈ edges) (row : AA × Nat) :
    (Graph.residueAtoms Primary.template (edges.erase edge) row).Perm
      (Graph.residueAtoms Primary.template edges row ++ gainedRow edge row) := by
  have law : Graph.survives (edges.erase edge) row.2 =
      fun atom => Graph.survives edges row.2 atom || restored edge row.2 atom :=
    funext (survives_erase edges unique edge present row.2)
  unfold Graph.residueAtoms gainedRow
  rw [law,← List.map_append]
  apply List.Perm.map
  apply filter_or_partition
  intro atom old
  cases added : restored edge row.2 atom with
  | false => rfl
  | true =>
    have impossible := restored_disjoint edges edge present row.2 atom added
    rw [old] at impossible
    cases impossible

theorem graph_atom_update (word : List AA) (edges : List Nat) (unique : edges.Nodup)
    (bounded : ∀ edge ∈ edges, edge+1 < word.length) (edge : Nat) (present : edge ∈ edges) :
    (Graph.build Primary.template word (edges.erase edge)).atoms.Perm
      ((Graph.build Primary.template word edges).atoms ++ gainedAtoms word edge) := by
  have oldEdges : edges.filter (fun edge => edge+1 < word.length) = edges :=
    List.filter_eq_self.mpr (fun address member => decide_eq_true (bounded _ member))
  have nextEdges : (edges.erase edge).filter (fun edge => edge+1 < word.length) = edges.erase edge :=
    List.filter_eq_self.mpr (fun address member => decide_eq_true (bounded _ (List.mem_of_mem_erase member)))
  simp only [Graph.build,oldEdges,nextEdges,gainedAtoms]
  have rowwise := List.Perm.flatMap_left word.zipIdx
    (fun row _ => residue_atom_update edges unique edge present row)
  exact rowwise.trans (List.flatMap_append_perm word.zipIdx
    (Graph.residueAtoms Primary.template edges) (gainedRow edge)).symm

theorem restored_left (edge : Nat) (atom : Primary.Atom) :
    restored edge edge atom = decide (atom.terminalLeave = .carboxyl) := by
  cases leave : atom.terminalLeave <;> simp [restored,leave]

theorem restored_right (edge : Nat) (atom : Primary.Atom) :
    restored edge (edge+1) atom = decide (atom.terminalLeave = .amino) := by
  cases leave : atom.terminalLeave <;> simp [restored,leave]

theorem restored_other (edge residue : Nat) (left : residue ≠ edge) (right : residue ≠ edge+1)
    (atom : Primary.Atom) : restored edge residue atom = false := by
  cases leave : atom.terminalLeave <;> simp [restored,leave,left,right]

def sourceWaterSlot (atom : Graph.Atom) : WaterAtom :=
  terminalWaterAtom atom.source.terminalLeave atom.source

theorem terminal_slot_map (aa : AA) (leave : Primary.TerminalLeave) :
    (terminalAtoms aa leave).map (fun atom => terminalWaterAtom atom.terminalLeave atom) =
      (terminalAtoms aa leave).map (terminalWaterAtom leave) := by
  apply List.map_congr_left
  intro atom member
  rw [(terminal_source aa leave atom member).2]

theorem gained_row_slots (edge : Nat) (row : AA × Nat) :
    (gainedRow edge row).map sourceWaterSlot =
      if row.2 = edge then [.oxygen,.hydroxylH]
      else if row.2 = edge+1 then [.aminoH] else [] := by
  by_cases left : row.2 = edge
  · rw [if_pos left]
    simp only [gainedRow,List.map_map]
    rw [left,funext (restored_left edge)]
    change (terminalAtoms row.1 .carboxyl).map (fun atom => terminalWaterAtom atom.terminalLeave atom) = _
    rw [terminal_slot_map]
    exact (terminal_water_slots row.1).2
  · by_cases right : row.2 = edge+1
    · rw [if_neg left,if_pos right]
      simp only [gainedRow,List.map_map]
      rw [right,funext (restored_right edge)]
      change (terminalAtoms row.1 .amino).map (fun atom => terminalWaterAtom atom.terminalLeave atom) = _
      rw [terminal_slot_map]
      exact (terminal_water_slots row.1).1
    · have nowhere : restored edge row.2 = fun _ => false :=
        funext (restored_other edge row.2 left right)
      simp only [gainedRow,nowhere,List.filter_false,List.map_nil,left,right,if_false]

theorem index_indicator (word : List AA) (index : Nat) (inside : index < word.length) :
    (word.zipIdx.map (fun row => if row.2 = index then 1 else 0)).sum = 1 := by
  have mapping : word.zipIdx.map (fun row => if row.2 = index then 1 else 0) =
      (List.range word.length).map (fun row => if row = index then 1 else 0) := by
    simpa only [List.map_map,Function.comp_def,← List.range_eq_range'] using
      congrArg (List.map (fun row => if row = index then 1 else 0)) (List.zipIdx_map_snd 0 word)
  rw [mapping]
  have paid := Incidence.range_membership_count word.length [index] (by simp)
    (fun value member => by
      have same := List.mem_singleton.mp member
      subst value
      exact inside)
  have indicator := Incidence.indicator_sum (List.range word.length) (fun row => decide (row = index))
  simp only [decide_eq_true_eq] at indicator
  rw [indicator]
  simpa only [List.mem_singleton,List.length_singleton] using paid

theorem gained_slots_partition (word : List AA) (edge : Nat) (inside : edge+1 < word.length) :
    ((gainedAtoms word edge).map sourceWaterSlot).Perm waterAtoms := by
  apply List.perm_iff_count.mpr
  intro slot
  have counted : ((gainedAtoms word edge).map sourceWaterSlot).count slot =
      if slot = .aminoH then (word.zipIdx.map (fun row => if row.2 = edge+1 then 1 else 0)).sum
      else (word.zipIdx.map (fun row => if row.2 = edge then 1 else 0)).sum := by
    simp only [gainedAtoms,List.map_flatMap,List.count_flatMap,Function.comp_def]
    split
    · rename_i amino
      subst slot
      apply congrArg List.sum
      apply List.map_congr_left
      intro row _
      rw [gained_row_slots]
      by_cases left : row.2 = edge
      · simp [left]
      · by_cases right : row.2 = edge+1 <;> simp [left,right]
    · rename_i other
      apply congrArg List.sum
      apply List.map_congr_left
      intro row _
      rw [gained_row_slots]
      cases slot with
      | aminoH => exact False.elim (other rfl)
      | hydroxylH => by_cases left : row.2 = edge <;> by_cases right : row.2 = edge+1 <;> simp [left,right]
      | oxygen => by_cases left : row.2 = edge <;> by_cases right : row.2 = edge+1 <;> simp [left,right]
  have first := index_indicator word edge (by omega)
  have second := index_indicator word (edge+1) inside
  rw [counted]
  cases slot <;> simp [first,second,waterAtoms]

inductive Origin
  | old (nuclear : Nat)
  | water (source : Water) (atom : WaterAtom)
  deriving DecidableEq

structure Atom where
  origin : Origin
  descriptor : Graph.Atom
  deriving DecidableEq

def oldAtoms (graph : Graph.Molecule) : List Atom :=
  graph.atoms.zipIdx.map (fun row => ⟨.old row.2,row.1⟩)

def waterAtomsAt (water : Water) (word : List AA) (edge : Nat) : List Atom :=
  (gainedAtoms word edge).map (fun atom =>
    ⟨.water water (terminalWaterAtom atom.source.terminalLeave atom.source),atom⟩)

def producedAtoms (water : Water) (word : List AA) (edges : List Nat) (edge : Nat) : List Atom :=
  oldAtoms (Graph.build Primary.template word edges) ++ waterAtomsAt water word edge

theorem produced_descriptors (water : Water) (word : List AA) (edges : List Nat)
    (unique : edges.Nodup) (bounded : ∀ edge ∈ edges, edge+1 < word.length)
    (edge : Nat) (present : edge ∈ edges) :
    ((producedAtoms water word edges edge).map Atom.descriptor).Perm
      (Graph.build Primary.template word (edges.erase edge)).atoms := by
  simp only [producedAtoms,oldAtoms,waterAtomsAt,List.map_append,List.map_map,Function.comp_def]
  have old := List.zipIdx_map_fst 0 (Graph.build Primary.template word edges).atoms
  rw [old]
  simpa only [List.map_id_fun',id_eq] using (graph_atom_update word edges unique bounded edge present).symm

theorem old_origins (graph : Graph.Molecule) :
    (oldAtoms graph).map Atom.origin = (List.range graph.atoms.length).map Origin.old := by
  simpa only [oldAtoms,List.map_map,Function.comp_def,← List.range_eq_range'] using
    congrArg (List.map Origin.old) (List.zipIdx_map_snd 0 graph.atoms)

theorem produced_partition (water : Water) (word : List AA) (edges : List Nat)
    (edge : Nat) (inside : edge+1 < word.length) :
    ((producedAtoms water word edges edge).map Atom.origin).Perm
      ((List.range (Graph.build Primary.template word edges).atoms.length).map Origin.old ++
        waterAtoms.map (Origin.water water)) := by
  simp only [producedAtoms,List.map_append,old_origins,waterAtomsAt,List.map_map]
  simpa only [List.map_map,Function.comp_def,sourceWaterSlot] using
    (((gained_slots_partition word edge inside).map (Origin.water water)).append_left
      ((List.range (Graph.build Primary.template word edges).atoms.length).map Origin.old))

theorem produced_origins_unique (water : Water) (word : List AA) (edges : List Nat)
    (edge : Nat) (inside : edge+1 < word.length) :
    ((producedAtoms water word edges edge).map Atom.origin).Nodup := by
  apply (produced_partition water word edges edge inside).nodup_iff.mpr
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_range).map (fun _ _ same => Origin.old.inj same),
    (water_rule .H).2.2.1.map (fun _ _ same => (Origin.water.inj same).2),?_⟩
  intro first old second fresh same
  rcases List.mem_map.mp old with ⟨index,_,rfl⟩
  rcases List.mem_map.mp fresh with ⟨atom,_,rfl⟩
  cases same

theorem gained_payload (word : List AA) (edge : Nat) (atom : Graph.Atom)
    (member : atom ∈ gainedAtoms word edge) :
    (∃ row ∈ word.zipIdx, atom.source ∈ (Primary.template row.1).atoms ∧
      atom.address = ⟨row.2,atom.source.name⟩) ∧
    (sourceWaterSlot atom).element = atom.source.element ∧
      (sourceWaterSlot atom).charge = atom.source.charge := by
  rcases List.mem_flatMap.mp member with ⟨row,inWord,gained⟩
  rcases List.mem_map.mp gained with ⟨source,selected,same⟩
  subst atom
  have templateSource := (List.mem_filter.mp selected).1
  have restoredSource := (List.mem_filter.mp selected).2
  have terminal : source.terminalLeave = .amino ∨ source.terminalLeave = .carboxyl := by
    cases leave : source.terminalLeave with
    | none => simp [restored,leave] at restoredSource
    | amino => exact Or.inl rfl
    | carboxyl => exact Or.inr rfl
  have selectedTerminal : source ∈ terminalAtoms row.1 source.terminalLeave :=
    List.mem_filter.mpr ⟨templateSource,by simp⟩
  exact ⟨⟨row,inWord,templateSource,rfl⟩,terminal_water_payload row.1 _ terminal _ selectedTerminal⟩

theorem graph_addresses_unique (word : List AA) (edges : List Nat) :
    ((Graph.build Primary.template word edges).atoms.map Graph.Atom.address).Nodup := by
  simp only [Graph.build,List.map_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro row _
    let remaining := edges.filter (fun edge => edge+1 < word.length)
    have namesUnique : (((Primary.template row.1).atoms.filter (Graph.survives remaining row.2)).map
        Primary.Atom.name).Nodup :=
      (Primary.original_names_unique row.1).sublist (List.filter_sublist.map _)
    have addressed := namesUnique.map (f := fun name : String => (⟨row.2,name⟩ : Graph.Address))
      (fun _ _ same => congrArg Graph.Address.atom same)
    simpa only [Graph.residueAtoms,List.map_map,Function.comp_def] using addressed
  · have indicesUnique : (word.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' _
    have different := List.pairwise_map.mp indicesUnique
    apply different.imp
    intro first second distinct address inFirst inSecond
    rcases List.mem_map.mp inFirst with ⟨firstAtom,firstMember,firstAddress⟩
    rcases List.mem_map.mp inSecond with ⟨secondAtom,secondMember,secondAddress⟩
    have left := (Graph.source_atom_payload Primary.template _ first firstAtom firstMember).2
    have right := (Graph.source_atom_payload Primary.template _ second secondAtom secondMember).2
    have same := congrArg Graph.Address.residue (firstAddress.trans secondAddress.symm)
    rw [left,right] at same
    exact distinct same

theorem produced_addresses_unique (water : Water) (word : List AA) (edges : List Nat)
    (unique : edges.Nodup) (bounded : ∀ edge ∈ edges, edge+1 < word.length)
    (edge : Nat) (present : edge ∈ edges) :
    ((producedAtoms water word edges edge).map (fun atom => atom.descriptor.address)).Nodup := by
  have aligned := (produced_descriptors water word edges unique bounded edge present).map Graph.Atom.address
  simpa only [List.map_map,Function.comp_def] using
    aligned.nodup_iff.mpr (graph_addresses_unique word (edges.erase edge))

theorem peptide_bond_injective : Function.Injective Graph.peptideBond := by
  intro left right same
  exact congrArg (fun bond => bond.left.residue) same

theorem peptide_removed (word : List AA) (edges : List Nat) (unique : edges.Nodup)
    (bounded : ∀ edge ∈ edges, edge+1 < word.length) (edge : Nat) (present : edge ∈ edges) :
    Graph.peptideBond edge ∈ (Graph.build Primary.template word edges).bonds ∧
      Graph.peptideBond edge ∉ (Graph.build Primary.template word (edges.erase edge)).bonds := by
  have oldEdges : edges.filter (fun address => address+1 < word.length) = edges :=
    List.filter_eq_self.mpr (fun address member => decide_eq_true (bounded _ member))
  have afterEdges : (edges.erase edge).filter (fun address => address+1 < word.length) = edges.erase edge :=
    List.filter_eq_self.mpr (fun address member => decide_eq_true (bounded _ (List.mem_of_mem_erase member)))
  constructor
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨edge,
      List.mem_filter.mpr ⟨present,decide_eq_true (bounded _ present)⟩,rfl⟩)
  · intro member
    rcases List.mem_append.mp member with component | peptide
    · rcases List.mem_flatMap.mp component with ⟨row,_,member⟩
      have source := Graph.source_component_bond Primary.template _ row _ member
      rcases source with ⟨original,_,_,_,_,_,_,kind⟩
      cases kind
    · rcases List.mem_map.mp peptide with ⟨address,member,same⟩
      have equality := peptide_bond_injective same
      subst address
      rw [afterEdges] at member
      exact unique.not_mem_erase member

theorem component_preserved (edges : List Nat) (unique : edges.Nodup) (edge : Nat)
    (present : edge ∈ edges) (row : AA × Nat) (bond : Graph.Bond)
    (old : bond ∈ Graph.componentBonds Primary.template edges row) :
    bond ∈ Graph.componentBonds Primary.template (edges.erase edge) row := by
  have names : ∀ name ∈ ((Primary.template row.1).atoms.filter (Graph.survives edges row.2)).map Primary.Atom.name,
      name ∈ ((Primary.template row.1).atoms.filter (Graph.survives (edges.erase edge) row.2)).map Primary.Atom.name := by
    intro name member
    rcases List.mem_map.mp member with ⟨atom,oldAtom,rfl⟩
    apply List.mem_map.mpr
    refine ⟨atom,List.mem_filter.mpr ⟨(List.mem_filter.mp oldAtom).1,?_⟩,rfl⟩
    rw [survives_erase edges unique edge present row.2 atom,(List.mem_filter.mp oldAtom).2]
    rfl
  rcases List.mem_map.mp old with ⟨original,member,same⟩
  subst bond
  have source := (List.mem_filter.mp member).1
  have ends := (List.mem_filter.mp member).2
  simp only [Bool.and_eq_true,decide_eq_true_eq] at ends
  apply List.mem_map.mpr
  refine ⟨original,List.mem_filter.mpr ⟨source,?_⟩,rfl⟩
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨names _ ends.1,names _ ends.2⟩

theorem other_bonds_preserved (word : List AA) (edges : List Nat) (unique : edges.Nodup)
    (bounded : ∀ edge ∈ edges, edge+1 < word.length) (edge : Nat) (present : edge ∈ edges)
    (bond : Graph.Bond) (old : bond ∈ (Graph.build Primary.template word edges).bonds)
    (different : bond ≠ Graph.peptideBond edge) :
    bond ∈ (Graph.build Primary.template word (edges.erase edge)).bonds := by
  have oldEdges : edges.filter (fun address => address+1 < word.length) = edges :=
    List.filter_eq_self.mpr (fun address member => decide_eq_true (bounded _ member))
  have afterEdges : (edges.erase edge).filter (fun address => address+1 < word.length) = edges.erase edge :=
    List.filter_eq_self.mpr (fun address member => decide_eq_true (bounded _ (List.mem_of_mem_erase member)))
  simp only [Graph.build,oldEdges] at old
  simp only [Graph.build,afterEdges]
  rcases List.mem_append.mp old with component | peptide
  · rcases List.mem_flatMap.mp component with ⟨row,inWord,member⟩
    exact List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨row,inWord,component_preserved edges unique edge present row bond member⟩)
  · rcases List.mem_map.mp peptide with ⟨address,member,same⟩
    have distinct : address ≠ edge := by
      intro equality
      subst address
      exact different same.symm
    exact List.mem_append_right _ (List.mem_map.mpr
      ⟨address,(List.mem_erase_of_ne distinct).mpr member,same⟩)

def atomAt? (atoms : List Atom) (address : Graph.Address) : Option Atom :=
  atoms.find? (fun atom => atom.descriptor.address = address)

theorem atom_at_exists (atoms : List Atom) (address : Graph.Address)
    (present : ∃ atom ∈ atoms, atom.descriptor.address = address) :
    ∃ atom, atomAt? atoms address = some atom ∧ atom ∈ atoms ∧ atom.descriptor.address = address := by
  have nonempty : (atomAt? atoms address).isSome := by
    apply List.find?_isSome.mpr
    rcases present with ⟨atom,member,same⟩
    exact ⟨atom,member,decide_eq_true same⟩
  cases found : atomAt? atoms address with
  | none => rw [found] at nonempty; cases nonempty
  | some atom =>
    exact ⟨atom,rfl,List.mem_of_find?_eq_some found,
      of_decide_eq_true (List.find?_some (p := fun value : Atom => decide (value.descriptor.address = address)) found)⟩

structure Bond where
  source : Graph.Bond
  left : Origin
  right : Origin
  deriving DecidableEq

def resolveBond? (atoms : List Atom) (bond : Graph.Bond) : Option Bond := do
  let left ← atomAt? atoms bond.left
  let right ← atomAt? atoms bond.right
  pure ⟨bond,left.origin,right.origin⟩

theorem resolve_bond_in_carrier (atoms : List Atom) (word : List AA) (edges : List Nat)
    (descriptors : (atoms.map Atom.descriptor).Perm (Graph.build Primary.template word edges).atoms)
    (source : Graph.Bond) (member : source ∈ (Graph.build Primary.template word edges).bonds) :
    ∃ bond, resolveBond? atoms source = some bond ∧ bond.source = source ∧
      (∃ atom ∈ atoms, atom.origin = bond.left ∧ atom.descriptor.address = source.left) ∧
      (∃ atom ∈ atoms, atom.origin = bond.right ∧ atom.descriptor.address = source.right) := by
  have undangling := Graph.no_dangling word edges
  have absent : source ∉ Graph.dangling (Graph.build Primary.template word edges) := by
    rw [undangling]
    simp
  have endpoints : Graph.addressPresent (Graph.build Primary.template word edges) source.left = true ∧
      Graph.addressPresent (Graph.build Primary.template word edges) source.right = true := by
    by_contra missing
    apply absent
    apply List.mem_filter.mpr
    refine ⟨member,?_⟩
    cases left : Graph.addressPresent (Graph.build Primary.template word edges) source.left <;>
      cases right : Graph.addressPresent (Graph.build Primary.template word edges) source.right <;>
      simp_all
  have recover (address : Graph.Address)
      (available : Graph.addressPresent (Graph.build Primary.template word edges) address = true) :
      ∃ atom ∈ atoms, atom.descriptor.address = address := by
    rcases (Graph.address_present_iff _ _).mp available with ⟨atom,member,same⟩
    have represented := descriptors.mem_iff.mpr member
    rcases List.mem_map.mp represented with ⟨carrier,held,identity⟩
    exact ⟨carrier,held,identity ▸ same⟩
  rcases atom_at_exists _ source.left (recover source.left endpoints.1) with ⟨left,leftAt,leftMember,leftAddress⟩
  rcases atom_at_exists _ source.right (recover source.right endpoints.2) with ⟨right,rightAt,rightMember,rightAddress⟩
  refine ⟨⟨source,left.origin,right.origin⟩,?_,rfl,⟨left,leftMember,rfl,leftAddress⟩,⟨right,rightMember,rfl,rightAddress⟩⟩
  unfold resolveBond?
  rw [leftAt,rightAt]
  rfl

theorem resolve_bond_generated (water : Water) (word : List AA) (edges : List Nat)
    (unique : edges.Nodup) (bounded : ∀ edge ∈ edges, edge+1 < word.length)
    (edge : Nat) (present : edge ∈ edges) (source : Graph.Bond)
    (member : source ∈ (Graph.build Primary.template word (edges.erase edge)).bonds) :
    ∃ bond, resolveBond? (producedAtoms water word edges edge) source = some bond ∧
      bond.source = source ∧
      (∃ atom ∈ producedAtoms water word edges edge, atom.origin = bond.left ∧ atom.descriptor.address = source.left) ∧
      (∃ atom ∈ producedAtoms water word edges edge, atom.origin = bond.right ∧ atom.descriptor.address = source.right) :=
  resolve_bond_in_carrier _ word (edges.erase edge)
    (produced_descriptors water word edges unique bounded edge present) source member

end CPS1AddressedHydrolysis
