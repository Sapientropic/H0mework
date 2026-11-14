import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.Search

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.Source

open SaturationMonoid.ComplexityProjection.SATSource.Affine

structure Item (n d : Nat) where
  literal : Fin n
  demand : Fin d
  deriving DecidableEq, Repr

def erase {n d : Nat} (groups : List (List (Item n d))) : List (List (Fin n)) :=
  groups.map (fun group => group.map (·.literal))

def put {n d : Nat} (formula : CNFFormula n) (item : Item n d) :
    List (List (Item n d)) → List (List (Item n d))
  | [] => [[item]]
  | group :: rest =>
      if (Capacity.fits formula item.literal (group.map (·.literal))).accepted then
        (item::group)::rest else group::put formula item rest

theorem put_erase {n d : Nat} (formula : CNFFormula n) (item : Item n d) (groups : List (List (Item n d))) :
    erase (put formula item groups) = Capacity.put formula item.literal (erase groups) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [put,erase,List.map_cons,Capacity.put]
      split <;> simp_all only [erase,List.map_cons]

theorem put_perm {n d : Nat} (formula : CNFFormula n) (item : Item n d) (groups : List (List (Item n d))) :
    (put formula item groups).flatten.Perm (item::groups.flatten) := by
  induction groups with
  | nil => exact List.Perm.refl _
  | cons group rest ih =>
      simp only [put]
      split
      · exact List.Perm.refl _
      · simp only [List.flatten_cons]
        exact (ih.append_left group).trans List.perm_middle

def partition {n d : Nat} (formula : CNFFormula n) : List (Item n d) → List (List (Item n d))
  | [] => []
  | item::rest => put formula item (partition formula rest)

theorem partition_erase {n d : Nat} (formula : CNFFormula n) (items : List (Item n d)) :
    erase (partition formula items) = Capacity.partition formula (items.map (·.literal)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => rw [partition,put_erase,ih]; rfl

theorem partition_perm {n d : Nat} (formula : CNFFormula n) (items : List (Item n d)) :
    (partition formula items).flatten.Perm items := by
  induction items with
  | nil => exact List.Perm.refl _
  | cons item rest ih => exact (put_perm formula item _).trans (ih.cons item)

def tags {n : Nat} (rows : List (List (Fin n))) : List (Item n rows.length) :=
  (List.ofFn fun i : Fin rows.length => (rows.get i).map fun literal => ⟨literal,i⟩).flatten

theorem tags_erase {n : Nat} (rows : List (List (Fin n))) :
    (tags rows).map (·.literal) = rows.flatten := by
  simp [tags,List.map_flatten,List.map_ofFn,List.map_map,Function.comp_def]

theorem tag_member {n : Nat} (rows : List (List (Fin n))) (i : Fin rows.length) (literal : Fin n)
    (member : literal ∈ rows.get i) : (⟨literal,i⟩ : Item n rows.length) ∈ tags rows := by
  apply List.mem_flatten.mpr
  refine ⟨(rows.get i).map (fun value => (⟨value,i⟩ : Item n rows.length)),?_,?_⟩
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · exact List.mem_map.mpr ⟨literal,member,rfl⟩

def groups {n : Nat} (formula : CNFFormula n) : List (List (Item n (Capacity.positives formula).length)) :=
  partition formula (tags (Capacity.positives formula))

theorem groups_erase {n : Nat} (formula : CNFFormula n) :
    erase (groups formula) = Capacity.partition formula (Capacity.positives formula).flatten := by
  rw [groups,partition_erase,tags_erase]

theorem groups_good {n : Nat} (formula : CNFFormula n) (group : List (Item n (Capacity.positives formula).length))
    (member : group ∈ groups formula) : Capacity.GoodGroup formula (group.map (·.literal)) := by
  have good := Capacity.partition_good formula (Capacity.positives formula).flatten
  rw [← groups_erase] at good
  exact good _ (List.mem_map.mpr ⟨group,member,rfl⟩)

theorem groups_length {n : Nat} (formula : CNFFormula n) :
    (groups formula).length ≤ Extract.literalCount formula := by
  have same := congrArg List.length (groups_erase formula)
  simp only [erase,List.length_map] at same
  rw [same]
  exact (Capacity.partition_length formula _).trans (Capacity.positives_literals formula)

theorem groups_items {n : Nat} (formula : CNFFormula n) :
    (groups formula).flatten.length = (Capacity.positives formula).flatten.length := by
  have retained := (partition_perm formula (tags (Capacity.positives formula))).length_eq
  have tagsSize := congrArg List.length (tags_erase (Capacity.positives formula))
  simp only [List.length_map] at tagsSize
  exact retained.trans tagsSize

def ofGroups {n d : Nat} (data : List (List (Item n d))) : Graph d data.length :=
  Vector.ofFn fun i => Vector.ofFn fun j => (data.get j).any fun item => item.demand == i

theorem edge_groups {n d : Nat} (data : List (List (Item n d))) (i : Fin d) (j : Fin data.length) :
    edge (ofGroups data) i j = ((data.get j).any fun item => item.demand == i) := by
  simp [ofGroups,edge]

def graph {n : Nat} (formula : CNFFormula n) : Graph (Capacity.positives formula).length (groups formula).length :=
  ofGroups (groups formula)

def enabledFor {n d : Nat} (assignment : Nat → Bool) (i : Fin d) (group : List (Item n d)) : Bool :=
  group.any fun item => item.demand == i && assignment item.literal.val

def destination {n d : Nat} (data : List (List (Item n d))) (assignment : Nat → Bool) (i : Fin d) :
    Option (Fin data.length) :=
  (List.finRange data.length).find? fun j => enabledFor assignment i (data.get j)

def fromAssignment {n d : Nat} (data : List (List (Item n d))) (assignment : Nat → Bool) : Matching d data.length :=
  Vector.ofFn fun j => (List.finRange d).find? fun i => destination data assignment i == some j

theorem assigned_spec {n d : Nat} (data : List (List (Item n d))) (assignment : Nat → Bool)
    (j : Fin data.length) (i : Fin d) (found : owner (fromAssignment data assignment) j = some i) :
    destination data assignment i = some j := by
  have result : (List.finRange d).find? (fun i => destination data assignment i == some j) = some i := by
    simpa [fromAssignment,owner] using found
  simpa using List.find?_some result

theorem destination_spec {n d : Nat} (data : List (List (Item n d))) (assignment : Nat → Bool)
    (i : Fin d) (j : Fin data.length) (found : destination data assignment i = some j) :
    enabledFor assignment i (data.get j) = true := by
  simpa only using List.find?_some (show
    (List.finRange data.length).find? (fun k => enabledFor assignment i (data.get k)) = some j from found)

theorem assignment_valid {n d : Nat} (data : List (List (Item n d))) (assignment : Nat → Bool) :
    Valid (ofGroups data) (fromAssignment data assignment) := by
  constructor
  · intro j i found
    have visited := destination_spec data assignment i j (assigned_spec data assignment j i found)
    obtain ⟨item,member,accepted⟩ := List.any_eq_true.mp visited
    simp only [Bool.and_eq_true] at accepted
    have label : item.demand == i := accepted.1
    rw [edge_groups]
    exact List.any_eq_true.mpr ⟨item,member,label⟩
  · intro j k i first second
    exact Option.some.inj ((assigned_spec data assignment j i first).symm.trans
      (assigned_spec data assignment k i second))

theorem enabled_member {n d : Nat} (assignment : Nat → Bool) (group : List (Item n d)) (item : Item n d)
    (member : item ∈ group) (accepted : assignment item.literal.val = true) :
    1 ≤ Capacity.enabled assignment (group.map (·.literal)) := by
  apply Capacity.enabled_positive
  exact List.any_eq_true.mpr ⟨item.literal,List.mem_map.mpr ⟨item,member,rfl⟩,accepted⟩

theorem enabled_unique {n d : Nat} (assignment : Nat → Bool) (group : List (Item n d))
    (bound : Capacity.enabled assignment (group.map (·.literal)) ≤ 1)
    (a b : Item n d) (first : a ∈ group) (second : b ∈ group)
    (left : assignment a.literal.val = true) (right : assignment b.literal.val = true) : a=b := by
  induction group with
  | nil => cases first
  | cons head rest ih =>
      have total : (if assignment head.literal.val then 1 else 0)+
          Capacity.enabled assignment (rest.map (·.literal)) ≤ 1 := bound
      have tail : Capacity.enabled assignment (rest.map (·.literal)) ≤ 1 := by omega
      rcases List.mem_cons.mp first with rfl | firstTail
      · rcases List.mem_cons.mp second with rfl | secondTail
        · rfl
        · have positive := enabled_member assignment rest b secondTail right
          rw [left] at total
          simp only [if_true] at total
          omega
      · rcases List.mem_cons.mp second with rfl | secondTail
        · have positive := enabled_member assignment rest a firstTail left
          rw [right] at total
          simp only [if_true] at total
          omega
        · exact ih tail firstTail secondTail

theorem enabledFor_unique {n d : Nat} (assignment : Nat → Bool) (group : List (Item n d))
    (bound : Capacity.enabled assignment (group.map (·.literal)) ≤ 1)
    (i k : Fin d) (left : enabledFor assignment i group = true) (right : enabledFor assignment k group = true) : i=k := by
  obtain ⟨a,memberA,readA⟩ := List.any_eq_true.mp left
  obtain ⟨b,memberB,readB⟩ := List.any_eq_true.mp right
  simp only [Bool.and_eq_true,beq_iff_eq] at readA readB
  have same := enabled_unique assignment group bound a b memberA memberB readA.2 readB.2
  exact readA.1.symm.trans ((congrArg Item.demand same).trans readB.1)

theorem assignment_covers {n d : Nat} (data : List (List (Item n d))) (assignment : Nat → Bool)
    (bound : ∀ j : Fin data.length, Capacity.enabled assignment ((data.get j).map (·.literal)) ≤ 1)
    (required : ∀ i : Fin d, ∃ j : Fin data.length, enabledFor assignment i (data.get j) = true) :
    ∀ i, covers (fromAssignment data assignment) i = true := by
  intro i
  obtain ⟨candidate,available⟩ := required i
  have found : ∃ j, destination data assignment i = some j := by
    cases result : destination data assignment i with
    | none =>
        have rejected := List.find?_eq_none.mp result candidate (List.mem_finRange candidate)
        rw [available] at rejected
        exact False.elim (rejected rfl)
    | some j => exact ⟨j,rfl⟩
  obtain ⟨j,selected⟩ := found
  have result : ∃ k, owner (fromAssignment data assignment) j = some k := by
    cases found : owner (fromAssignment data assignment) j with
    | none =>
        have empty : (List.finRange d).find? (fun k => destination data assignment k == some j) = none := by
          simpa [owner,fromAssignment] using found
        have rejected := List.find?_eq_none.mp empty i (List.mem_finRange i)
        simp [selected] at rejected
    | some k => exact ⟨k,rfl⟩
  obtain ⟨k,present⟩ := result
  have same : i=k := enabledFor_unique assignment (data.get j) (bound j) i k
    (destination_spec data assignment i j selected)
    (destination_spec data assignment k j (assigned_spec data assignment j k present))
  subst k
  exact (covers_iff _ _).mpr ⟨j,present⟩

theorem groups_required {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) (i : Fin (Capacity.positives formula).length) :
    ∃ j : Fin (groups formula).length, enabledFor assignment i ((groups formula).get j) = true := by
  have positive := Capacity.positives_satisfied formula assignment accepted ((Capacity.positives formula).get i)
    (List.get_mem _ _)
  obtain ⟨literal,member,value⟩ := List.any_eq_true.mp positive
  have tagged := tag_member (Capacity.positives formula) i literal member
  have retained : (⟨literal,i⟩ : Item n (Capacity.positives formula).length) ∈ (groups formula).flatten :=
    (partition_perm formula (tags (Capacity.positives formula))).mem_iff.mpr tagged
  obtain ⟨group,groupMember,itemMember⟩ := List.mem_flatten.mp retained
  apply (List.exists_mem_iff_get (l := groups formula)
    (p := fun group => enabledFor assignment i group = true)).mp
  refine ⟨group,groupMember,?_⟩
  apply List.any_eq_true.mpr
  exact ⟨⟨literal,i⟩,itemMember,by simp [value]⟩

theorem source_admits {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) :
    ∃ table, Valid (graph formula) table ∧ ∀ i, covers table i = true := by
  refine ⟨fromAssignment (groups formula) assignment,assignment_valid _ _,?_⟩
  apply assignment_covers _ _ _ (groups_required formula assignment accepted)
  intro j
  exact Capacity.group_upper formula assignment accepted _ (groups_good formula _ (List.get_mem _ _))

def possible {n : Nat} (formula : CNFFormula n) : Bool := CapacityMatching.possible (graph formula)

theorem possible_of_satisfied {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : possible formula = true :=
  (CapacityMatching.possible_correct (graph formula)).mpr (source_admits formula assignment accepted)

theorem rejected_unsatisfiable {n : Nat} (formula : CNFFormula n) (rejected : possible formula = false) :
    ¬ CNFSatisfiable formula := by
  rintro ⟨assignment,accepted⟩
  have result := possible_of_satisfied formula assignment accepted
  rw [rejected] at result
  cases result

theorem rejected_projector {n : Nat} (formula : CNFFormula n) (rejected : possible formula = false) :
    zeroProjector formula = 0 := by
  apply LinearMap.ext
  intro source
  funext assignment
  have value : CNFFormula.eval formula (extendAssignment assignment) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun accepted => rejected_unsatisfiable formula rejected ⟨extendAssignment assignment,accepted⟩
  rw [zeroProjector_apply,value]
  rfl

theorem graph_cells {n : Nat} (formula : CNFFormula n) :
    (Capacity.positives formula).length*(groups formula).length ≤ formula.length*Extract.literalCount formula :=
  Nat.mul_le_mul (Capacity.positives_length formula) (groups_length formula)

theorem matching_visits {n : Nat} (formula : CNFFormula n) :
    (generate (graph formula)).visits ≤
      (formula.length+1)*solveUnits formula.length (Extract.literalCount formula)+Extract.literalCount formula+1 := by
  have first := generate_visits (graph formula)
  have demands := Capacity.positives_length formula
  have supply := groups_length formula
  apply first.trans
  unfold solveUnits roundUnits
  gcongr

end SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.Source
