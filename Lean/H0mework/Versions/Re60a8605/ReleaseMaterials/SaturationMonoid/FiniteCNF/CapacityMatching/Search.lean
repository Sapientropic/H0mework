import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.Core

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching

structure ReachValid {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (root : Fin m) (entries : List (Entry m r)) : Prop where
  nodup : (seen entries).Nodup
  start : root ∈ seen entries
  relocations : ∀ entry ∈ entries, Relocation graph base root (seen entries) entry

theorem reach_length {m r : Nat} {graph : Graph m r} {base : Matching m r}
    {root : Fin m} {entries : List (Entry m r)} (valid : ReachValid graph base root entries) :
    entries.length ≤ m := by
  simpa only [seen,List.length_map,Fintype.card_fin] using valid.nodup.length_le_card

theorem reach_initial {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (valid : Valid graph base) (root : Fin m) (free : covers base root = false) :
    ReachValid graph base root [⟨root,base⟩] := by
  refine ⟨by simp [seen],by simp [seen],?_⟩
  intro entry member
  have same : entry = ⟨root,base⟩ := List.mem_singleton.mp member
  subst entry
  exact initial_relocation graph base valid root free

theorem reach_advance {m r : Nat} (graph : Graph m r) (base : Matching m r) (root : Fin m)
    (entries : List (Entry m r)) (valid : ReachValid graph base root entries)
    (entry : Entry m r) (present : entry ∈ entries) (j : Fin r) (next : Fin m)
    (hit : owner base j = some next) (fresh : next ∉ seen entries) (adjacent : edge graph entry.demand j = true) :
    ReachValid graph base root (⟨next,write entry.table j entry.demand⟩ :: entries) := by
  refine ⟨List.nodup_cons.mpr ⟨fresh,valid.nodup⟩,List.mem_cons_of_mem _ valid.start,?_⟩
  intro other member
  rcases List.mem_cons.mp member with same | tail
  · subst other
    exact relocation_advance graph base root (seen entries) entry (valid.relocations entry present)
      (List.mem_map.mpr ⟨entry,present,rfl⟩) j next hit fresh adjacent
  · exact relocation_weaken (valid.relocations other tail) (by intro i member; exact List.mem_cons_of_mem _ member)

structure Cut (m r : Nat) where
  demands : List (Fin m)
  groups : List (Fin r)
  deriving DecidableEq,Repr

def cut {m r : Nat} (graph : Graph m r) (entries : List (Entry m r)) : Cut m r :=
  ⟨seen entries,neighbors graph (seen entries)⟩

def Cut.Correct {m r : Nat} (graph : Graph m r) (value : Cut m r) : Prop :=
  value.demands.Nodup ∧ value.groups = neighbors graph value.demands ∧ value.groups.length < value.demands.length

inductive Answer (m r : Nat)
  | matched (table : Matching m r)
  | deficient (cut : Cut m r)
  deriving Repr

structure Run (m r : Nat) where
  answer : Answer m r
  visits : Nat
  deriving Repr

def cutUnits (size r : Nat) : Nat := size+(r+1)*(size+1)+5

def search {m r : Nat} (graph : Graph m r) (base : Matching m r) :
    Nat → List (Entry m r) → Run m r
  | 0, entries => ⟨.deficient (cut graph entries),cutUnits entries.length r⟩
  | fuel+1, entries =>
      let found := scan graph base entries
      match found.candidate with
      | none => ⟨.deficient (cut graph entries),found.visits+cutUnits entries.length r⟩
      | some (entry,j) =>
          match owner base j with
          | none => ⟨.matched (write entry.table j entry.demand),found.visits+r+2⟩
          | some next =>
              let continued := search graph base fuel (⟨next,write entry.table j entry.demand⟩ :: entries)
              ⟨continued.answer,found.visits+r+continued.visits+3⟩

def AugmentSpec {m r : Nat} (graph : Graph m r) (base : Matching m r) (root : Fin m) : Answer m r → Prop
  | .matched table => Valid graph table ∧ ∀ i, covers table i = true ↔ i=root ∨ covers base i = true
  | .deficient value => value.Correct graph

theorem search_correct {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (matching : Valid graph base) (root : Fin m) (free : covers base root = false)
    (fuel : Nat) (entries : List (Entry m r)) (valid : ReachValid graph base root entries)
    (enough : m+1 ≤ fuel+entries.length) : AugmentSpec graph base root (search graph base fuel entries).answer := by
  induction fuel generalizing entries with
  | zero =>
      have size := reach_length valid
      omega
  | succ fuel ih =>
      cases found : (scan graph base entries).candidate with
      | none =>
          simp only [search,found,AugmentSpec,Cut.Correct,cut]
          exact ⟨valid.nodup,trivial,hall_from_closed graph base matching root free (seen entries)
            valid.nodup valid.start (scan_none graph base entries found)⟩
      | some pair =>
          obtain ⟨entry,j⟩ := pair
          have source := scan_some graph base entries entry j found
          cases occupied : owner base j with
          | none =>
              simpa only [search,found,occupied,AugmentSpec] using
                relocation_finish graph base root (seen entries) entry (valid.relocations entry source.1) j occupied source.2.1
          | some next =>
              have fresh : next ∉ seen entries := by
                simpa [occupied] using source.2.2
              have updated := reach_advance graph base root entries valid entry source.1 j next occupied fresh source.2.1
              simpa only [search,found,occupied] using ih _ updated (by simp only [List.length_cons]; omega)

def roundUnits (m r : Nat) : Nat := 20*(m+1)^2*(r+1)

theorem round_covers_scan {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (entries : List (Entry m r)) (size : entries.length ≤ m) :
    (scan graph base entries).visits + cutUnits entries.length r + r + 3 ≤ roundUnits m r := by
  have bound := scan_visits graph base entries
  have first := Nat.mul_le_mul (Nat.mul_le_mul_right r size) (Nat.add_le_add_right size 9)
  have second := Nat.mul_le_mul_left (r+1) (Nat.add_le_add_right size 1)
  unfold cutUnits roundUnits
  nlinarith [Nat.zero_le (m*m*r),Nat.zero_le (m*r),Nat.zero_le (m*m)]

theorem search_visits {m r : Nat} (graph : Graph m r) (base : Matching m r) (root : Fin m)
    (fuel : Nat) (entries : List (Entry m r)) (valid : ReachValid graph base root entries) :
    (search graph base fuel entries).visits ≤ (fuel+1)*roundUnits m r := by
  induction fuel generalizing entries with
  | zero =>
      have bound := round_covers_scan graph base entries (reach_length valid)
      simpa only [search,Nat.zero_add,Nat.one_mul] using (show cutUnits entries.length r ≤ roundUnits m r by omega)
  | succ fuel ih =>
      have bound := round_covers_scan graph base entries (reach_length valid)
      cases found : (scan graph base entries).candidate with
      | none => simp only [search,found]; nlinarith
      | some pair =>
          obtain ⟨entry,j⟩ := pair
          have source := scan_some graph base entries entry j found
          cases occupied : owner base j with
          | none => simp only [search,found,occupied]; nlinarith
          | some next =>
              have fresh : next ∉ seen entries := by
                simpa [occupied] using source.2.2
              have updated := reach_advance graph base root entries valid entry source.1 j next occupied fresh source.2.1
              have tail := ih _ updated
              simp only [search,found,occupied]
              nlinarith

def augment {m r : Nat} (graph : Graph m r) (base : Matching m r) (root : Fin m) : Run m r :=
  search graph base m [⟨root,base⟩]

theorem augment_correct {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (valid : Valid graph base) (root : Fin m) (free : covers base root = false) :
    AugmentSpec graph base root (augment graph base root).answer :=
  search_correct graph base valid root free m _ (reach_initial graph base valid root free) (by simp)

theorem augment_visits {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (valid : Valid graph base) (root : Fin m) (free : covers base root = false) :
    (augment graph base root).visits ≤ (m+1)*roundUnits m r :=
  search_visits graph base root m _ (reach_initial graph base valid root free)

def solve {m r : Nat} (graph : Graph m r) : List (Fin m) → Matching m r → Run m r
  | [], base => ⟨.matched base,1⟩
  | i::rest, base =>
      if covers base i then
        let tail := solve graph rest base
        ⟨tail.answer,tail.visits+r+2⟩
      else
        let advanced := augment graph base i
        match advanced.answer with
        | .deficient value => ⟨.deficient value,advanced.visits+r+2⟩
        | .matched next =>
            let tail := solve graph rest next
            ⟨tail.answer,advanced.visits+tail.visits+r+2⟩

def SolveSpec {m r : Nat} (graph : Graph m r) (base : Matching m r) (needed : List (Fin m)) : Answer m r → Prop
  | .matched table => Valid graph table ∧ ∀ i, (i ∈ needed ∨ covers base i = true) → covers table i = true
  | .deficient value => value.Correct graph

theorem solve_correct {m r : Nat} (graph : Graph m r) (needed : List (Fin m)) (base : Matching m r)
    (valid : Valid graph base) : SolveSpec graph base needed (solve graph needed base).answer := by
  induction needed generalizing base with
  | nil => exact ⟨valid,by simp⟩
  | cons i rest ih =>
      by_cases covered : covers base i = true
      · have tail := ih base valid
        simp only [solve,covered,if_true]
        cases produced : (solve graph rest base).answer with
        | deficient value => simpa only [produced,SolveSpec] using tail
        | matched table =>
            rw [produced] at tail
            refine ⟨tail.1,?_⟩
            intro j reason
            apply tail.2
            rcases reason with member | present
            · rcases List.mem_cons.mp member with same | next
              · subst j
                exact Or.inr covered
              · exact Or.inl next
            · exact Or.inr present
      · have free : covers base i = false := Bool.eq_false_iff.mpr covered
        have upgraded := augment_correct graph base valid i free
        cases advanced : (augment graph base i).answer with
        | deficient value => simpa only [solve,free,Bool.false_eq_true,if_false,advanced,SolveSpec,AugmentSpec] using upgraded
        | matched next =>
            rw [advanced] at upgraded
            have tail := ih next upgraded.1
            simp only [solve,free,Bool.false_eq_true,if_false,advanced]
            cases produced : (solve graph rest next).answer with
            | deficient value => simpa only [produced,SolveSpec] using tail
            | matched table =>
                rw [produced] at tail
                refine ⟨tail.1,?_⟩
                intro j reason
                apply tail.2
                rcases reason with member | present
                · rcases List.mem_cons.mp member with same | next
                  · exact Or.inr ((upgraded.2 j).mpr (Or.inl same))
                  · exact Or.inl next
                · exact Or.inr ((upgraded.2 j).mpr (Or.inr present))

def solveUnits (m r : Nat) : Nat := (m+1)*roundUnits m r+r+3

theorem solve_visits {m r : Nat} (graph : Graph m r) (needed : List (Fin m)) (base : Matching m r)
    (valid : Valid graph base) : (solve graph needed base).visits ≤ (needed.length+1)*solveUnits m r := by
  induction needed generalizing base with
  | nil => simp [solve,solveUnits,roundUnits]
  | cons i rest ih =>
      by_cases covered : covers base i = true
      · have tail := ih base valid
        simp only [solve,covered,if_true,List.length_cons]
        unfold solveUnits at *
        nlinarith
      · have free : covers base i = false := Bool.eq_false_iff.mpr covered
        have bound := augment_visits graph base valid i free
        have correct := augment_correct graph base valid i free
        cases advanced : (augment graph base i).answer with
        | deficient value =>
            simp only [solve,free,Bool.false_eq_true,if_false,advanced,List.length_cons]
            unfold solveUnits
            nlinarith
        | matched next =>
            rw [advanced] at correct
            have tail := ih next correct.1
            simp only [solve,free,Bool.false_eq_true,if_false,advanced,List.length_cons]
            unfold solveUnits at *
            nlinarith

def generate {m r : Nat} (graph : Graph m r) : Run m r :=
  let result := solve graph (List.finRange m) (empty m r)
  ⟨result.answer,result.visits+r+1⟩

theorem generate_correct {m r : Nat} (graph : Graph m r) :
    match (generate graph).answer with
    | .matched table => Valid graph table ∧ ∀ i, covers table i = true
    | .deficient value => value.Correct graph := by
  have result := solve_correct graph (List.finRange m) (empty m r) (empty_valid graph)
  cases produced : (solve graph (List.finRange m) (empty m r)).answer <;>
    simpa only [generate,produced,SolveSpec,List.mem_finRange,true_or,forall_true_left] using result

theorem generate_visits {m r : Nat} (graph : Graph m r) :
    (generate graph).visits ≤ (m+1)*solveUnits m r+r+1 := by
  have result := solve_visits graph (List.finRange m) (empty m r) (empty_valid graph)
  simpa only [generate,List.length_finRange] using Nat.add_le_add_right (Nat.add_le_add_right result r) 1

theorem cut_no_cover {m r : Nat} (graph : Graph m r) (value : Cut m r)
    (deficient : value.Correct graph) (table : Matching m r) (valid : Valid graph table)
    (covered : ∀ i, covers table i = true) : False := by
  classical
  choose assigned assigned_eq using fun i => (covers_iff table i).mp (covered i)
  have bound := Finset.card_le_card_of_injOn assigned
    (s := value.demands.toFinset) (t := (neighbors graph value.demands).toFinset) ?_ ?_
  · rw [List.toFinset_card_of_nodup deficient.1,
      List.toFinset_card_of_nodup (neighbors_nodup graph value.demands),← deficient.2.1] at bound
    exact Nat.not_lt_of_ge bound deficient.2.2
  · intro i member
    exact List.mem_toFinset.mpr ((mem_neighbors graph value.demands (assigned i)).mpr
      ⟨i,List.mem_toFinset.mp member,valid.adjacent _ _ (assigned_eq i)⟩)
  · intro i _ j _ equal
    exact Option.some.inj ((assigned_eq i).symm.trans (equal ▸ assigned_eq j))

def possible {m r : Nat} (graph : Graph m r) : Bool :=
  match (generate graph).answer with
  | .matched _ => true
  | .deficient _ => false

theorem possible_correct {m r : Nat} (graph : Graph m r) :
    possible graph = true ↔ ∃ table : Matching m r, Valid graph table ∧ ∀ i, covers table i = true := by
  have sound := generate_correct graph
  cases produced : (generate graph).answer with
  | matched table =>
      simp only [possible,produced,true_iff]
      exact ⟨table,by simpa only [produced] using sound⟩
  | deficient value =>
      simp only [possible,produced,Bool.false_eq_true,false_iff]
      rintro ⟨table,valid,covered⟩
      exact cut_no_cover graph value (by simpa only [produced] using sound) table valid covered

theorem reach_storage {m r : Nat} {graph : Graph m r} {base : Matching m r}
    {root : Fin m} {entries : List (Entry m r)} (valid : ReachValid graph base root entries) :
    entries.length*(r+1) ≤ m*(r+1) ∧ (pairs entries).length*(r+2) ≤ m*r*(r+2) := by
  have bound := reach_length valid
  refine ⟨Nat.mul_le_mul_right _ bound,?_⟩
  rw [pairs_length]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right r bound)

def answerCells {m r : Nat} : Answer m r → Nat
  | .matched _ => r
  | .deficient value => value.demands.length+value.groups.length

theorem generate_storage {m r : Nat} (graph : Graph m r) : answerCells (generate graph).answer ≤ m+r := by
  have sound := generate_correct graph
  cases produced : (generate graph).answer with
  | matched table => simp [answerCells]
  | deficient value =>
      simp only [produced] at sound
      have first : value.demands.length ≤ m := by simpa only [Fintype.card_fin] using sound.1.length_le_card
      have second : value.groups.length ≤ r := by
        rw [sound.2.1]
        exact (List.length_filter_le _ (List.finRange r)).trans_eq List.length_finRange
      simp only [answerCells]
      omega

end SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching
