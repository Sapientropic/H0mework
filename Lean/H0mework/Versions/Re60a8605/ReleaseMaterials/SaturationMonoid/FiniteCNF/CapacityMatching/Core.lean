import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Capacity
import Mathlib.Combinatorics.Hall.Finite

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching

abbrev Graph (m r : Nat) := Vector (Vector Bool r) m
abbrev Matching (m r : Nat) := Vector (Option (Fin m)) r

def edge {m r : Nat} (graph : Graph m r) (i : Fin m) (j : Fin r) : Bool := graph[i.val][j.val]
def owner {m r : Nat} (table : Matching m r) (j : Fin r) : Option (Fin m) := table[j.val]
def empty (m r : Nat) : Matching m r := Vector.replicate r none
def write {m r : Nat} (table : Matching m r) (j : Fin r) (i : Fin m) : Matching m r := table.set j.val (some i)

@[simp] theorem owner_empty (m r : Nat) (j : Fin r) : owner (empty m r) j = none := by simp [owner,empty]

theorem owner_write {m r : Nat} (table : Matching m r) (j k : Fin r) (i : Fin m) :
    owner (write table j i) k = if j=k then some i else owner table k := by
  simp only [owner,write,Vector.getElem_set]
  by_cases equal : j=k
  · subst k
    simp
  · have apart : j.val ≠ k.val := fun same => equal (Fin.ext same)
    simp [equal,apart]

def covers {m r : Nat} (table : Matching m r) (i : Fin m) : Bool :=
  (List.finRange r).any (fun j => owner table j == some i)

theorem covers_iff {m r : Nat} (table : Matching m r) (i : Fin m) :
    covers table i = true ↔ ∃ j, owner table j = some i := by
  simp [covers,List.any_eq_true]

@[simp] theorem covers_empty (m r : Nat) (i : Fin m) : covers (empty m r) i = false := by
  simp [covers]

structure Valid {m r : Nat} (graph : Graph m r) (table : Matching m r) : Prop where
  adjacent : ∀ j i, owner table j = some i → edge graph i j = true
  injective : ∀ j k i, owner table j = some i → owner table k = some i → j=k

theorem empty_valid {m r : Nat} (graph : Graph m r) : Valid graph (empty m r) where
  adjacent := by simp
  injective := by simp

theorem write_valid {m r : Nat} (graph : Graph m r) (table : Matching m r)
    (valid : Valid graph table) (i : Fin m) (j : Fin r)
    (free : covers table i = false) (adjacent : edge graph i j = true) : Valid graph (write table j i) := by
  have absent : ∀ k, owner table k ≠ some i := by
    intro k hit
    have present := (covers_iff table i).mpr ⟨k,hit⟩
    simp [free] at present
  constructor
  · intro k a hit
    rw [owner_write] at hit
    split at hit
    · rename_i equal
      subst k
      cases Option.some.inj hit
      exact adjacent
    · exact valid.adjacent k a hit
  · intro k l a first second
    rw [owner_write] at first second
    split at first <;> split at second
    · rename_i eqk eql
      exact eqk.symm.trans eql
    · have same := Option.some.inj first
      exact False.elim (absent l (same ▸ second))
    · have same := Option.some.inj second
      exact False.elim (absent k (same ▸ first))
    · exact valid.injective k l a first second

theorem covers_write {m r : Nat} (graph : Graph m r) (table : Matching m r)
    (valid : Valid graph table) (i a : Fin m) (j : Fin r) :
    covers (write table j i) a = true ↔ a=i ∨ (covers table a = true ∧ owner table j ≠ some a) := by
  rw [covers_iff,covers_iff]
  constructor
  · rintro ⟨k,hit⟩
    rw [owner_write] at hit
    split at hit
    · exact Or.inl (Option.some.inj hit).symm
    · rename_i apart
      exact Or.inr ⟨⟨k,hit⟩,fun same => apart (valid.injective j k a same hit)⟩
  · rintro (rfl | ⟨⟨k,hit⟩,apart⟩)
    · exact ⟨j,by simp [owner_write]⟩
    · refine ⟨k,?_⟩
      have different : j ≠ k := fun same => apart (same ▸ hit)
      simp [owner_write,different,hit]

structure Entry (m r : Nat) where
  demand : Fin m
  table : Matching m r

def seen {m r : Nat} (entries : List (Entry m r)) : List (Fin m) := entries.map Entry.demand

/-- A finite exchange table for a reached demand; only that demand is currently missing. -/
structure Relocation {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (root : Fin m) (reached : List (Fin m)) (entry : Entry m r) : Prop where
  valid : Valid graph entry.table
  origin : entry.demand = root ∨ covers base entry.demand = true
  domain : ∀ i, covers entry.table i = true ↔ i ≠ entry.demand ∧ (i=root ∨ covers base i = true)
  untouched : ∀ j, (owner base j = none ∨ ∃ i, owner base j = some i ∧ i ∉ reached) →
    owner entry.table j = owner base j

theorem initial_relocation {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (valid : Valid graph base) (root : Fin m) (free : covers base root = false) :
    Relocation graph base root [root] ⟨root,base⟩ := by
  refine ⟨valid,Or.inl rfl,?_,fun _ _ => rfl⟩
  intro i
  by_cases equal : i=root
  · subst i
    simp [free]
  · simp [equal]

theorem relocation_missing {m r : Nat} {graph : Graph m r} {base : Matching m r}
    {root : Fin m} {reached : List (Fin m)} {entry : Entry m r}
    (valid : Relocation graph base root reached entry) : covers entry.table entry.demand = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  exact (valid.domain entry.demand).mp present |>.1 rfl

theorem relocation_weaken {m r : Nat} {graph : Graph m r} {base : Matching m r}
    {root : Fin m} {before after : List (Fin m)} {entry : Entry m r}
    (valid : Relocation graph base root before entry) (subset : before ⊆ after) :
    Relocation graph base root after entry := by
  refine ⟨valid.valid,valid.origin,valid.domain,?_⟩
  intro j reason
  apply valid.untouched j
  rcases reason with empty | ⟨i,hit,outside⟩
  · exact Or.inl empty
  · exact Or.inr ⟨i,hit,fun member => outside (subset member)⟩

theorem relocation_advance {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (root : Fin m) (reached : List (Fin m)) (entry : Entry m r)
    (valid : Relocation graph base root reached entry) (current : entry.demand ∈ reached)
    (j : Fin r) (next : Fin m) (hit : owner base j = some next) (fresh : next ∉ reached)
    (adjacent : edge graph entry.demand j = true) :
    Relocation graph base root (next::reached) ⟨next,write entry.table j entry.demand⟩ := by
  have read : owner entry.table j = some next := (valid.untouched j (Or.inr ⟨next,hit,fresh⟩)).trans hit
  have apart : entry.demand ≠ next := fun equal => fresh (equal ▸ current)
  refine ⟨write_valid graph entry.table valid.valid entry.demand j (relocation_missing valid) adjacent,
    Or.inr ((covers_iff base next).mpr ⟨j,hit⟩),?_,?_⟩
  · intro i
    rw [covers_write graph entry.table valid.valid,valid.domain,read]
    simp only [ne_eq,Option.some.injEq]
    have origin := valid.origin
    by_cases equal : i=entry.demand <;> aesop
  · intro k reason
    have different : j ≠ k := by
      intro same
      subst k
      rcases reason with empty | ⟨i,other,outside⟩
      · rw [hit] at empty
        cases empty
      · have equal : next=i := Option.some.inj (hit.symm.trans other)
        exact outside (by simp [← equal])
    rw [owner_write,if_neg different]
    apply valid.untouched k
    rcases reason with empty | ⟨i,other,outside⟩
    · exact Or.inl empty
    · exact Or.inr ⟨i,other,fun member => outside (by simp [member])⟩

theorem relocation_finish {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (root : Fin m) (reached : List (Fin m)) (entry : Entry m r)
    (valid : Relocation graph base root reached entry) (j : Fin r)
    (free : owner base j = none) (adjacent : edge graph entry.demand j = true) :
    Valid graph (write entry.table j entry.demand) ∧
      ∀ i, covers (write entry.table j entry.demand) i = true ↔ i=root ∨ covers base i = true := by
  have read : owner entry.table j = none := (valid.untouched j (Or.inl free)).trans free
  refine ⟨write_valid graph entry.table valid.valid entry.demand j (relocation_missing valid) adjacent,?_⟩
  intro i
  rw [covers_write graph entry.table valid.valid,valid.domain,read]
  simp only [ne_eq,reduceCtorEq,not_false_eq_true,and_true]
  have origin := valid.origin
  by_cases equal : i=entry.demand <;> aesop

def neighbors {m r : Nat} (graph : Graph m r) (reached : List (Fin m)) : List (Fin r) :=
  (List.finRange r).filter (fun j => reached.any (fun i => edge graph i j))

theorem mem_neighbors {m r : Nat} (graph : Graph m r) (reached : List (Fin m)) (j : Fin r) :
    j ∈ neighbors graph reached ↔ ∃ i ∈ reached, edge graph i j = true := by
  simp [neighbors,List.any_eq_true]

theorem neighbors_nodup {m r : Nat} (graph : Graph m r) (reached : List (Fin m)) :
    (neighbors graph reached).Nodup := (List.nodup_finRange r).filter _

theorem hall_from_closed {m r : Nat} (graph : Graph m r) (base : Matching m r)
    (valid : Valid graph base) (root : Fin m) (free : covers base root = false)
    (reached : List (Fin m)) (nodup : reached.Nodup) (start : root ∈ reached)
    (closed : ∀ i ∈ reached, ∀ j, edge graph i j = true →
      ∃ next, owner base j = some next ∧ next ∈ reached) :
    (neighbors graph reached).length < reached.length := by
  have owned : ∀ j ∈ neighbors graph reached, ∃ next, owner base j = some next ∧ next ∈ reached := by
    intro j member
    obtain ⟨i,present,adjacent⟩ := (mem_neighbors graph reached j).mp member
    exact closed i present j adjacent
  have absent : ∀ j, owner base j ≠ some root := by
    intro j hit
    have present := (covers_iff base root).mpr ⟨j,hit⟩
    simp [free] at present
  let read := fun j => (owner base j).getD root
  have count := Finset.card_le_card_of_injOn read
    (s := (neighbors graph reached).toFinset) (t := reached.toFinset.erase root) ?_ ?_
  · rw [List.toFinset_card_of_nodup (neighbors_nodup graph reached),
      Finset.card_erase_of_mem (List.mem_toFinset.mpr start),List.toFinset_card_of_nodup nodup] at count
    have positive : 0 < reached.length := List.length_pos_iff.mpr (by intro empty; simp [empty] at start)
    omega
  · intro j member
    obtain ⟨next,hit,present⟩ := owned j (List.mem_toFinset.mp member)
    have different : next ≠ root := fun same => absent j (same ▸ hit)
    simp [read,hit,present,different]
  · intro j first k second equal
    obtain ⟨a,left,_⟩ := owned j (List.mem_toFinset.mp first)
    obtain ⟨b,right,_⟩ := owned k (List.mem_toFinset.mp second)
    have same : a=b := by simpa [read,left,right] using equal
    exact valid.injective j k a left (same ▸ right)

def pairs {m r : Nat} (entries : List (Entry m r)) : List (Entry m r × Fin r) :=
  entries.flatMap fun entry => (List.finRange r).map (entry,·)

theorem mem_pairs {m r : Nat} (entries : List (Entry m r)) (entry : Entry m r) (j : Fin r) :
    (entry,j) ∈ pairs entries ↔ entry ∈ entries := by simp [pairs]

theorem pairs_length {m r : Nat} (entries : List (Entry m r)) : (pairs entries).length = entries.length*r := by
  simp [pairs]

def eligible {m r : Nat} (graph : Graph m r) (base : Matching m r) (reached : List (Fin m))
    (pair : Entry m r × Fin r) : Bool :=
  edge graph pair.1.demand pair.2 &&
    match owner base pair.2 with
    | none => true
    | some i => !reached.contains i

structure Scan (m r : Nat) where
  candidate : Option (Entry m r × Fin r)
  visits : Nat

/-- Each inspected pair charges a full possible owner-membership scan plus fixed field reads. -/
def inspect {m r : Nat} (graph : Graph m r) (base : Matching m r) (reached : List (Fin m)) :
    List (Entry m r × Fin r) → Scan m r
  | [] => ⟨none,1⟩
  | pair::rest =>
      if eligible graph base reached pair then ⟨some pair,reached.length+8⟩
      else let next := inspect graph base reached rest
           ⟨next.candidate,next.visits+reached.length+8⟩

theorem inspect_find {m r : Nat} (graph : Graph m r) (base : Matching m r) (reached : List (Fin m))
    (items : List (Entry m r × Fin r)) :
    (inspect graph base reached items).candidate = items.find? (eligible graph base reached) := by
  induction items with
  | nil => rfl
  | cons pair rest ih => simp only [inspect,List.find?_cons]; split <;> simp_all

theorem inspect_visits {m r : Nat} (graph : Graph m r) (base : Matching m r) (reached : List (Fin m))
    (items : List (Entry m r × Fin r)) :
    (inspect graph base reached items).visits ≤ items.length*(reached.length+8)+1 := by
  induction items with
  | nil => simp [inspect]
  | cons pair rest ih => simp only [inspect,List.length_cons]; split <;> simp only <;> nlinarith

def scan {m r : Nat} (graph : Graph m r) (base : Matching m r) (entries : List (Entry m r)) : Scan m r :=
  let read := inspect graph base (seen entries) (pairs entries)
  ⟨read.candidate,read.visits+entries.length*(r+2)+1⟩

theorem scan_visits {m r : Nat} (graph : Graph m r) (base : Matching m r) (entries : List (Entry m r)) :
    (scan graph base entries).visits ≤ entries.length*r*(entries.length+9)+2*entries.length+2 := by
  have bound := inspect_visits graph base (seen entries) (pairs entries)
  simp only [pairs_length,seen,List.length_map] at bound
  simp only [scan,seen]
  nlinarith

theorem scan_some {m r : Nat} (graph : Graph m r) (base : Matching m r) (entries : List (Entry m r))
    (entry : Entry m r) (j : Fin r) (found : (scan graph base entries).candidate = some (entry,j)) :
    entry ∈ entries ∧ edge graph entry.demand j = true ∧
      (owner base j = none ∨ ∃ next, owner base j = some next ∧ next ∉ seen entries) := by
  have read : (pairs entries).find? (eligible graph base (seen entries)) = some (entry,j) := by
    simpa only [scan,inspect_find] using found
  have member := List.mem_of_find?_eq_some read
  have chosen := List.find?_some read
  simp only [eligible,Bool.and_eq_true] at chosen
  have adjacent := chosen.1
  refine ⟨(mem_pairs entries entry j).mp member,adjacent,?_⟩
  cases occupied : owner base j with
  | none => exact Or.inl rfl
  | some next =>
      right
      refine ⟨next,rfl,?_⟩
      simpa [occupied,adjacent] using chosen

theorem scan_none {m r : Nat} (graph : Graph m r) (base : Matching m r) (entries : List (Entry m r))
    (missing : (scan graph base entries).candidate = none) :
    ∀ i ∈ seen entries, ∀ j, edge graph i j = true →
      ∃ next, owner base j = some next ∧ next ∈ seen entries := by
  have read : (pairs entries).find? (eligible graph base (seen entries)) = none := by
    simpa only [scan,inspect_find] using missing
  intro i member j adjacent
  obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
  have absent := List.find?_eq_none.mp read (entry,j) ((mem_pairs entries entry j).mpr present)
  cases occupied : owner base j with
  | none => simp [eligible,adjacent,occupied] at absent
  | some next =>
      refine ⟨next,rfl,?_⟩
      simpa [eligible,adjacent,occupied] using absent

end SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching
