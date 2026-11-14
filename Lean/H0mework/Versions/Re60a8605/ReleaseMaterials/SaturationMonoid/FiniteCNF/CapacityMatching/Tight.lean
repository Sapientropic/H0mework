import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.Search

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.Tight

def without {m r : Nat} (graph : Graph m r) (removed : Fin r) : Graph m r :=
  Vector.ofFn fun i => Vector.ofFn fun j => edge graph i j && decide (j ≠ removed)

theorem edge_without {m r : Nat} (graph : Graph m r) (removed j : Fin r) (i : Fin m) :
    edge (without graph removed) i j = (edge graph i j && decide (j ≠ removed)) := by
  simp [edge,without]

theorem mem_without {m r : Nat} (graph : Graph m r) (removed : Fin r) (demands : List (Fin m)) (j : Fin r) :
    j ∈ neighbors (without graph removed) demands ↔ j ∈ neighbors graph demands ∧ j ≠ removed := by
  rw [mem_neighbors,mem_neighbors]
  constructor
  · rintro ⟨i,member,found⟩
    rw [edge_without,Bool.and_eq_true,decide_eq_true_eq] at found
    exact ⟨⟨i,member,found.1⟩,found.2⟩
  · rintro ⟨⟨i,member,found⟩,kept⟩
    exact ⟨i,member,by simp [edge_without,found,kept]⟩

theorem neighbors_without_bound {m r : Nat} (graph : Graph m r) (removed : Fin r) (demands : List (Fin m)) :
    (neighbors graph demands).length ≤ (neighbors (without graph removed) demands).length+1 := by
  have included : (neighbors graph demands).toFinset ⊆
      insert removed (neighbors (without graph removed) demands).toFinset := by
    intro j member
    by_cases same : j=removed
    · simp [same]
    · apply Finset.mem_insert_of_mem
      exact List.mem_toFinset.mpr ((mem_without graph removed demands j).mpr ⟨List.mem_toFinset.mp member,same⟩)
  have first := Finset.card_le_card included
  have second := Finset.card_insert_le removed (neighbors (without graph removed) demands).toFinset
  have result := first.trans second
  simpa only [List.toFinset_card_of_nodup (neighbors_nodup graph demands),
    List.toFinset_card_of_nodup (neighbors_nodup (without graph removed) demands)] using result

theorem covered_neighborhood {m r : Nat} (graph : Graph m r) (table : Matching m r)
    (valid : Valid graph table) (covered : ∀ i, covers table i = true)
    (demands : List (Fin m)) (nodup : demands.Nodup) :
    demands.length ≤ (neighbors graph demands).length := by
  classical
  choose assigned assigned_eq using fun i => (covers_iff table i).mp (covered i)
  have bound := Finset.card_le_card_of_injOn assigned
    (s := demands.toFinset) (t := (neighbors graph demands).toFinset) ?_ ?_
  · simpa only [List.toFinset_card_of_nodup nodup,
      List.toFinset_card_of_nodup (neighbors_nodup graph demands)] using bound
  · intro i member
    exact List.mem_toFinset.mpr ((mem_neighbors graph demands (assigned i)).mpr
      ⟨i,List.mem_toFinset.mp member,valid.adjacent _ _ (assigned_eq i)⟩)
  · intro i _ j _ equal
    exact Option.some.inj ((assigned_eq i).symm.trans (equal ▸ assigned_eq j))

def Correct {m r : Nat} (graph : Graph m r) (value : Cut m r) : Prop :=
  value.demands.Nodup ∧ value.groups = neighbors graph value.demands ∧ value.groups.length = value.demands.length

theorem filled {m r : Nat} (graph : Graph m r) (value : Cut m r) (tight : Correct graph value)
    (table : Matching m r) (valid : Valid graph table) (covered : ∀ i, covers table i = true)
    (j : Fin r) (member : j ∈ value.groups) : ∃ i ∈ value.demands, owner table j = some i := by
  classical
  choose assigned assigned_eq using fun i => (covers_iff table i).mp (covered i)
  have mapped : Set.MapsTo assigned value.demands.toFinset value.groups.toFinset := by
    intro i present
    apply List.mem_toFinset.mpr
    rw [tight.2.1,mem_neighbors]
    exact ⟨i,List.mem_toFinset.mp present,valid.adjacent _ _ (assigned_eq i)⟩
  have injective : Set.InjOn assigned value.demands.toFinset := by
    intro i _ k _ equal
    exact Option.some.inj ((assigned_eq i).symm.trans (equal ▸ assigned_eq k))
  have groupsUnique : value.groups.Nodup := by rw [tight.2.1]; exact neighbors_nodup graph value.demands
  have size : value.groups.toFinset.card ≤ value.demands.toFinset.card := by
    rw [List.toFinset_card_of_nodup groupsUnique,List.toFinset_card_of_nodup tight.1,tight.2.2]
  have onto := Finset.surjOn_of_injOn_of_card_le assigned mapped injective size
  obtain ⟨i,present,same⟩ := onto (List.mem_toFinset.mpr member)
  exact ⟨i,List.mem_toFinset.mp present,same ▸ assigned_eq i⟩

def restore {m r : Nat} (graph : Graph m r) (value : Cut m r) : Cut m r :=
  ⟨value.demands,neighbors graph value.demands⟩

theorem restore_correct {m r : Nat} (graph : Graph m r) (removed : Fin r) (table : Matching m r)
    (valid : Valid graph table) (covered : ∀ i, covers table i = true) (value : Cut m r)
    (deficient : value.Correct (without graph removed)) : Correct graph (restore graph value) := by
  refine ⟨deficient.1,rfl,?_⟩
  have lower := covered_neighborhood graph table valid covered value.demands deficient.1
  have upper := neighbors_without_bound graph removed value.demands
  rw [← deficient.2.1] at upper
  have strict := deficient.2.2
  change (neighbors graph value.demands).length = value.demands.length
  omega

def probe {m r : Nat} (graph : Graph m r) (removed : Fin r) : Option (Cut m r) :=
  match (generate (without graph removed)).answer with
  | .matched _ => none
  | .deficient value => some (restore graph value)

theorem probe_correct {m r : Nat} (graph : Graph m r) (removed : Fin r) (table : Matching m r)
    (valid : Valid graph table) (covered : ∀ i, covers table i = true) (value : Cut m r)
    (found : probe graph removed = some value) : Correct graph value := by
  have generated := generate_correct (without graph removed)
  cases result : (generate (without graph removed)).answer with
  | matched other => simp [probe,result] at found
  | deficient cut =>
      have same : restore graph cut = value := by simpa [probe,result] using found
      subst value
      exact restore_correct graph removed table valid covered cut (by simpa only [result] using generated)

def run {m r : Nat} (graph : Graph m r) : List (Cut m r) :=
  match (generate graph).answer with
  | .deficient _ => []
  | .matched _ => (List.finRange r).filterMap (probe graph)

theorem run_correct {m r : Nat} (graph : Graph m r) (value : Cut m r) (member : value ∈ run graph) :
    Correct graph value := by
  have original := generate_correct graph
  cases produced : (generate graph).answer with
  | deficient cut => simp [run,produced] at member
  | matched table =>
      have valid : Valid graph table ∧ ∀ i, covers table i = true := by simpa only [produced] using original
      simp only [run,produced] at member
      obtain ⟨removed,_,found⟩ := List.mem_filterMap.mp member
      exact probe_correct graph removed table valid.1 valid.2 value found

theorem run_length {m r : Nat} (graph : Graph m r) : (run graph).length ≤ r := by
  unfold run
  cases (generate graph).answer
  · exact (List.length_filterMap_le _ _).trans_eq List.length_finRange
  · simp

end SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.Tight
