import H0mework.Fock.SourceHistory.CountedObservation.Mixture

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

def capacity (table : SourceCountedObservation.Table Fine) : Nat :=
  table.keys.toFinset.sup (fun key => (SourceCountedObservation.lookup table key).hilbert.size)

def mergeEntry (table : SourceCountedObservation.Table Fine) (forget : Fine → Coarse) (coarse : Coarse) :
    SourceCountedObservation.Entry where
  count := SourceCountedObservation.total table forget coarse
  hilbert := Array.ofFn (fun position : Fin (capacity table) =>
    ∑ key ∈ table.keys.toFinset, if forget key = coarse then
      SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert position.val else 0)
  mass := ∑ key ∈ table.keys.toFinset, if forget key = coarse then (SourceCountedObservation.lookup table key).mass else 0
  clock := ∑ key ∈ table.keys.toFinset, if forget key = coarse then (SourceCountedObservation.lookup table key).clock else 0

def mergeTable (table : SourceCountedObservation.Table Fine) (forget : Fine → Coarse) :
    SourceCountedObservation.Table Coarse :=
  SourceCountedObservation.collect (table.keys.map forget) (mergeEntry table forget)

theorem merge_keys (table : SourceCountedObservation.Table Fine) (forget : Fine → Coarse) (coarse : Coarse) :
    coarse ∈ mergeTable table forget ↔ coarse ∈ table.keys.toFinset.image forget := by
  rw [mergeTable, SourceCountedObservation.collect_keys]
  simp only [List.mem_map, Finset.mem_image, List.mem_toFinset]

theorem lookup_merge (table : SourceCountedObservation.Table Fine) (forget : Fine → Coarse) (coarse : Coarse) :
    SourceCountedObservation.lookup (mergeTable table forget) coarse =
      if coarse ∈ table.keys.toFinset.image forget then mergeEntry table forget coarse else SourceCountedObservation.emptyEntry := by
  have membership : coarse ∈ table.keys.map forget ↔ coarse ∈ table.keys.toFinset.image forget := by
    simp only [List.mem_map, Finset.mem_image, List.mem_toFinset]
  rw [SourceCountedObservation.lookup, mergeTable, SourceCountedObservation.collect_lookup]
  by_cases present : coarse ∈ table.keys.toFinset.image forget
  · rw [if_pos (membership.mpr present), Option.getD_some, if_pos present]
  · rw [if_neg (fun inside => present (membership.mp inside)), Option.getD_none, if_neg present]

theorem mergeEntry_coordinate (table : SourceCountedObservation.Table Fine) (forget : Fine → Coarse)
    (coarse : Coarse) (position : Nat) :
    SourceCountedObservation.coordinate (mergeEntry table forget coarse).hilbert position =
      ∑ key ∈ table.keys.toFinset, if forget key = coarse then
        SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert position else 0 := by
  rw [mergeEntry, SourceCountedObservation.coordinate, Array.getElem?_ofFn]
  by_cases inside : position < capacity table
  · rw [dif_pos inside, Option.getD_some]
  · rw [dif_neg inside, Option.getD_none]
    symm
    apply Finset.sum_eq_zero
    intro key present
    by_cases selected : forget key = coarse
    · have fits : (SourceCountedObservation.lookup table key).hilbert.size ≤ capacity table := by
        unfold capacity
        exact Finset.le_sup (f := fun item : Fine => (SourceCountedObservation.lookup table item).hilbert.size) present
      rw [if_pos selected, SourceCountedObservation.coordinate,
        Array.getElem?_eq_none (by omega), Option.getD_none]
    · exact if_neg selected

end SourceCountedMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
