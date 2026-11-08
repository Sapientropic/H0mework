import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Scaling
import Mathlib.Data.List.ProdSigma

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network

private def searchAssignments {Key Result : Type*} [DecidableEq Key] (limit : Key → Nat)
    (visit : (Key → Nat) → Option Result) : List Key → (Key → Nat) → Option Result
  | [], current => visit current
  | key :: tail, current =>
      (List.range (limit key + 1)).findSome? fun amount =>
        searchAssignments limit visit tail (Function.update current key amount)

private theorem searchAssignments_covers {Key Result : Type*} [DecidableEq Key]
    (limit : Key → Nat) (visit : (Key → Nat) → Option Result)
    (keys : List Key) (current target : Key → Nat)
    (bounded : ∀ key ∈ keys, target key ≤ limit key)
    (fixed : ∀ key, key ∉ keys → current key = target key)
    (wanted : (visit target).isSome) :
    (searchAssignments limit visit keys current).isSome := by
  induction keys generalizing current with
  | nil =>
    have same : current = target := funext fun key => fixed key (List.not_mem_nil)
    simpa only [searchAssignments, same] using wanted
  | cons first tail previous =>
    unfold searchAssignments
    apply List.findSome?_isSome_iff.mpr
    refine ⟨target first, List.mem_range.mpr (Nat.lt_succ_of_le (bounded first List.mem_cons_self)), ?_⟩
    apply previous
    · intro key member
      exact bounded key (List.mem_cons_of_mem _ member)
    · intro key absent
      by_cases same : key = first
      · subst key
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne same]
        exact fixed key (fun found => (List.mem_cons.mp found).elim same absent)

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

private def groupOf (bits : L → Nat) : Finset L :=
  Finset.univ.filter fun slot => bits slot = 1

private def searchCuts (network : Network L R) (slots : List L) (allocation : L → R → ℚ) :
    Option (network.Certificate) :=
  searchAssignments (fun _ => 1) (fun bits => network.check allocation (groupOf bits)) slots (fun _ => 0)

omit [DecidableEq R] in
private theorem searchCuts_covers (network : Network L R) (slots : List L) (allSlots : ∀ slot, slot ∈ slots)
    (allocation : L → R → ℚ) (group : Finset L) (admitted : network.Admissible allocation)
    (tight : total allocation = network.cut group) : (searchCuts network slots allocation).isSome := by
  let bits : L → Nat := fun slot => if slot ∈ group then 1 else 0
  have recovered : groupOf bits = group := by
    ext slot
    by_cases member : slot ∈ group <;> simp [groupOf, bits, member]
  apply searchAssignments_covers _ _ _ _ bits
  · intro slot _
    by_cases member : slot ∈ group <;> simp [bits, member]
  · intro slot missing
    exact (missing (allSlots slot)).elim
  · simp [recovered, check, admitted, tight]

/-- Finite fallback on the exact common-denominator lattice. The grid,
bounds and enumerated positions are all computed from the input. -/
def gridSearch (network : Network L R) (slots : List L) (items : List R) : Option (network.Certificate) :=
  let limit : L × R → Nat := fun edge => scaledAmount network.scale (network.need edge.1)
  let visit := fun candidate : L × R → Nat =>
    searchCuts network slots (network.unscale fun slot item => candidate (slot, item))
  searchAssignments limit visit (slots.product items) (fun _ => 0)

theorem gridSearch_returns_an_exact_certificate (network : Network L R)
    (slots : List L) (items : List R) (allSlots : ∀ slot, slot ∈ slots) (allItems : ∀ item, item ∈ items) :
    (network.gridSearch slots items).isSome := by
  obtain ⟨allocation, group, bounded, admitted, tight⟩ := network.exists_grid_certificate
  apply searchAssignments_covers _ _ _ _ (fun edge => allocation edge.1 edge.2)
  · intro edge _
    exact bounded edge.1 edge.2
  · intro edge missing
    exact (missing (List.mem_product.mpr ⟨allSlots edge.1, allItems edge.2⟩)).elim
  · exact searchCuts_covers network slots allSlots _ group admitted tight

end SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network
