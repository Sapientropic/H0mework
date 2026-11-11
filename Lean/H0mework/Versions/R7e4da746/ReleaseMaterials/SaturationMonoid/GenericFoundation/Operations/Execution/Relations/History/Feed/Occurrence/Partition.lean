import Lean.Elab.Tactic.Omega

set_option autoImplicit false
universe u

namespace SaturationMonoid.OrderedTracePartition

/-- The original block address and offset in a list assembled in order. -/
structure PartAt {G : Type u} (parts whole : Nat → List G) (n position : Nat) where
  block : Fin n
  localIndex : Fin (parts block.val).length
  offset_eq : position = (whole block.val).length + localIndex.val
  read : (whole n)[position]? = (parts block.val)[localIndex.val]?

def locatePart {G : Type u} (parts whole : Nat → List G)
    (empty : whole 0 = []) (advance : ∀ n, whole (n+1) = whole n ++ parts n) :
    (n position : Nat) → position < (whole n).length → PartAt parts whole n position
  | 0, position, inside => by
    rw [empty, List.length_nil] at inside
    exact False.elim (Nat.not_lt_zero position inside)
  | n+1, position, inside => by
    by_cases earlier : position < (whole n).length
    · let found := locatePart parts whole empty advance n position earlier
      refine ⟨found.block.castSucc, found.localIndex, found.offset_eq, ?_⟩
      rw [advance, List.getElem?_append_left earlier]
      exact found.read
    · have later : (whole n).length ≤ position := Nat.le_of_not_gt earlier
      let localIndex := position - (whole n).length
      have valid : localIndex < (parts n).length := by
        rw [advance, List.length_append] at inside
        dsimp only [localIndex]
        omega
      refine ⟨Fin.last n, ⟨localIndex, valid⟩, ?_, ?_⟩
      · change position = (whole n).length + localIndex
        dsimp only [localIndex]
        omega
      · simp only [advance, List.getElem?_append_right later, Fin.val_last, localIndex]

end SaturationMonoid.OrderedTracePartition
