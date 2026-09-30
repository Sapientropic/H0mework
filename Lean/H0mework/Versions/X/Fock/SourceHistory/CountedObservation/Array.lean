import H0mework.Versions.X.Fock.RetainedCoarsening.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

def coordinate (data : Array ℚ) (position : Nat) : ℚ := (data[position]?).getD 0

def grow (data : Array ℚ) (size : Nat) : Array ℚ := data ++ Array.replicate (size - data.size) 0

def addAt (data : Array ℚ) (position : Nat) (amount : ℚ) : Array ℚ :=
  (grow data (position + 1)).modify position (fun previous => previous + amount)

theorem grow_at (data : Array ℚ) (size position : Nat) : coordinate (grow data size) position = coordinate data position := by
  simp only [coordinate, grow, Array.getElem?_append]
  split_ifs with inside
  · rfl
  · rw [show data[position]? = none from Array.getElem?_eq_none (by omega), Option.getD_none,
      Array.getElem?_replicate]
    split_ifs <;> rfl

theorem grow_size (data : Array ℚ) (size : Nat) : (grow data size).size = max data.size size := by
  simp only [grow, Array.size_append, Array.size_replicate]
  omega

theorem addAt_at (data : Array ℚ) (position : Nat) (amount : ℚ) (query : Nat) :
    coordinate (addAt data position amount) query = coordinate data query + if query = position then amount else 0 := by
  dsimp only [coordinate, addAt]
  rw [Array.getElem?_modify]
  by_cases selected : query = position
  · subst query
    rw [if_pos rfl]
    have included : position < (grow data (position + 1)).size := by rw [grow_size]; omega
    rw [Array.getElem?_eq_getElem included]
    simp only [Option.map_some, Option.getD_some, ↓reduceIte]
    have previous := grow_at data (position + 1) position
    simpa only [coordinate, Array.getElem?_eq_getElem included, Option.getD_some] using
      congrArg (fun scalar : ℚ => scalar + amount) previous
  · rw [if_neg (Ne.symm selected), if_neg selected, add_zero]
    exact grow_at data (position + 1) query

end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
