import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Forcing
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyePreservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye.Score

def areaPoints {n : Nat} (board : Board n) (colour : Polarity) : Finset (Point n) :=
  Finset.univ.filter (fun point =>
    board point = some colour ∨ territoryOwner? board point = some colour)

theorem territoryOwner_empty {n : Nat} {board : Board n} {point : Point n}
    {colour : Polarity} (owned : territoryOwner? board point = some colour) :
    board point = none := by
  by_cases empty : board point = none
  · exact empty
  · simp [territoryOwner?, empty] at owned

theorem areaPoints_disjoint {n : Nat} (board : Board n) :
    Disjoint (areaPoints board .positive) (areaPoints board .negative) := by
  apply Finset.disjoint_left.mpr
  intro point black white
  simp only [areaPoints, Finset.mem_filter, Finset.mem_univ, true_and] at black white
  rcases black with black | black <;> rcases white with white | white
  · cases Option.some.inj (black.symm.trans white)
  · have empty := territoryOwner_empty white
    rw [empty] at black
    cases black
  · have empty := territoryOwner_empty black
    rw [empty] at white
    cases white
  · cases Option.some.inj (black.symm.trans white)

theorem areaScore_total_le {n : Nat} (board : Board n) :
    areaScore board .positive + areaScore board .negative ≤ n * n := by
  have count := Finset.card_le_card
    (Finset.subset_univ (areaPoints board .positive ∪ areaPoints board .negative))
  rw [Finset.card_union_of_disjoint (areaPoints_disjoint board)] at count
  simpa only [areaPoints, areaScore, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin] using count

theorem white_margin_bound {n : Nat} (board : Board n) (lower : Nat)
    (area : lower ≤ areaScore board .negative) :
    areaMargin board ≤ ((n * n : Nat) : Int) - 2 * (lower : Int) := by
  have total := areaScore_total_le board
  unfold areaMargin
  omega

theorem black_margin_bound {n : Nat} (board : Board n) (lower : Nat)
    (area : lower ≤ areaScore board .positive) :
    2 * (lower : Int) - ((n * n : Nat) : Int) ≤ areaMargin board := by
  have total := areaScore_total_le board
  unfold areaMargin
  omega

/-- The original empty-component worklist stops at a point surrounded by stones. -/
theorem emptyRegion_singleton {n : Nat} {board : Board n} {eye : Point n}
    {colour : Polarity} (empty : board eye = none)
    (boundary : ∀ point ∈ adjacentPoints eye, board point = some colour) :
    emptyRegionAt board eye = {eye} := by
  unfold emptyRegionAt
  rw [empty]
  apply Finset.Subset.antisymm
  · intro point member
    apply Finset.mem_singleton.mpr
    apply componentAt_minimal (predicate := fun point => point = eye) rfl _ point member
    intro current _ currentEq candidate adjacent candidateValue
    subst current
    have occupied := boundary candidate (by simpa only [adjacentPoints, List.mem_toFinset] using adjacent)
    rw [empty, occupied] at candidateValue
    cases candidateValue
  · intro point member
    have same := Finset.mem_singleton.mp member
    subst point
    exact point_mem_componentAt board eye

theorem borderingColours_singleton {n : Nat} {board : Board n} {eye : Point n}
    {colour : Polarity}
    (boundary : ∀ point ∈ adjacentPoints eye, board point = some colour)
    (neighbour : (adjacentPoints eye).Nonempty) :
    borderingColours board {eye} = {colour} := by
  ext other
  simp only [borderingColours, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨emptyPoint, rfl, stone, adjacent, occupied⟩
    have same := boundary stone (mem_adjacentPoints_iff_orthogonallyAdjacent.mpr adjacent)
    exact Option.some.inj (occupied.symm.trans same)
  · rintro rfl
    obtain ⟨stone, adjacent⟩ := neighbour
    exact ⟨eye, rfl, stone,
      mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent, boundary stone adjacent⟩

theorem singleton_eye_owner {n : Nat} {board : Board n} {eye : Point n}
    {colour : Polarity} (empty : board eye = none)
    (boundary : ∀ point ∈ adjacentPoints eye, board point = some colour)
    (neighbour : (adjacentPoints eye).Nonempty) :
    territoryOwner? board eye = some colour := by
  unfold territoryOwner?
  rw [if_pos empty, emptyRegion_singleton empty boundary,
    borderingColours_singleton boundary neighbour]
  cases colour <;> simp

theorem core_occupied {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) {point : Point n} (member : point ∈ g.core) :
    board point = some colour :=
  groupAt_member_colour holds.1 (holds.2.1 member)

theorem eye₁_owner {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) : territoryOwner? board g.eye₁ = some colour :=
  singleton_eye_owner holds.2.2.1
    (fun _point adjacent => core_occupied holds (g.boundary₁ adjacent)) g.neighbour₁

theorem eye₂_owner {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) : territoryOwner? board g.eye₂ = some colour :=
  singleton_eye_owner holds.2.2.2
    (fun _point adjacent => core_occupied holds (g.boundary₂ adjacent)) g.neighbour₂

theorem eye₁_not_core {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) : g.eye₁ ∉ g.core := by
  intro member
  have occupied := core_occupied holds member
  rw [holds.2.2.1] at occupied
  cases occupied

theorem eye₂_not_core {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) : g.eye₂ ∉ g.core := by
  intro member
  have occupied := core_occupied holds member
  rw [holds.2.2.2] at occupied
  cases occupied

theorem core_two_eyes_card {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) :
    (g.core ∪ {g.eye₁, g.eye₂}).card = g.core.card + 2 := by
  have separated : Disjoint g.core {g.eye₁, g.eye₂} := by
    apply Finset.disjoint_left.mpr
    intro point coreMember eyeMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at eyeMember
    rcases eyeMember with rfl | rfl
    · exact eye₁_not_core holds coreMember
    · exact eye₂_not_core holds coreMember
  rw [Finset.card_union_of_disjoint separated]
  simp [g.distinct]

theorem core_two_eyes_area {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) :
    g.core.card + 2 ≤ areaScore board colour := by
  rw [← core_two_eyes_card holds]
  apply Finset.card_le_card
  intro point member
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases Finset.mem_union.mp member with coreMember | eyeMember
  · exact Or.inl (core_occupied holds coreMember)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at eyeMember
    rcases eyeMember with rfl | rfl
    · exact Or.inr (eye₁_owner holds)
    · exact Or.inr (eye₂_owner holds)

theorem twoEye_white_margin {n : Nat} {g : Geometry n} {board : Board n}
    (holds : Holds g .negative board) :
    areaMargin board ≤ ((n * n : Nat) : Int) - 2 * ((g.core.card + 2 : Nat) : Int) :=
  white_margin_bound board (g.core.card + 2) (core_two_eyes_area holds)

theorem twoEye_black_margin {n : Nat} {g : Geometry n} {board : Board n}
    (holds : Holds g .positive board) :
    2 * ((g.core.card + 2 : Nat) : Int) - ((n * n : Nat) : Int) ≤ areaMargin board :=
  black_margin_bound board (g.core.card + 2) (core_two_eyes_area holds)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye.Score
