import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorSource

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorContinuation

open Corridor

theorem point_row (row column : Nat) (bound : row < 19) : (point row column).1.val = row := by
  change row % 19 = row
  exact Nat.mod_eq_of_lt bound

theorem point_column (row column : Nat) (bound : column < 19) : (point row column).2.val = column := by
  change column % 19 = column
  exact Nat.mod_eq_of_lt bound

theorem point_coordinates (p : Point 19) : point p.1.val p.2.val = p := by
  apply Prod.ext <;> apply Fin.ext
  · exact point_row _ _ p.1.isLt
  · exact point_column _ _ p.2.isLt

theorem point_at_row {p : Point 19} {row : Nat} (same : p.1.val = row) :
    point row p.2.val = p := by
  rw [← same]
  exact point_coordinates p

@[simp] theorem mem_rowRange {p : Point 19} {row first past : Nat} :
    p ∈ rowRange row first past ↔ p.1.val = row ∧ first ≤ p.2.val ∧ p.2.val < past := by
  simp [rowRange]

theorem horizontal (row column : Nat) (bound : column + 1 < 19) :
    point row (column + 1) ∈ adjacentPoints (point row column) := by
  apply mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
  refine Or.inl ⟨rfl, ?_⟩
  rw [point_column _ _ (by omega), point_column _ _ bound, nat_dist_eq_one_iff]
  exact Or.inl rfl

theorem vertical (column : Nat) : point 0 column ∈ adjacentPoints (point 1 column) := by
  apply mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
  exact Or.inr ⟨rfl, by change Nat.dist 1 0 = 1; decide⟩

theorem floor_mem {j column : Nat} (edge : j < 19) (bound : column ≤ j) :
    point 1 column ∈ floor j := by
  apply mem_rowRange.mpr
  refine ⟨point_row _ _ (by decide), Nat.zero_le _, ?_⟩
  rw [point_column _ _ (by omega)]
  omega

theorem same_colour_step {board : Board 19} {seed current next : Point 19}
    (occupied : board seed = some .positive) (member : current ∈ groupAt board seed)
    (adjacent : next ∈ adjacentPoints current) (nextOccupied : board next = some .positive) :
    next ∈ groupAt board seed := by
  have component : current ∈ componentAt board seed := by simpa only [groupAt, occupied] using member
  have nextMember := componentAt_closed component
    (by simpa only [adjacentPoints, List.mem_toFinset] using adjacent) (nextOccupied.trans occupied.symm)
  simpa only [groupAt, occupied] using nextMember

theorem floor_connected {board : Board 19} {j : Nat} (edge : j < 19)
    (occupied : ∀ p ∈ floor j, board p = some .positive) :
    ∀ column ≤ j, point 1 column ∈ groupAt board (point 1 0) := by
  have seed := occupied _ (floor_mem edge (Nat.zero_le j))
  intro column
  induction column with
  | zero => intro _; exact occupied_point_mem_groupAt seed
  | succ column ih =>
      intro bound
      exact same_colour_step seed (ih (by omega)) (horizontal 1 column (by omega))
        (occupied _ (floor_mem edge bound))

theorem wall_connected {board : Board 19} {j divider : Nat} (edge : j < 19)
    (dividerBound : divider ≤ j)
    (occupied : ∀ p ∈ insert (point 0 divider) (floor j), board p = some .positive) :
    ∀ p ∈ insert (point 0 divider) (floor j), p ∈ groupAt board (point 1 0) := by
  have floorOccupied : ∀ p ∈ floor j, board p = some .positive :=
    fun p member => occupied p (Finset.mem_insert_of_mem member)
  have floorGroup := floor_connected edge floorOccupied
  have seed := floorOccupied _ (floor_mem edge (Nat.zero_le j))
  intro p member
  rcases Finset.mem_insert.mp member with same | inFloor
  · subst p
    exact same_colour_step seed (floorGroup divider dividerBound) (vertical divider)
      (occupied _ (Finset.mem_insert_self _ _))
  · obtain ⟨row, _, column⟩ := mem_rowRange.mp inFloor
    rw [← point_at_row row]
    exact floorGroup _ (by omega)

theorem wall_reserve {board : Board 19} {j divider : Nat} (edge : j < 19)
    (dividerBound : divider < j)
    (occupied : ∀ p ∈ insert (point 0 divider) (floor j), board p = some .positive)
    (left : ∃ p ∈ leftRoom divider, board p = none) (sealEmpty : board (point 0 j) = none) :
    ∀ p ∈ insert (point 0 divider) (floor j), 2 ≤ (LibertyReserve.liberties board p).card := by
  obtain ⟨vacant, inLeft, vacantEmpty⟩ := left
  obtain ⟨row, _, column⟩ := mem_rowRange.mp inLeft
  have vacantEq := point_at_row row
  have distinct : vacant ≠ point 0 j := by
    intro same
    have sameColumn := congrArg (fun p : Point 19 => p.2.val) same
    rw [point_column _ _ edge] at sameColumn
    omega
  have floorOccupied : ∀ p ∈ floor j, board p = some .positive :=
    fun p member => occupied p (Finset.mem_insert_of_mem member)
  have seed := floorOccupied _ (floor_mem edge (Nat.zero_le j))
  have floorGroup := floor_connected edge floorOccupied
  intro p member
  have reseeded := groupAt_eq_of_mem seed (wall_connected edge (by omega) occupied p member)
  have leftLiberty : vacant ∈ LibertyReserve.liberties board p := by
    apply LibertyReserve.mem_liberties.mpr
    refine ⟨⟨point 1 vacant.2.val, ?_, ?_⟩, vacantEmpty⟩
    · rw [reseeded]; exact floorGroup _ (by omega)
    · simpa only [vacantEq] using vertical vacant.2.val
  have sealLiberty : point 0 j ∈ LibertyReserve.liberties board p := by
    apply LibertyReserve.mem_liberties.mpr
    refine ⟨⟨point 1 j, ?_, vertical j⟩, sealEmpty⟩
    rw [reseeded]; exact floorGroup j (Nat.le_refl j)
  have included : ({vacant, point 0 j} : Finset (Point 19)) ⊆ LibertyReserve.liberties board p := by
    intro q inside
    rcases Finset.mem_insert.mp inside with same | inside
    · simpa only [same] using leftLiberty
    · simpa only [Finset.mem_singleton.mp inside] using sealLiberty
  simpa only [Finset.card_pair distinct] using Finset.card_le_card included

end SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorContinuation
