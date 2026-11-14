import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorContinuationGeometry
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthCapturing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorPreparation

open Corridor CorridorContinuation

theorem seal_mem_frontier {j : Nat} (edge : j < 19) : point 0 j ∈ Corridor.frontier j := by
  apply Finset.mem_union_left
  apply mem_rowRange.mpr
  exact ⟨point_row _ _ (by decide), by rw [point_column _ _ edge],
    by simpa only [point_column _ _ edge] using edge⟩

theorem geometry_fields {n : Nat} {core : Finset (Point n)} {rooms : Finset (Finset (Point n))}
    {geometry : VitalChambers.Geometry n} (generated : VitalChambers.geometry? core rooms = some geometry) :
    geometry.core = core ∧ geometry.rooms = rooms := by
  unfold VitalChambers.geometry? at generated
  split at generated
  · split at generated
    · split at generated
      · split at generated
        · cases generated; exact ⟨rfl, rfl⟩
        · cases generated
      · cases generated
    · cases generated
  · cases generated

theorem sealed_fields {j divider : Nat} {geometry : VitalChambers.Geometry 19}
    (beforeEdge : j < 18) (generated : sealedGeometry? j divider = some geometry) :
    geometry.core = insert (point 0 j) (insert (point 0 divider) (floor j)) ∧
      geometry.rooms = {leftRoom divider, rightRoom j divider} := by
  unfold sealedGeometry? at generated
  rw [if_neg (show j ≠ 18 by omega)] at generated
  exact geometry_fields generated

theorem internal_ne_seal {p : Point 19} {j divider : Nat} (edge : j < 19) (gap : divider < j)
    (member : p ∈ leftRoom divider ∪ rightRoom j divider) : p ≠ point 0 j := by
  rcases Finset.mem_union.mp member with left | right
  · intro same
    have bound := (mem_rowRange.mp left).2.2
    rw [same, point_column _ _ edge] at bound
    omega
  · intro same
    have bound := (mem_rowRange.mp right).2.2
    rw [same, point_column _ _ edge] at bound
    omega

theorem last_right {j divider : Nat} (edge : j < 19) (gap : divider + 1 < j) :
    point 0 (j - 1) ∈ rightRoom j divider ∧ point 0 (j - 1) ∈ adjacentPoints (point 0 j) := by
  have previous : j - 1 < 19 := by omega
  constructor
  · apply mem_rowRange.mpr
    refine ⟨point_row _ _ (by decide), ?_, ?_⟩ <;> rw [point_column _ _ previous] <;> omega
  · apply mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
    refine Or.inl ⟨rfl, ?_⟩
    rw [point_column _ _ edge, point_column _ _ previous, nat_dist_eq_one_iff]
    exact Or.inr (by omega)

def plan {frame : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18) (geometry : VitalChambers.Geometry 19)
    (generated : sealedGeometry? j divider = some geometry) :
    VitalBirthCapturing.Plan frame.visible.board .positive where
  point := point 0 j
  empty := by
    rcases source with ⟨_, upper, _, _, _, _, _, _, _, _, _, future, _⟩
    exact future _ (seal_mem_frontier (by omega))
  geometry := geometry
  participates := by rw [(sealed_fields beforeEdge generated).1]; exact Finset.mem_insert_self _ _
  core := by
    rcases source with ⟨_, _, _, _, _, _, _, _, wall, _⟩
    intro p member
    rw [(sealed_fields beforeEdge generated).1] at member
    rcases Finset.mem_insert.mp member with same | old
    · subst p; exact Board.set_self _ _ _
    · by_cases same : p = point 0 j
      · subst p; exact Board.set_self _ _ _
      · rw [Board.set_other _ _ same]
        exact wall p old
  notOwn := by
    rcases source with ⟨_, upper, _, _, gap, _, _, _, _, internal, _⟩
    intro room member p inside
    rw [(sealed_fields beforeEdge generated).2] at member
    have old : p ∈ leftRoom divider ∪ rightRoom j divider := by
      rcases Finset.mem_insert.mp member with same | last
      · subst room; exact Finset.mem_union_left _ inside
      · have same := Finset.mem_singleton.mp last
        subst room; exact Finset.mem_union_right _ inside
    rw [Board.set_other _ _ (internal_ne_seal (by omega) (by omega) old)]
    exact internal p old
  rooms := by
    rcases source with ⟨_, upper, _, _, gap, _, _, _, _, internal, left, _⟩
    intro room member
    rw [(sealed_fields beforeEdge generated).2] at member
    rcases Finset.mem_insert.mp member with same | last
    · subst room; exact Or.inl left
    · have same := Finset.mem_singleton.mp last
      subst room
      by_cases vacant : ∃ p ∈ rightRoom j divider, frame.visible.board p = none
      · exact Or.inl vacant
      · refine Or.inr ⟨?_, ?_⟩
        · intro p inside
          have notOwn := internal p (Finset.mem_union_right _ inside)
          have notEmpty : frame.visible.board p ≠ none := fun empty => vacant ⟨p, inside, empty⟩
          cases value : frame.visible.board p with
          | none => exact False.elim (notEmpty value)
          | some colour => cases colour <;> simp_all
        · exact ⟨point 0 (j - 1), (last_right (by omega) gap).1, (last_right (by omega) gap).2⟩

theorem saved {frame : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18) (geometry : VitalChambers.Geometry 19)
    (generated : sealedGeometry? j divider = some geometry) :
    VitalBirthCapturing.SavedCore (plan source beforeEdge geometry generated) := by
  rcases source with ⟨_, upper, _, _, gap, _, _, _, wall, _, left, future, _⟩
  have reserve := wall_reserve (board := frame.visible.board) (j := j) (divider := divider)
    (by omega) (by omega) wall left (future _ (seal_mem_frontier (by omega)))
  intro p member different
  change p ∈ geometry.core at member
  change p ≠ point 0 j at different
  rw [(sealed_fields beforeEdge generated).1] at member
  rcases Finset.mem_insert.mp member with same | old
  · exact False.elim (different same)
  · exact reserve p old

theorem floor_five_card : (floor 5).card = 6 := by decide

theorem floor_five_subset {j : Nat} (lower : 5 ≤ j) : floor 5 ⊆ floor j := by
  intro p member
  obtain ⟨row, start, past⟩ := mem_rowRange.mp member
  exact mem_rowRange.mpr ⟨row, start, by omega⟩

theorem top_not_floor (column j : Nat) : point 0 column ∉ floor j := by
  intro member
  have row := (mem_rowRange.mp member).1
  rw [point_row _ _ (by decide)] at row
  omega

theorem distinct_seal_divider {j divider : Nat} (edge : j < 19) (gap : divider < j) :
    point 0 j ≠ point 0 divider := by
  intro same
  have columns := congrArg (fun p : Point 19 => p.2.val) same
  rw [point_column _ _ edge, point_column _ _ (by omega)] at columns
  omega

theorem area_lower {frame : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18) (geometry : VitalChambers.Geometry 19)
    (generated : sealedGeometry? j divider = some geometry) :
    8 ≤ (VitalChambers.points geometry).card := by
  obtain ⟨core, rooms⟩ := sealed_fields beforeEdge generated
  rcases source with ⟨lower, upper, dividerLower, dividerUpper, gap, _⟩
  by_cases small : j = 4
  · subst j
    have choices : divider = 1 ∨ divider = 2 := by omega
    rcases choices with rfl | rfl
    · simp only [VitalChambers.points, VitalChambers.eyes, core, rooms]
      decide
    · simp only [VitalChambers.points, VitalChambers.eyes, core, rooms]
      decide
  · have firstFresh : point 0 divider ∉ floor 5 := top_not_floor _ _
    have lastFresh : point 0 j ∉ insert (point 0 divider) (floor 5) := by
      intro member
      rcases Finset.mem_insert.mp member with same | bottom
      · exact distinct_seal_divider (by omega) (by omega) same
      · exact top_not_floor _ _ bottom
    have count : (insert (point 0 j) (insert (point 0 divider) (floor 5))).card = 8 := by
      rw [Finset.card_insert_of_notMem lastFresh, Finset.card_insert_of_notMem firstFresh, floor_five_card]
    have included : insert (point 0 j) (insert (point 0 divider) (floor 5)) ⊆ VitalChambers.points geometry := by
      apply Finset.Subset.trans _ Finset.subset_union_left
      rw [core]
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (floor_five_subset (by omega)))
    simpa only [count] using Finset.card_le_card included

theorem accepted {frame : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18) (geometry : VitalChambers.Geometry 19)
    (generated : sealedGeometry? j divider = some geometry) :
    acceptsMargin .positive (-345) (VitalChambers.bound geometry .positive) = true := by
  have area := area_lower source beforeEdge geometry generated
  apply decide_eq_true
  change (-345 : Int) ≤ 2 * ((VitalChambers.points geometry).card : Int) - 361
  omega

structure Prepared (frame : Frame 19) (j : Nat) where
  candidate : VitalBirthCapturing.Candidate frame .positive (-345) (CoalitionBirth.retained frame .positive)
  point_eq : candidate.plan.point = point 0 j
  saved : VitalBirthCapturing.SavedCore candidate.plan

/-- Current source facts prepare the common response before any opponent event.
Only the given original-coordinate geometry producer is consumed here. -/
def prepare {frame : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18) (geometry : VitalChambers.Geometry 19)
    (generated : sealedGeometry? j divider = some geometry) : Prepared frame j :=
  let currentPlan := plan source beforeEdge geometry generated
  have virgin : currentPlan.point ∉ CoalitionBirth.retained frame .positive := by
    rcases source with ⟨_, upper, _, _, _, _, _, _, _, _, _, _, fresh⟩
    intro member
    exact (Finset.disjoint_left.mp fresh) (seal_mem_frontier (by omega)) member
  let candidate : VitalBirthCapturing.Candidate frame .positive (-345) (CoalitionBirth.retained frame .positive) :=
    ⟨currentPlan, virgin, accepted source beforeEdge geometry generated⟩
  ⟨candidate, rfl, saved source beforeEdge geometry generated⟩

theorem base {frame : Frame 19} {divider : Nat} (source : Source frame 18 divider)
    (geometry : VitalChambers.Geometry 19) (generated : sealedGeometry? 18 divider = some geometry) :
    VitalChambers.Holds geometry .positive frame.visible.board ∧
      acceptsMargin .positive (-345) (VitalChambers.bound geometry .positive) = true := by
  unfold sealedGeometry? at generated
  rw [if_pos rfl] at generated
  obtain ⟨core, rooms⟩ := geometry_fields generated
  rcases source with ⟨_, _, _, dividerUpper, _, _, _, _, wall, internal, left, future, _⟩
  have lastEmpty : frame.visible.board (point 0 18) = none := future _ (seal_mem_frontier (by decide))
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro p member
      rw [core] at member
      exact wall p member
    · intro room member p inside
      rw [rooms] at member
      rcases Finset.mem_insert.mp member with same | last
      · subst room; exact internal p (Finset.mem_union_left _ inside)
      · have same := Finset.mem_singleton.mp last
        subst room
        obtain ⟨row, lower, upper⟩ := mem_rowRange.mp inside
        by_cases old : p.2.val < 18
        · exact internal p (Finset.mem_union_right _ (mem_rowRange.mpr ⟨row, lower, old⟩))
        · have column : p.2.val = 18 := by omega
          have pointEq : p = point 0 18 := by rw [← point_at_row row, column]
          rw [pointEq, lastEmpty]
          simp
    · intro room member
      rw [rooms] at member
      rcases Finset.mem_insert.mp member with same | last
      · subst room; exact left
      · have same := Finset.mem_singleton.mp last
        subst room
        refine ⟨point 0 18, mem_rowRange.mpr ?_, lastEmpty⟩
        exact ⟨point_row _ _ (by decide), by change divider + 1 ≤ 18; omega, by decide⟩
  · have eight : (floor 7).card = 8 := by decide
    have included : floor 7 ⊆ VitalChambers.points geometry := by
      intro p member
      apply Finset.mem_union_left
      rw [core]
      apply Finset.mem_insert_of_mem
      obtain ⟨row, lower, upper⟩ := mem_rowRange.mp member
      exact mem_rowRange.mpr ⟨row, lower, by omega⟩
    have area : 8 ≤ (VitalChambers.points geometry).card := by
      simpa only [eight] using Finset.card_le_card included
    apply decide_eq_true
    change (-345 : Int) ≤ 2 * ((VitalChambers.points geometry).card : Int) - 361
    omega

end SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorPreparation
