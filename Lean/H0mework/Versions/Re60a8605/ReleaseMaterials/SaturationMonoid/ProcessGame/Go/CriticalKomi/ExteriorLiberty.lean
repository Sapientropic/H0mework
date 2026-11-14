import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionProjection

/-!
Exterior space supplies a present liberty through its generated connected
component and the actual opposing-stone count. No boundary life or future
preservation witness is an input.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.ExteriorLiberty

open RegionProjection RegionAction

/-- The existing component program reads only the exterior geometry. -/
def maskBoard {n : Nat} (region : Finset (Point n)) : Board n :=
  fun point => if point ∈ region then none else some .positive

def component {n : Nat} (region : Finset (Point n)) (seed : Point n) :
    Finset (Point n) := groupAt (maskBoard region) seed

theorem mask_outside {n : Nat} (region : Finset (Point n)) (point : Point n) :
    maskBoard region point = some .positive ↔ point ∉ region := by
  by_cases inside : point ∈ region <;> simp [maskBoard, inside]

/-- A liberty-free group would fill every exterior component that it meets. -/
theorem component_subset_of_no_liberty {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity} {seed stone exterior : Point n}
    (confined : Confined region board colour)
    (occupied : board seed = some colour.other)
    (member : stone ∈ groupAt board seed)
    (adjacent : exterior ∈ adjacentPoints stone) (outside : exterior ∉ region)
    (noLiberty : ¬ stoneHasLiberty board seed) :
    component region exterior ⊆ groupAt board seed := by
  have extend {current candidate : Point n}
      (currentMember : current ∈ groupAt board seed)
      (candidateAdjacent : candidate ∈ adjacentPoints current)
      (candidateOutside : candidate ∉ region) : candidate ∈ groupAt board seed := by
    have notOwn : board candidate ≠ some colour := by
      intro own
      exact candidateOutside (confined candidate own)
    have candidateOccupied : board candidate = some colour.other := by
      cases value : board candidate with
      | none =>
          exact False.elim (noLiberty ⟨current, currentMember,
            candidate, candidateAdjacent, value⟩)
      | some other =>
          have different : other ≠ colour := by
            intro same
            exact notOwn (value.trans (congrArg some same))
          have same : other = colour.other := by
            cases colour <;> cases other <;> simp_all [Polarity.other]
          exact congrArg some same
    simp only [groupAt, occupied] at currentMember ⊢
    exact componentAt_closed currentMember
      (by simpa only [adjacentPoints, List.mem_toFinset] using candidateAdjacent)
      (candidateOccupied.trans occupied.symm)
  have initialMember := extend member adjacent outside
  have maskSeed := (mask_outside region exterior).mpr outside
  simp only [component, groupAt, maskSeed]
  apply componentAt_minimal (predicate := fun point => point ∈ groupAt board seed)
    initialMember
  intro current _ currentMember candidate candidateAdjacent candidateValue
  apply extend currentMember
    (by simpa only [adjacentPoints, List.mem_toFinset] using candidateAdjacent)
  exact (mask_outside region candidate).mp (candidateValue.trans maskSeed)

/-- An exterior component larger than the complete opposing occupancy must
contain a real liberty of the source group. -/
theorem liberty_of_capacity {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity} {seed stone exterior : Point n}
    (confined : Confined region board colour)
    (occupied : board seed = some colour.other)
    (member : stone ∈ groupAt board seed)
    (adjacent : exterior ∈ adjacentPoints stone) (outside : exterior ∉ region)
    (capacity : (stones board colour.other).card < (component region exterior).card) :
    stoneHasLiberty board seed := by
  by_contra noLiberty
  have contained := component_subset_of_no_liberty region confined occupied member
    adjacent outside noLiberty
  have occupiedSubset : component region exterior ⊆ stones board colour.other := by
    intro point pointMember
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ point,
      groupAt_member_colour occupied (contained pointMember)⟩
  exact Nat.not_lt_of_ge (Finset.card_le_card occupiedSubset) capacity

theorem confined_set {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity} {played : Point n}
    (confined : Confined region board colour) (inside : played ∈ region) :
    Confined region (Board.set board played (some colour)) colour := by
  intro point occupied
  by_cases same : point = played
  · exact same ▸ inside
  · rw [Board.set_other _ _ same] at occupied
    exact confined point occupied

theorem opposing_stones_set {n : Nat} {board : Board n} {colour : Polarity}
    {played : Point n} (empty : board played = none) :
    stones (Board.set board played (some colour)) colour.other = stones board colour.other := by
  ext point
  simp only [stones, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases same : point = played
  · subst point
    rw [Board.set_self, empty]
    cases colour <;> simp
  · rw [Board.set_other _ _ same]

/-- The source capacity survives an interior placement: opposing groups and
their total occupancy are unchanged in the compiler's pre-capture board. -/
theorem placed_liberty_of_capacity {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity} {played seed stone exterior : Point n}
    (confined : Confined region board colour) (inside : played ∈ region)
    (empty : board played = none) (occupied : board seed = some colour.other)
    (member : stone ∈ groupAt board seed)
    (adjacent : exterior ∈ adjacentPoints stone) (outside : exterior ∉ region)
    (capacity : (stones board colour.other).card < (component region exterior).card) :
    stoneHasLiberty (Board.set board played (some colour)) seed := by
  have different : seed ≠ played := by
    intro same
    subst seed
    rw [empty] at occupied
    cases occupied
  have placedOccupied : Board.set board played (some colour) seed = some colour.other := by
    rw [Board.set_other _ _ different]
    exact occupied
  refine liberty_of_capacity region (confined_set region confined inside) placedOccupied
    ?_ adjacent outside ?_
  · rw [groupAt_placed_opponent_eq empty occupied]
    exact member
  · rw [opposing_stones_set empty]
    exact capacity

private theorem not_captured_of_placed_liberty {n : Nat} {board : Board n}
    {colour : Polarity} {played point : Point n}
    (liberty : stoneHasLiberty (Board.set board played (some colour)) point) :
    point ∉ capturedStonesAfterPlay board colour played := by
  intro captured
  unfold capturedStonesAfterPlay at captured
  obtain ⟨neighbour, _, member⟩ := Finset.mem_biUnion.mp captured
  split at member
  · rename_i taken
    have same := groupAt_eq_of_mem taken.1 member
    apply taken.2
    unfold stoneHasLiberty at liberty ⊢
    rw [← same]
    exact liberty
  · simp at member

/-- A generated exterior capacity guards every stone in the original group
against the original capture compiler, after the actual interior placement. -/
theorem group_not_captured {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity} {played seed stone exterior point : Point n}
    (confined : Confined region board colour) (inside : played ∈ region)
    (empty : board played = none) (occupied : board seed = some colour.other)
    (member : stone ∈ groupAt board seed)
    (adjacent : exterior ∈ adjacentPoints stone) (outside : exterior ∉ region)
    (capacity : (stones board colour.other).card < (component region exterior).card)
    (pointMember : point ∈ groupAt board seed) :
    point ∉ capturedStonesAfterPlay board colour played := by
  have liberty := placed_liberty_of_capacity region confined inside empty occupied
    member adjacent outside capacity
  apply not_captured_of_placed_liberty
  have pointOccupied := groupAt_member_colour occupied pointMember
  unfold stoneHasLiberty at liberty ⊢
  rw [groupAt_placed_opponent_eq empty pointOccupied,
    groupAt_eq_of_mem occupied pointMember]
  rw [groupAt_placed_opponent_eq empty occupied] at liberty
  exact liberty

def occupiedPoints {n : Nat} (board : Board n) : Finset (Point n) :=
  Finset.univ.filter (fun point => board point ≠ none)

def placementCount {n : Nat} : List (Move n) → Nat
  | [] => 0
  | .play _ :: remaining => placementCount remaining + 1
  | .pass :: remaining => placementCount remaining
  | .resign :: remaining => placementCount remaining

theorem placementCount_le_length {n : Nat} (moves : List (Move n)) :
    placementCount moves ≤ moves.length := by
  induction moves with
  | nil => rfl
  | cons move remaining ih =>
      cases move <;> simp only [placementCount, List.length_cons] <;> omega

theorem occupied_afterPlay_le {n : Nat} (board : Board n) (colour : Polarity)
    (played : Point n) :
    (occupiedPoints (boardAfterPlay board colour played)).card ≤
      (occupiedPoints board).card + 1 := by
  have included : occupiedPoints (boardAfterPlay board colour played) ⊆
      insert played (occupiedPoints board) := by
    intro point occupied
    by_cases same : point = played
    · exact Finset.mem_insert.mpr (Or.inl same)
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ point, ?_⟩
      have nonempty := (Finset.mem_filter.mp occupied).2
      unfold boardAfterPlay at nonempty
      split at nonempty
      · exact False.elim (nonempty rfl)
      · simpa only [Board.set_other _ _ same] using nonempty
  exact (Finset.card_le_card included).trans (Finset.card_insert_le _ _)

private theorem play_step_board {n : Nat} {law : Law} {frame target : Frame n}
    {played : Point n} (step : LegalStep law frame (.play played) target) :
    target.visible.board = boardAfterPlay frame.visible.board frame.visible.toMove played := by
  have generated := nativeStep_visible_eq step
  cases status : frame.visible.status with
  | terminal reason => simp [stepVisible?, playVisible?, status] at generated
  | playing =>
      simp only [stepVisible?, playVisible?, status] at generated
      split at generated
      · split at generated
        · split at generated
          · simp at generated
          · exact (congrArg VisiblePosition.board (Option.some.inj generated)).symm
        · simp at generated
      · simp at generated

private theorem nonplay_step_board {n : Nat} {law : Law} {frame target : Frame n}
    {move : Move n} (step : LegalStep law frame move target)
    (nonplay : ∀ point, move ≠ .play point) : target.visible.board = frame.visible.board := by
  have generated := nativeStep_visible_eq step
  cases move with
  | play point => exact False.elim (nonplay point rfl)
  | pass =>
      cases status : frame.visible.status with
      | terminal reason => simp [stepVisible?, passVisible?, status] at generated
      | playing =>
          simp only [stepVisible?, passVisible?, status] at generated
          split at generated
          · simp at generated
          · exact (congrArg VisiblePosition.board (Option.some.inj generated)).symm
  | resign =>
      cases status : frame.visible.status with
      | terminal reason => simp [stepVisible?, resignVisible?, status] at generated
      | playing =>
          simp only [stepVisible?, resignVisible?, status] at generated
          exact (congrArg VisiblePosition.board (Option.some.inj generated)).symm

/-- The same actual replay can add at most one occupied point per placement;
capture only reduces this count and pass/resign add none. -/
theorem replay_occupied_le {n : Nat} {law : Law} {start : Frame n} {moves : List (Move n)}
    (replay : GeneratedReplay law start moves) :
    (occupiedPoints replay.final.visible.board).card ≤
      (occupiedPoints start.visible.board).card + placementCount moves := by
  induction replay with
  | nil => simp [GeneratedReplay.final, placementCount]
  | @cons start next moves move step tail ih =>
      change (occupiedPoints tail.final.visible.board).card ≤ _
      cases move with
      | play point =>
          have bound := occupied_afterPlay_le start.visible.board start.visible.toMove point
          rw [← play_step_board step] at bound
          simp only [placementCount]
          omega
      | pass =>
          have same := nonplay_step_board step (by intro point; simp)
          rw [same] at ih
          exact ih
      | resign =>
          have same := nonplay_step_board step (by intro point; simp)
          rw [same] at ih
          exact ih

theorem initial_occupied_le {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) :
    (occupiedPoints replay.final.visible.board).card ≤ placementCount moves := by
  have bound := replay_occupied_le replay
  simpa only [Frame.initial, occupiedPoints, Board.empty, ne_eq, not_true_eq_false,
    Finset.filter_false, Finset.card_empty, Nat.zero_add] using bound

theorem stones_le_occupied {n : Nat} (board : Board n) (colour : Polarity) :
    (stones board colour).card ≤ (occupiedPoints board).card := by
  apply Finset.card_le_card
  intro point member
  have value := (Finset.mem_filter.mp member).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ point, by rw [value]; simp⟩

theorem initial_stones_le_placements {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) (colour : Polarity) :
    (stones replay.final.visible.board colour).card ≤ placementCount moves :=
  (stones_le_occupied replay.final.visible.board colour).trans (initial_occupied_le replay)

/-- The exterior capture guard is paid by the exact source replay's event
count, without accepting any living-boundary certificate. -/
theorem initial_group_not_captured {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) (region : Finset (Point n))
    {colour : Polarity} {played seed stone exterior point : Point n}
    (confined : Confined region replay.final.visible.board colour) (inside : played ∈ region)
    (empty : replay.final.visible.board played = none)
    (occupied : replay.final.visible.board seed = some colour.other)
    (member : stone ∈ groupAt replay.final.visible.board seed)
    (adjacent : exterior ∈ adjacentPoints stone) (outside : exterior ∉ region)
    (capacity : placementCount moves < (component region exterior).card)
    (pointMember : point ∈ groupAt replay.final.visible.board seed) :
    point ∉ capturedStonesAfterPlay replay.final.visible.board colour played :=
  group_not_captured region confined inside empty occupied member adjacent outside
    (lt_of_le_of_lt (initial_stones_le_placements replay colour.other) capacity) pointMember

end SaturationMonoid.ProcessGame.Go.CriticalKomi.ExteriorLiberty
