import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorContinuationGeometry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorContinuation

open Corridor

theorem top_mem_frontier {j column : Nat} (lower : j ≤ column) (upper : column < 19) :
    point 0 column ∈ Corridor.frontier j := by
  apply Finset.mem_union_left
  apply mem_rowRange.mpr
  exact ⟨point_row _ _ (by decide), by simpa only [point_column _ _ upper] using lower,
    by simpa only [point_column _ _ upper] using upper⟩

theorem next_floor_mem_frontier {j : Nat} (edge : j + 1 < 19) :
    point 1 (j + 1) ∈ Corridor.frontier j := by
  apply Finset.mem_union_right
  apply mem_rowRange.mpr
  exact ⟨point_row _ _ (by decide), by rw [point_column _ _ edge],
    by simpa only [point_column _ _ edge] using edge⟩

theorem frontier_next_subset (j : Nat) : Corridor.frontier (j + 1) ⊆ Corridor.frontier j := by
  intro p member
  rcases Finset.mem_union.mp member with top | bottom
  · obtain ⟨row, lower, upper⟩ := mem_rowRange.mp top
    exact Finset.mem_union_left _ (mem_rowRange.mpr ⟨row, by omega, upper⟩)
  · obtain ⟨row, lower, upper⟩ := mem_rowRange.mp bottom
    exact Finset.mem_union_right _ (mem_rowRange.mpr ⟨row, by omega, upper⟩)

theorem next_frontier_not_seal {j : Nat} (edge : j < 19) : point 0 j ∉ Corridor.frontier (j + 1) := by
  intro member
  rcases Finset.mem_union.mp member with top | bottom
  · have fields := mem_rowRange.mp top
    rw [point_column _ _ edge] at fields
    omega
  · have fields := (mem_rowRange.mp bottom).1
    rw [point_row _ _ (by decide)] at fields
    omega

theorem next_frontier_not_floor {j : Nat} (edge : j + 1 < 19) :
    point 1 (j + 1) ∉ Corridor.frontier (j + 1) := by
  intro member
  rcases Finset.mem_union.mp member with top | bottom
  · have fields := (mem_rowRange.mp top).1
    rw [point_row _ _ (by decide)] at fields
    omega
  · have fields := mem_rowRange.mp bottom
    rw [point_column _ _ edge] at fields
    omega

theorem top_ne_floor (topColumn floorColumn : Nat) : point 0 topColumn ≠ point 1 floorColumn := by
  intro same
  have rows := congrArg (fun p : Point 19 => p.1.val) same
  rw [point_row _ _ (by decide), point_row _ _ (by decide)] at rows
  omega

theorem rooms_row {p : Point 19} {j divider : Nat}
    (member : p ∈ leftRoom divider ∪ rightRoom j divider) : p.1.val = 0 := by
  rcases Finset.mem_union.mp member with left | right
  · exact (mem_rowRange.mp left).1
  · exact (mem_rowRange.mp right).1

theorem rooms_next_split {p : Point 19} {j divider : Nat}
    (member : p ∈ leftRoom divider ∪ rightRoom (j + 1) divider) :
    p ∈ leftRoom divider ∪ rightRoom j divider ∨ p = point 0 j := by
  rcases Finset.mem_union.mp member with left | right
  · exact Or.inl (Finset.mem_union_left _ left)
  · obtain ⟨row, lower, upper⟩ := mem_rowRange.mp right
    by_cases old : p.2.val < j
    · exact Or.inl (Finset.mem_union_right _ (mem_rowRange.mpr ⟨row, lower, old⟩))
    · have column : p.2.val = j := by omega
      exact Or.inr (by rw [← point_at_row row, column])

theorem wall_next_split {p : Point 19} {j divider : Nat}
    (member : p ∈ insert (point 0 divider) (floor (j + 1))) :
    p ∈ insert (point 0 divider) (floor j) ∨ p = point 1 (j + 1) := by
  rcases Finset.mem_insert.mp member with same | bottom
  · exact Or.inl (Finset.mem_insert.mpr (Or.inl same))
  · obtain ⟨row, lower, upper⟩ := mem_rowRange.mp bottom
    by_cases old : p.2.val < j + 1
    · exact Or.inl (Finset.mem_insert_of_mem (mem_rowRange.mpr ⟨row, lower, old⟩))
    · have column : p.2.val = j + 1 := by omega
      exact Or.inr (by rw [← point_at_row row, column])

theorem left_ne_seal {p : Point 19} {j divider : Nat} (edge : j < 19) (gap : divider < j)
    (member : p ∈ leftRoom divider) : p ≠ point 0 j := by
  intro same
  have column := (mem_rowRange.mp member).2.2
  rw [same, point_column _ _ edge] at column
  omega

theorem retained_subset_of_tracked {n : Nat} {frame : Frame n} {colour : Polarity}
    {seen : Finset (Point n)} (tracked : VirginHistory.Tracked frame colour seen) :
    CoalitionBirth.retained frame colour ⊆ seen := by
  intro p member
  rcases Finset.mem_union.mp member with current | previous
  · exact tracked.1 current
  · obtain ⟨old, oldMember, occupied⟩ := List.any_eq_true.mp (Finset.mem_filter.mp previous).2
    exact tracked.2 old oldMember p (of_decide_eq_true occupied)

theorem opponent_not_own {n : Nat} {board : Board n} {colour : Polarity} {played p : Point n}
    (notOwn : board p ≠ some colour) : boardAfterPlay board colour.other played p ≠ some colour := by
  intro occupied
  exact notOwn (Finset.mem_filter.mp (VirginHistory.opponent_stones_subset board colour played
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, occupied⟩))).2

theorem own_not_own {n : Nat} {board : Board n} {colour : Polarity} {played p : Point n}
    (notOwn : board p ≠ some colour) (different : p ≠ played) :
    boardAfterPlay board colour played p ≠ some colour := by
  unfold boardAfterPlay
  split
  · simp
  · rw [Board.set_other _ _ different]
    exact notOwn

theorem after_seal_wall {frame target : Frame 19} {j divider : Nat}
    (source : Source frame j divider)
    (step : LegalStep (Law.positionalSuperko 0) frame (.play (point 0 j)) target) :
    ∀ p ∈ insert (point 0 divider) (floor j), target.visible.board p = some .positive := by
  rcases source with ⟨_, edge, _, _, gap, _, opponent, _, wall, _, left, future, _⟩
  have reserve := wall_reserve (board := frame.visible.board) (j := j) (divider := divider)
    (by omega) (by omega) wall left
    (future _ (top_mem_frontier (Nat.le_refl j) (by omega)))
  have facts := CoalitionBirth.play_data step
  intro p member
  rw [facts.2.2.1, opponent]
  exact LibertyReserve.seed_survives_of_two (board := frame.visible.board) (colour := .positive)
    (seed := p) (played := point 0 j) (wall p member) (reserve p member) facts.1

theorem after_seal_tracked {frame target : Frame 19} {j divider : Nat}
    (source : Source frame j divider)
    (step : LegalStep (Law.positionalSuperko 0) frame (.play (point 0 j)) target) :
    VirginHistory.Tracked target .positive (CoalitionBirth.retained frame .positive) := by
  rcases source with ⟨_, _, _, _, _, _, opponent, _⟩
  have retained := VirginHistory.step (CoalitionBirth.retained_tracked frame .positive) (by simp) step
  simpa only [VirginHistory.nextSeen, opponent, reduceCtorEq, ↓reduceIte] using retained

theorem reply_ready {frame target : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18)
    (step : LegalStep (Law.positionalSuperko 0) frame (.play (point 0 j)) target) :
    target.visible.toMove = .positive ∧ target.visible.board (point 1 (j + 1)) = none ∧
      stoneHasLiberty (boardAfterPlay target.visible.board .positive (point 1 (j + 1))) (point 1 (j + 1)) ∧
      point 1 (j + 1) ∉ CoalitionBirth.retained frame .positive := by
  rcases source with ⟨_, _, _, _, _, _, opponent, _, _, _, _, future, fresh⟩
  have facts := CoalitionBirth.play_data step
  have targetBoard : target.visible.board = boardAfterPlay frame.visible.board .negative (point 0 j) := by
    rw [facts.2.2.1, opponent]
  have targetTurn : target.visible.toMove = .positive := by rw [facts.2.2.2, opponent]; rfl
  have empty : target.visible.board (point 1 (j + 1)) = none := by
    rw [targetBoard]
    exact CoalitionBirth.empty_after_other (future _ (next_floor_mem_frontier (by omega)))
      (Ne.symm (top_ne_floor j (j + 1)))
  have upperEmpty : target.visible.board (point 0 (j + 1)) = none := by
    rw [targetBoard]
    apply CoalitionBirth.empty_after_other (future _ (top_mem_frontier (by omega) (by omega)))
    intro same
    have columns := congrArg (fun p : Point 19 => p.2.val) same
    rw [point_column _ _ (by omega), point_column _ _ (by omega)] at columns
    omega
  have legal : stoneHasLiberty (boardAfterPlay target.visible.board .positive (point 1 (j + 1)))
      (point 1 (j + 1)) := by
    refine ⟨point 1 (j + 1), occupied_point_mem_groupAt (TwoEye.Growth.placed_survives _ _ _),
      point 0 (j + 1), vertical _, ?_⟩
    exact CoalitionBirth.empty_after_other upperEmpty (top_ne_floor _ _)
  have virgin : point 1 (j + 1) ∉ CoalitionBirth.retained frame .positive := by
    intro member
    exact (Finset.disjoint_left.mp fresh) (next_floor_mem_frontier (by omega)) member
  exact ⟨targetTurn, empty, legal, virgin⟩

def rawReply {frame target : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18)
    (step : LegalStep (Law.positionalSuperko 0) frame (.play (point 0 j)) target) : ScoringReply target :=
  let ready := reply_ready source beforeEdge step
  VirginHistory.reply target .positive (CoalitionBirth.retained frame .positive)
    (after_seal_tracked source step) (point 1 (j + 1)) ready.2.2.2
    (play_step_facts step).2.1 ready.1 ready.2.1 ready.2.2.1

theorem rawReply_move {frame target : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18)
    (step : LegalStep (Law.positionalSuperko 0) frame (.play (point 0 j)) target) :
    (rawReply source beforeEdge step).move = .play (point 1 (j + 1)) := rfl

theorem rawReply_source {frame target : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18)
    (step : LegalStep (Law.positionalSuperko 0) frame (.play (point 0 j)) target) :
    Source (rawReply source beforeEdge step).target (j + 1) divider := by
  have wallAfter := after_seal_wall source step
  have trackedAfter := after_seal_tracked source step
  rcases source with ⟨lower, upper, dividerLower, dividerUpper, gap, playing, opponent, passes,
    wall, rooms, left, future, fresh⟩
  have facts := CoalitionBirth.play_data step
  have targetBoard : target.visible.board = boardAfterPlay frame.visible.board .negative (point 0 j) := by
    rw [facts.2.2.1, opponent]
  have targetTurn : target.visible.toMove = .positive := by rw [facts.2.2.2, opponent]; rfl
  refine ⟨by omega, by omega, dividerLower, dividerUpper, by omega, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro p member
    dsimp only [rawReply, VirginHistory.reply, Frame.advance]
    rcases wall_next_split (j := j) (divider := divider) member with old | same
    · exact TwoEye.Growth.own_stone_survives (board := target.visible.board) (colour := .positive)
        (point := p) (wallAfter p old) (point 1 (j + 1))
    · subst p; exact TwoEye.Growth.placed_survives target.visible.board .positive (point 1 (j + 1))
  · intro p member
    dsimp only [rawReply, VirginHistory.reply, Frame.advance]
    apply own_not_own (board := target.visible.board) (colour := .positive) (played := point 1 (j + 1)) (p := p)
    · rw [targetBoard]
      rcases rooms_next_split (j := j) (divider := divider) member with old | same
      · exact opponent_not_own (board := frame.visible.board) (colour := .positive)
          (played := point 0 j) (p := p) (rooms p old)
      · subst p
        rw [TwoEye.Growth.placed_survives]
        decide
    · have row := rooms_row member
      rw [← point_at_row row]
      exact top_ne_floor _ _
  · obtain ⟨p, member, empty⟩ := left
    refine ⟨p, member, ?_⟩
    dsimp only [rawReply, VirginHistory.reply, Frame.advance]
    rw [targetBoard]
    apply CoalitionBirth.empty_after_other (board := boardAfterPlay frame.visible.board .negative (point 0 j))
      (colour := .positive) (played := point 1 (j + 1)) (point := p)
    · exact CoalitionBirth.empty_after_other (board := frame.visible.board) (colour := .negative)
        (played := point 0 j) (point := p) empty (left_ne_seal (by omega) (by omega) member)
    · rw [← point_at_row (mem_rowRange.mp member).1]
      exact top_ne_floor _ _
  · intro p member
    dsimp only [rawReply, VirginHistory.reply, Frame.advance]
    rw [targetBoard]
    apply CoalitionBirth.empty_after_other (board := boardAfterPlay frame.visible.board .negative (point 0 j))
      (colour := .positive) (played := point 1 (j + 1)) (point := p)
    · apply CoalitionBirth.empty_after_other (board := frame.visible.board) (colour := .negative)
        (played := point 0 j) (point := p) (future p (frontier_next_subset j member))
      intro same; subst p; exact next_frontier_not_seal (by omega) member
    · intro same; subst p; exact next_frontier_not_floor (by omega) member
  · have ready := reply_ready (frame := frame) (target := target) (j := j) (divider := divider)
      ⟨lower, upper, dividerLower, dividerUpper, gap, playing, opponent, passes,
        wall, rooms, left, future, fresh⟩ beforeEdge step
    have trackedNext : VirginHistory.Tracked
        (rawReply (frame := frame) (target := target) (j := j) (divider := divider) ⟨lower, upper, dividerLower, dividerUpper, gap, playing, opponent, passes,
          wall, rooms, left, future, fresh⟩ beforeEdge step).target .positive
        (insert (point 1 (j + 1)) (CoalitionBirth.retained frame .positive)) := by
      exact VirginHistory.reply_tracked target .positive (CoalitionBirth.retained frame .positive)
        trackedAfter (point 1 (j + 1)) ready.2.2.2 (play_step_facts step).2.1
        ready.1 ready.2.1 ready.2.2.1
    apply Finset.disjoint_left.mpr
    intro p member historical
    have inside := retained_subset_of_tracked trackedNext historical
    rcases Finset.mem_insert.mp inside with same | old
    · subst p; exact next_frontier_not_floor (by omega) member
    · exact (Finset.disjoint_left.mp fresh) (frontier_next_subset j member) old

structure Continuation (frame : Frame 19) (j divider : Nat) where
  reply : ScoringReply frame
  move_eq : reply.move = .play (point 1 (j + 1))
  next_source : Source reply.target (j + 1) divider

/-- Only the actually observed seal occupation invokes this continuation.
The next original source and its complete fresh frontier are generated by the two native steps. -/
def continuation {frame target : Frame 19} {j divider : Nat} (source : Source frame j divider)
    (beforeEdge : j < 18)
    (step : LegalStep (Law.positionalSuperko 0) frame (.play (point 0 j)) target) :
    Continuation target j divider :=
  let material := BufferedReplay.restore (BufferedReplay.capture target)
  have same : material = target := BufferedReplay.restore_capture target
  have native : LegalStep (Law.positionalSuperko 0) frame (.play (point 0 j)) material := by rw [same]; exact step
  let response := rawReply source beforeEdge native
  let next := BufferedReplay.restore (BufferedReplay.capture response.target)
  have nextSame : next = response.target := BufferedReplay.restore_capture response.target
  let stored : ScoringReply material :=
    ⟨response.move, next, response.notResign, by rw [nextSame]; exact response.step⟩
  let generated : Continuation material j divider := ⟨stored, rfl, by
    change Source next (j + 1) divider
    rw [nextSame]
    exact rawReply_source source beforeEdge native⟩
  same ▸ generated

end SaturationMonoid.ProcessGame.Go.CriticalKomi.CorridorContinuation
