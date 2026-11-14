import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionAction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.VirginHistory

/-- The retained carrier contains every point that has held the tracked colour.
Current stones may be captured; historical occupancy is never deleted. -/
def Tracked {n : Nat} (frame : Frame n) (colour : Polarity) (seen : Finset (Point n)) : Prop :=
  RegionAction.stones frame.visible.board colour ⊆ seen ∧
    ∀ previous ∈ frame.positionHistory, ∀ point,
      TwoEye.History.signatureCell previous.board point = some colour → point ∈ seen

theorem opponent_stones_subset {n : Nat} (board : Board n) (colour : Polarity) (played : Point n) :
    RegionAction.stones (boardAfterPlay board colour.other played) colour ⊆ RegionAction.stones board colour := by
  intro point member
  have occupied := (Finset.mem_filter.mp member).2
  have different : point ≠ played := by
    intro same
    subst point
    rw [TwoEye.Growth.placed_survives] at occupied
    exact Polarity.other_ne colour (Option.some.inj occupied)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold boardAfterPlay at occupied
  split at occupied
  · cases occupied
  · rw [Board.set_other _ _ different] at occupied
    exact occupied

private theorem play_board {n : Nat} {frame target : Frame n} {played : Point n}
    (step : LegalStep (Law.positionalSuperko 0) frame (.play played) target) :
    target.visible.board = boardAfterPlay frame.visible.board frame.visible.toMove played := by
  have visible := nativeStep_visible_eq step
  simp only [stepVisible?, playVisible?] at visible
  split at visible
  · simp at visible
  · split at visible
    · split at visible
      · split at visible
        · simp at visible
        · exact (congrArg VisiblePosition.board (Option.some.inj visible)).symm
      · simp at visible
    · simp at visible

def nextSeen {n : Nat} (frame : Frame n) (colour : Polarity) (seen : Finset (Point n)) :
    Move n → Finset (Point n)
  | .play point => if frame.visible.toMove = colour then insert point seen else seen
  | .pass | .resign => seen

theorem seen_subset_next {n : Nat} (frame : Frame n) (colour : Polarity)
    (seen : Finset (Point n)) (move : Move n) : seen ⊆ nextSeen frame colour seen move := by
  cases move <;> simp only [nextSeen]
  · split
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  · exact Finset.Subset.refl _
  · exact Finset.Subset.refl _

theorem step {n : Nat} {frame target : Frame n} {colour : Polarity} {seen : Finset (Point n)}
    (tracked : Tracked frame colour seen) {move : Move n} (scoring : move ≠ .resign)
    (native : LegalStep (Law.positionalSuperko 0) frame move target) :
    Tracked target colour (nextSeen frame colour seen move) := by
  have current : RegionAction.stones target.visible.board colour ⊆ nextSeen frame colour seen move := by
    cases move with
    | resign => exact False.elim (scoring rfl)
    | pass => rw [(pass_step_facts native).2.1]; exact tracked.1
    | play point =>
        rw [play_board native]
        by_cases own : frame.visible.toMove = colour
        · rw [own, RegionAction.own_stones]
          simpa only [nextSeen, if_pos own] using Finset.insert_subset_insert point tracked.1
        · have other : frame.visible.toMove = colour.other := by
            cases colour <;> cases turn : frame.visible.toMove <;> simp_all [Polarity.other]
          rw [other]
          simpa only [nextSeen, if_neg own] using
            (opponent_stones_subset frame.visible.board colour point).trans tracked.1
  refine ⟨current, ?_⟩
  intro previous member point occupied
  rw [nativeStep_positionHistory_eq native] at member
  rcases List.mem_append.mp member with old | latest
  · exact seen_subset_next frame colour seen move (tracked.2 previous old point occupied)
  · have same := List.mem_singleton.mp latest
    subst previous
    rw [VisiblePosition.situation, TwoEye.History.signatureCell_boardSignature] at occupied
    exact current (Finset.mem_filter.mpr ⟨Finset.mem_univ _, occupied⟩)

theorem initial (n : Nat) (colour : Polarity) : Tracked (Frame.initial n) colour ∅ := by
  constructor
  · simp [RegionAction.stones, Frame.initial, Board.empty]
  · intro previous member point occupied
    have same : previous = (Frame.initial n).visible.situation := by
      simpa only [Frame.initial, VisiblePosition.situation, List.mem_singleton] using member
    subst previous
    rw [VisiblePosition.situation, TwoEye.History.signatureCell_boardSignature] at occupied
    cases occupied

def fromReplay {n : Nat} {start : Frame n} {moves : List (Move n)}
    (replay : GeneratedReplay (Law.positionalSuperko 0) start moves)
    (colour : Polarity) (seen : Finset (Point n)) (tracked : Tracked start colour seen)
    (scoring : ∀ move ∈ moves, move ≠ .resign) :
    {next : Finset (Point n) // Tracked replay.final colour next} :=
  match replay with
  | .nil _ => ⟨seen, tracked⟩
  | .cons move native tail =>
      fromReplay tail colour (nextSeen start colour seen move)
        (step tracked (scoring move List.mem_cons_self) native)
        (fun later member => scoring later (List.mem_cons_of_mem _ member))

theorem fresh {n : Nat} {frame : Frame n} {colour : Polarity} {seen : Finset (Point n)}
    (tracked : Tracked frame colour seen) {played : Point n} (virgin : played ∉ seen) :
    ¬ violatesRepetition .positionalSuperko frame.positionHistory
      ⟨boardSignature (boardAfterPlay frame.visible.board colour played), colour.other⟩ := by
  rintro ⟨previous, member, same⟩
  apply virgin
  apply tracked.2 previous member played
  rw [same, TwoEye.History.signatureCell_boardSignature]
  exact TwoEye.Growth.placed_survives _ _ _

/-- The original no-suicide guard and a source-unplayed point generate the
native move even after some earlier own stones have been captured. -/
def reply {n : Nat} (frame : Frame n) (colour : Polarity) (seen : Finset (Point n))
    (tracked : Tracked frame colour seen) (played : Point n) (virgin : played ∉ seen)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (empty : frame.visible.board played = none)
    (legal : stoneHasLiberty (boardAfterPlay frame.visible.board colour played) played) :
    ScoringReply frame where
  move := .play played
  target := frame.advance {
    board := boardAfterPlay frame.visible.board colour played
    toMove := colour.other
    consecutivePasses := 0
    status := .playing
  }
  notResign := by simp
  step := by
    have new := fresh tracked virgin
    simp only [LegalStep, nativeStep?, stepVisible?, playVisible?, playing, owned,
      if_pos empty, if_pos legal, Law.positionalSuperko, if_neg new, Option.map_some]

theorem reply_tracked {n : Nat} (frame : Frame n) (colour : Polarity) (seen : Finset (Point n))
    (tracked : Tracked frame colour seen) (played : Point n) (virgin : played ∉ seen)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (empty : frame.visible.board played = none)
    (legal : stoneHasLiberty (boardAfterPlay frame.visible.board colour played) played) :
    Tracked (reply frame colour seen tracked played virgin playing owned empty legal).target
      colour (insert played seen) := by
  have generated := step tracked (reply frame colour seen tracked played virgin playing owned empty legal).notResign
    (reply frame colour seen tracked played virgin playing owned empty legal).step
  simpa only [reply, nextSeen, if_pos owned] using generated

end SaturationMonoid.ProcessGame.Go.CriticalKomi.VirginHistory
