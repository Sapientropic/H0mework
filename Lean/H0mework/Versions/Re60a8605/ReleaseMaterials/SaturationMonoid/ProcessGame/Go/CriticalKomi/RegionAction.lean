import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.LibertyReserve
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeGrowth

/-!
Raw action facts for an initial-region birth calculation.  During its reserved
single-group phase an opponent cannot remove an own stone.  An outside placement
is a spatial stutter, retaining its actual play event and history rather than
being changed into a pass.  Monotone own-stone counts pay fresh original PSK moves.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionAction

def OneGroup {n : Nat} (board : Board n) (colour : Polarity) (seed : Point n) : Prop :=
  ∀ point, board point = some colour → point ∈ groupAt board seed

theorem opponent_capture_empty {n : Nat} {board : Board n} {colour : Polarity}
    {seed played : Point n} (occupied : board seed = some colour)
    (single : OneGroup board colour seed)
    (reserve : 2 ≤ (LibertyReserve.liberties board seed).card)
    (empty : board played = none) :
    capturedStonesAfterPlay board colour.other played = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro point captured
  have placed := capturedStonesAfterPlay_member_placed_colour captured
  rw [Polarity.other_other] at placed
  have different : point ≠ played := by
    intro same
    subst point
    rw [Board.set_self] at placed
    exact Polarity.other_ne colour (Option.some.inj placed)
  rw [Board.set_other _ _ different] at placed
  exact LibertyReserve.whole_group_survives occupied reserve empty (single point placed) captured

theorem opponent_is_placement {n : Nat} {board : Board n} {colour : Polarity}
    {seed played : Point n} (occupied : board seed = some colour)
    (single : OneGroup board colour seed)
    (reserve : 2 ≤ (LibertyReserve.liberties board seed).card)
    (empty : board played = none) :
    boardAfterPlay board colour.other played = Board.set board played (some colour.other) := by
  funext point
  simp [boardAfterPlay, opponent_capture_empty occupied single reserve empty]

theorem outside_placement_restricts {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity} {seed played : Point n}
    (occupied : board seed = some colour) (single : OneGroup board colour seed)
    (reserve : 2 ≤ (LibertyReserve.liberties board seed).card)
    (empty : board played = none) (outside : played ∉ region)
    (point : Point n) (inside : point ∈ region) :
    boardAfterPlay board colour.other played point = board point := by
  rw [opponent_is_placement occupied single reserve empty]
  apply Board.set_other
  intro same
  exact outside (same ▸ inside)

def stones {n : Nat} (board : Board n) (colour : Polarity) : Finset (Point n) :=
  Finset.univ.filter (fun point => board point = some colour)

theorem own_stones {n : Nat} (board : Board n) (colour : Polarity) (played : Point n) :
    stones (boardAfterPlay board colour played) colour = insert played (stones board colour) := by
  ext point
  simp only [stones, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro occupied
    by_cases same : point = played
    · exact Or.inl same
    · right
      unfold boardAfterPlay at occupied
      split at occupied
      · cases occupied
      · rw [Board.set_other _ _ same] at occupied
        exact occupied
  · rintro (same | occupied)
    · subst point
      exact TwoEye.Growth.placed_survives _ _ _
    · exact TwoEye.Growth.own_stone_survives occupied played

theorem own_stones_card {n : Nat} {board : Board n} {colour : Polarity} {played : Point n}
    (empty : board played = none) :
    (stones (boardAfterPlay board colour played) colour).card = (stones board colour).card + 1 := by
  rw [own_stones, Finset.card_insert_of_notMem]
  simp [stones, empty]

theorem opponent_stones {n : Nat} {board : Board n} {colour : Polarity} {seed played : Point n}
    (occupied : board seed = some colour) (single : OneGroup board colour seed)
    (reserve : 2 ≤ (LibertyReserve.liberties board seed).card)
    (empty : board played = none) :
    stones (boardAfterPlay board colour.other played) colour = stones board colour := by
  rw [opponent_is_placement occupied single reserve empty]
  ext point
  simp only [stones, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases same : point = played
  · subst point
    rw [Board.set_self, empty]
    simp [Polarity.other_ne]
  · rw [Board.set_other _ _ same]

theorem opponent_oneGroup {n : Nat} {board : Board n} {colour : Polarity} {seed played : Point n}
    (occupied : board seed = some colour) (single : OneGroup board colour seed)
    (reserve : 2 ≤ (LibertyReserve.liberties board seed).card)
    (empty : board played = none) :
    OneGroup (boardAfterPlay board colour.other played) colour seed := by
  have groupEq : groupAt (boardAfterPlay board colour.other played) seed = groupAt board seed := by
    rw [opponent_is_placement occupied single reserve empty]
    exact groupAt_placed_opponent_eq empty (by simpa only [Polarity.other_other] using occupied)
  intro point owned
  rw [groupEq]
  apply single point
  have member : point ∈ stones (boardAfterPlay board colour.other played) colour := by
    simp only [stones, Finset.mem_filter, Finset.mem_univ, true_and]
    exact owned
  rw [opponent_stones occupied single reserve empty] at member
  exact (Finset.mem_filter.mp member).2

def signatureCount {n : Nat} (signature : BoardSignature n) (colour : Polarity) : Nat :=
  (Finset.univ.filter (fun point => TwoEye.History.signatureCell signature point = some colour)).card

theorem signatureCount_board {n : Nat} (board : Board n) (colour : Polarity) :
    signatureCount (boardSignature board) colour = (stones board colour).card := by
  simp only [signatureCount, TwoEye.History.signatureCell_boardSignature, stones]

def HistoryBound {n : Nat} (frame : Frame n) (colour : Polarity) : Prop :=
  ∀ previous ∈ frame.positionHistory,
    signatureCount previous.board colour ≤ (stones frame.visible.board colour).card

theorem growth_fresh {n : Nat} {frame : Frame n} {colour : Polarity} {played : Point n}
    (history : HistoryBound frame colour) (empty : frame.visible.board played = none) :
    ¬ violatesRepetition .positionalSuperko frame.positionHistory
      ⟨boardSignature (boardAfterPlay frame.visible.board colour played), colour.other⟩ := by
  rintro ⟨previous, member, same⟩
  have bound := history previous member
  rw [same, signatureCount_board, own_stones_card empty] at bound
  omega

theorem historyBound_step {n : Nat} {frame target : Frame n} {move : Move n} {colour : Polarity}
    (history : HistoryBound frame colour)
    (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (monotone : (stones frame.visible.board colour).card ≤ (stones target.visible.board colour).card) :
    HistoryBound target colour := by
  intro previous member
  rw [nativeStep_positionHistory_eq step] at member
  rcases List.mem_append.mp member with old | latest
  · exact (history previous old).trans monotone
  · have same := List.mem_singleton.mp latest
    subst previous
    simp only [VisiblePosition.situation, signatureCount_board, le_refl]

/-- A local placed-board reserve and the retained prefix count generate a
native placement; no superko oracle or future strategy is supplied. -/
def playReply {n : Nat} (frame : Frame n) (colour : Polarity) (played : Point n)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (empty : frame.visible.board played = none) (history : HistoryBound frame colour)
    (reserve : 2 ≤ (LibertyReserve.liberties
      (boardAfterPlay frame.visible.board colour played) played).card) : ScoringReply frame where
  move := .play played
  target := frame.advance {
    board := boardAfterPlay frame.visible.board colour played
    toMove := colour.other
    consecutivePasses := 0
    status := .playing
  }
  notResign := by simp
  step := by
    have nonempty := Finset.card_pos.mp (show 0 < (LibertyReserve.liberties
      (boardAfterPlay frame.visible.board colour played) played).card from by omega)
    obtain ⟨liberty, member⟩ := nonempty
    obtain ⟨⟨stone, groupMember, adjacent⟩, free⟩ := LibertyReserve.mem_liberties.mp member
    have legal : stoneHasLiberty (boardAfterPlay frame.visible.board colour played) played :=
      ⟨stone, groupMember, liberty, adjacent, free⟩
    have fresh := growth_fresh history empty
    simp only [LegalStep, nativeStep?, stepVisible?, playVisible?, playing, owned,
      if_pos empty, if_pos legal, Law.positionalSuperko, if_neg fresh, Option.map_some]

theorem playReply_history {n : Nat} (frame : Frame n) (colour : Polarity) (played : Point n)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (empty : frame.visible.board played = none) (history : HistoryBound frame colour)
    (reserve : 2 ≤ (LibertyReserve.liberties
      (boardAfterPlay frame.visible.board colour played) played).card) :
    HistoryBound (playReply frame colour played playing owned empty history reserve).target colour := by
  apply historyBound_step history (playReply frame colour played playing owned empty history reserve).step
  change (stones frame.visible.board colour).card ≤
    (stones (boardAfterPlay frame.visible.board colour played) colour).card
  rw [own_stones_card empty]
  omega

theorem own_oneGroup {n : Nat} {board : Board n} {colour : Polarity} {seed played : Point n}
    (occupied : board seed = some colour) (single : OneGroup board colour seed)
    (empty : board played = none)
    (attached : ∃ stone ∈ groupAt board seed, played ∈ adjacentPoints stone) :
    OneGroup (boardAfterPlay board colour played) colour seed := by
  have after := TwoEye.Growth.own_stone_survives occupied played
  have oldGroup : groupAt board seed ⊆ groupAt (boardAfterPlay board colour played) seed := by
    simpa only [groupAt, occupied, after] using
      (componentAt_subset_boardAfterPlay_of_seed_survives empty occupied after)
  have playedMember : played ∈ groupAt (boardAfterPlay board colour played) seed := by
    obtain ⟨stone, member, adjacent⟩ := attached
    have stoneMember := oldGroup member
    unfold groupAt at stoneMember ⊢
    rw [after] at stoneMember ⊢
    exact componentAt_closed stoneMember
      (by simpa only [adjacentPoints, List.mem_toFinset] using adjacent)
      ((TwoEye.Growth.placed_survives board colour played).trans after.symm)
  intro point colourAfter
  have member : point ∈ stones (boardAfterPlay board colour played) colour := by
    simp only [stones, Finset.mem_filter, Finset.mem_univ, true_and]
    exact colourAfter
  rw [own_stones] at member
  rcases Finset.mem_insert.mp member with same | old
  · subst point
    exact playedMember
  · apply oldGroup
    apply single point
    exact (Finset.mem_filter.mp old).2

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionAction
