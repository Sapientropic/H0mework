import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.ComponentCorrectness
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Survival
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Forcing

/-!
One-step source liberty reserves, before a permanent living core exists.
Every liberty is a deduplicated empty neighbour of the original generated
component.  A reserve pays one opponent move; it is not an infinite survival
or a corner-birth assertion.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.LibertyReserve

def liberties {n : Nat} (board : Board n) (seed : Point n) : Finset (Point n) :=
  ((groupAt board seed).biUnion adjacentPoints).filter (fun point => board point = none)

@[simp] theorem mem_liberties {n : Nat} {board : Board n} {seed liberty : Point n} :
    liberty ∈ liberties board seed ↔
      (∃ stone ∈ groupAt board seed, liberty ∈ adjacentPoints stone) ∧ board liberty = none := by
  simp [liberties]

theorem seed_survives {n : Nat} {board : Board n}
    {colour : Polarity} {seed left right played : Point n}
    (occupied : board seed = some colour)
    (leftLiberty : left ∈ liberties board seed) (rightLiberty : right ∈ liberties board seed)
    (distinct : left ≠ right) (empty : board played = none) :
    boardAfterPlay board colour.other played seed = some colour := by
  have placedLiberty : stoneHasLiberty (Board.set board played (some colour.other)) seed := by
    unfold stoneHasLiberty
    rw [groupAt_placed_opponent_eq empty (by simpa using occupied)]
    by_cases leftPlayed : left = played
    · obtain ⟨⟨stone, member, adjacent⟩, free⟩ := mem_liberties.mp rightLiberty
      refine ⟨stone, member, right, adjacent, ?_⟩
      rw [Board.set_other]
      · exact free
      · intro rightPlayed
        exact distinct (leftPlayed.trans rightPlayed.symm)
    · obtain ⟨⟨stone, member, adjacent⟩, free⟩ := mem_liberties.mp leftLiberty
      refine ⟨stone, member, left, adjacent, ?_⟩
      rw [Board.set_other _ _ leftPlayed]
      exact free
  have notCaptured : seed ∉ capturedStonesAfterPlay board colour.other played := by
    intro captured
    unfold capturedStonesAfterPlay at captured
    simp only [Finset.mem_biUnion] at captured
    obtain ⟨neighbour, _, member⟩ := captured
    split at member
    · rename_i capturedGroup
      have sameGroup := groupAt_eq_of_mem capturedGroup.1 member
      apply capturedGroup.2
      unfold stoneHasLiberty at placedLiberty ⊢
      rw [← sameGroup]
      exact placedLiberty
    · simp at member
  rw [boardAfterPlay_eq_placed_of_not_mem_captured notCaptured]
  rw [Board.set_other]
  · exact occupied
  · intro same
    rw [same, empty] at occupied
    cases occupied

theorem seed_survives_of_two {n : Nat} {board : Board n} {colour : Polarity}
    {seed played : Point n} (occupied : board seed = some colour)
    (reserve : 2 ≤ (liberties board seed).card) (empty : board played = none) :
    boardAfterPlay board colour.other played seed = some colour := by
  obtain ⟨left, leftMember, right, rightMember, distinct⟩ :=
    Finset.one_lt_card.mp reserve
  exact seed_survives occupied leftMember rightMember distinct empty

theorem whole_group_survives {n : Nat} {board : Board n} {colour : Polarity}
    {seed played : Point n} (occupied : board seed = some colour)
    (reserve : 2 ≤ (liberties board seed).card) (empty : board played = none)
    {point : Point n} (member : point ∈ groupAt board seed) :
    point ∉ capturedStonesAfterPlay board colour.other played :=
  source_group_not_captured_of_seed_survives empty occupied
    (seed_survives_of_two occupied reserve empty) member

/-- Same-action whole-component transport is generated from the surviving seed. -/
theorem group_subset_after {n : Nat} {board : Board n} {colour : Polarity}
    {seed played : Point n} (occupied : board seed = some colour)
    (reserve : 2 ≤ (liberties board seed).card) (empty : board played = none) :
    groupAt board seed ⊆ groupAt (boardAfterPlay board colour.other played) seed := by
  have after := seed_survives_of_two occupied reserve empty
  simpa only [groupAt, occupied, after] using
    (componentAt_subset_boardAfterPlay_of_seed_survives empty occupied after)

/-- Every original liberty except the played point remains an actual empty
neighbour of the transported original group. -/
theorem liberties_erase_subset {n : Nat} {board : Board n} {colour : Polarity}
    {seed played : Point n} (occupied : board seed = some colour)
    (reserve : 2 ≤ (liberties board seed).card) (empty : board played = none) :
    (liberties board seed).erase played ⊆
      liberties (boardAfterPlay board colour.other played) seed := by
  intro liberty member
  obtain ⟨notPlayed, member⟩ := Finset.mem_erase.mp member
  obtain ⟨⟨stone, stoneMember, adjacent⟩, free⟩ := mem_liberties.mp member
  apply mem_liberties.mpr
  refine ⟨⟨stone, group_subset_after occupied reserve empty stoneMember, adjacent⟩, ?_⟩
  unfold boardAfterPlay
  split
  · rfl
  · rw [Board.set_other _ _ notPlayed]
    exact free

theorem loses_at_most_one {n : Nat} {board : Board n} {colour : Polarity}
    {seed played : Point n} (occupied : board seed = some colour)
    (reserve : 2 ≤ (liberties board seed).card) (empty : board played = none) :
    (liberties board seed).card ≤
      (liberties (boardAfterPlay board colour.other played) seed).card + 1 := by
  have retained := Finset.card_le_card (liberties_erase_subset occupied reserve empty)
  have erase := Finset.pred_card_le_card_erase (s := liberties board seed) (a := played)
  omega

/-- Original PSK play/pass successors preserve the exact source seed and
spend at most one liberty.  There is no future-opponent input. -/
theorem opponent_legalStep {n : Nat} {frame target : Frame n} {move : Move n}
    {colour : Polarity} {seed : Point n}
    (occupied : frame.visible.board seed = some colour)
    (reserve : 2 ≤ (liberties frame.visible.board seed).card)
    (opponent : frame.visible.toMove = colour.other) (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    target.visible.board seed = some colour ∧
      (liberties frame.visible.board seed).card ≤ (liberties target.visible.board seed).card + 1 := by
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass =>
      have boardEq := (pass_step_facts step).2.1
      rw [boardEq]
      exact ⟨occupied, Nat.le_succ _⟩
  | play played =>
      have visible := nativeStep_visible_eq step
      simp only [stepVisible?, playVisible?] at visible
      split at visible
      · simp at visible
      · split at visible
        · rename_i empty
          split at visible
          · split at visible
            · simp at visible
            · have boardEq := congrArg VisiblePosition.board (Option.some.inj visible)
              rw [← boardEq, opponent]
              exact ⟨seed_survives_of_two occupied reserve empty,
                loses_at_most_one occupied reserve empty⟩
          · simp at visible
        · simp at visible

private theorem boardAfterPlay_empty {n : Nat} (colour : Polarity) (played : Point n) :
    boardAfterPlay Board.empty colour played = Board.set Board.empty played (some colour) := by
  funext point
  apply boardAfterPlay_eq_placed_of_not_mem_captured
  intro captured
  have opposite := capturedStonesAfterPlay_member_placed_colour captured
  by_cases same : point = played
  · subst point
    rw [Board.set_self] at opposite
    exact Polarity.other_ne colour (Option.some.inj opposite).symm
  · rw [Board.set_other _ _ same] at opposite
    cases opposite

def openingPoint : Point 19 := ((1 : Fin 19), (1 : Fin 19))

def openingBoard : Board 19 := boardAfterPlay Board.empty .positive openingPoint

theorem openingBoard_eq :
    openingBoard = Board.set Board.empty openingPoint (some .positive) :=
  boardAfterPlay_empty .positive openingPoint

theorem opening_occupied : openingBoard openingPoint = some .positive := by
  rw [openingBoard_eq, Board.set_self]

private theorem opening_has_liberty : stoneHasLiberty openingBoard openingPoint := by
  refine ⟨openingPoint, occupied_point_mem_groupAt opening_occupied,
    ((0 : Fin 19), (1 : Fin 19)), ?_, ?_⟩
  · decide
  · rw [openingBoard_eq, Board.set_other]
    · rfl
    · decide

private theorem opening_fresh :
    ¬ violatesRepetition .positionalSuperko (Frame.initial 19).positionHistory
      ⟨boardSignature openingBoard, .negative⟩ := by
  rintro ⟨previous, member, same⟩
  have previousEq : previous = (Frame.initial 19).visible.situation := by
    simpa only [Frame.initial, VisiblePosition.situation, List.mem_singleton] using member
  subst previous
  have boards : (Board.empty : Board 19) = openingBoard := boardSignature_injective same
  have atPoint := congrFun boards openingPoint
  change none = openingBoard openingPoint at atPoint
  rw [opening_occupied] at atPoint
  cases atPoint

def openingVisible : VisiblePosition 19 where
  board := openingBoard
  toMove := .negative
  consecutivePasses := 0
  status := .playing

/-- The source actually computes the original first move; the target is the
native board-after-play image with its native history append. -/
def opening19 : ScoringReply (Frame.initial 19) where
  move := .play openingPoint
  target := (Frame.initial 19).advance openingVisible
  notResign := by intro impossible; cases impossible
  step := by
    change
      (if (Board.empty : Board 19) openingPoint = none then
        if stoneHasLiberty openingBoard openingPoint then
          if violatesRepetition .positionalSuperko (Frame.initial 19).positionHistory
              ⟨boardSignature openingBoard, .negative⟩ then none
          else some openingVisible
        else none
      else none).map (Frame.advance (Frame.initial 19)) =
        some ((Frame.initial 19).advance openingVisible)
    simp only [Board.empty, opening_has_liberty, opening_fresh, ↓reduceIte, Option.map_some]

theorem opening_group : groupAt openingBoard openingPoint = {openingPoint} := by
  ext point
  constructor
  · intro member
    have occupied := groupAt_member_colour opening_occupied member
    by_cases same : point = openingPoint
    · exact Finset.mem_singleton.mpr same
    · rw [openingBoard_eq, Board.set_other _ _ same] at occupied
      cases occupied
  · intro member
    have same := Finset.mem_singleton.mp member
    subst point
    exact occupied_point_mem_groupAt opening_occupied

theorem opening_liberties : liberties openingBoard openingPoint = adjacentPoints openingPoint := by
  ext liberty
  rw [mem_liberties, opening_group]
  constructor
  · rintro ⟨⟨stone, member, adjacent⟩, _⟩
    have same := Finset.mem_singleton.mp member
    subst stone
    exact adjacent
  · intro adjacent
    refine ⟨⟨openingPoint, Finset.mem_singleton_self _, adjacent⟩, ?_⟩
    have different : liberty ≠ openingPoint := by
      intro same
      subst liberty
      exact not_orthogonallyAdjacent_self openingPoint
        (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent)
    rw [openingBoard_eq, Board.set_other _ _ different]
    rfl

theorem opening_liberties_card : (liberties openingBoard openingPoint).card = 4 := by
  rw [opening_liberties]
  decide

/-- Every original legal white play/pass response preserves the generated
black seed and at least three original-source liberties. -/
theorem opening19_responses (move : Move 19) (target : Frame 19)
    (step : LegalStep (Law.positionalSuperko 0) opening19.target move target)
    (scoring : move ≠ .resign) :
    target.visible.board openingPoint = some .positive ∧
      3 ≤ (liberties target.visible.board openingPoint).card := by
  have reserve : 2 ≤ (liberties opening19.target.visible.board openingPoint).card := by
    change 2 ≤ (liberties openingBoard openingPoint).card
    rw [opening_liberties_card]
    decide
  have response := opponent_legalStep (colour := .positive)
    opening_occupied reserve rfl scoring step
  refine ⟨response.1, ?_⟩
  have count : (liberties opening19.target.visible.board openingPoint).card = 4 :=
    opening_liberties_card
  omega

/-- The dependent port mouth plugs directly into the existing native ∀-node. -/
theorem opening19_port (port : Fin (scoringExpansion opening19.target).length) :
    ((scoringExpansion opening19.target).get port).2.visible.board openingPoint =
        some .positive ∧
      3 ≤ (liberties ((scoringExpansion opening19.target).get port).2.visible.board
        openingPoint).card := by
  generalize childEq : (scoringExpansion opening19.target).get port = child
  rcases child with ⟨move, target⟩
  have member : (move, target) ∈ scoringExpansion opening19.target := by
    rw [← childEq]
    exact List.get_mem _ _
  have facts := mem_scoringExpansion_iff.mp member
  exact opening19_responses _ _ facts.1 facts.2

def opening19_response_replay (move : Move 19) (target : Frame 19)
    (step : LegalStep (Law.positionalSuperko 0) opening19.target move target) :
    GeneratedReplay (Law.positionalSuperko 0) (Frame.initial 19) [opening19.move, move] :=
  .cons opening19.move opening19.step (.cons move step (.nil target))

end SaturationMonoid.ProcessGame.Go.CriticalKomi.LibertyReserve
