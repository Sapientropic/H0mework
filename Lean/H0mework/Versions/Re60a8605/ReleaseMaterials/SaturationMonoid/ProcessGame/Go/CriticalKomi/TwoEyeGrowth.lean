import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeClosure
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeHistory

/-!
An actual own placement can enlarge a living core.  The old permanent core
filters superko history; a previously unowned attached point supplies a fresh
native action and becomes part of the next core.  These are source board and
history tests, with no supplied future policy or legality certificate.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye.Growth

theorem own_placed_survives {n : Nat} {board : Board n} {colour : Polarity}
    {played point : Point n}
    (occupied : Board.set board played (some colour) point = some colour) :
    boardAfterPlay board colour played point = some colour := by
  have retained : point ∉ capturedStonesAfterPlay board colour played := by
    intro captured
    have opposite := capturedStonesAfterPlay_member_placed_colour captured
    exact Polarity.other_ne colour (Option.some.inj (opposite.symm.trans occupied))
  rw [boardAfterPlay_eq_placed_of_not_mem_captured retained]
  exact occupied

theorem own_stone_survives {n : Nat} {board : Board n} {colour : Polarity}
    {point : Point n} (occupied : board point = some colour) (played : Point n) :
    boardAfterPlay board colour played point = some colour := by
  apply own_placed_survives
  by_cases same : point = played
  · subst point
    exact Board.set_self _ _ _
  · rw [Board.set_other _ _ same]
    exact occupied

theorem placed_survives {n : Nat} (board : Board n) (colour : Polarity) (played : Point n) :
    boardAfterPlay board colour played played = some colour :=
  own_placed_survives (Board.set_self _ _ _)

theorem own_preserves {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (inside : Holds g colour board) (played : Point n) (empty : board played = none)
    (first : played ≠ g.eye₁) (second : played ≠ g.eye₂) :
    Holds g colour (boardAfterPlay board colour played) := by
  have seedAfter := own_stone_survives inside.1 played
  refine ⟨seedAfter, ?_, ?_, ?_⟩
  · intro point member
    have before : point ∈ componentAt board g.seed := by
      simpa only [groupAt, inside.1] using inside.2.1 member
    have after := componentAt_subset_boardAfterPlay_of_seed_survives
      empty inside.1 seedAfter before
    simpa only [groupAt, seedAfter] using after
  · unfold boardAfterPlay
    split
    · rfl
    · rw [Board.set_other _ _ (Ne.symm first)]
      exact inside.2.2.1
  · unfold boardAfterPlay
    split
    · rfl
    · rw [Board.set_other _ _ (Ne.symm second)]
      exact inside.2.2.2

def enlarge {n : Nat} (g : Geometry n) (point : Point n) : Geometry n where
  seed := g.seed
  core := insert point g.core
  eye₁ := g.eye₁
  eye₂ := g.eye₂
  distinct := g.distinct
  boundary₁ := g.boundary₁.trans (Finset.subset_insert _ _)
  boundary₂ := g.boundary₂.trans (Finset.subset_insert _ _)
  neighbour₁ := g.neighbour₁
  neighbour₂ := g.neighbour₂

def Attached {n : Nat} (g : Geometry n) (point : Point n) : Prop :=
  ∃ neighbour ∈ g.core, point ∈ adjacentPoints neighbour

instance {n : Nat} (g : Geometry n) (point : Point n) : Decidable (Attached g point) :=
  inferInstanceAs (Decidable (∃ neighbour ∈ g.core, point ∈ adjacentPoints neighbour))

theorem own_enlarges {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (inside : Holds g colour board) (played : Point n) (empty : board played = none)
    (first : played ≠ g.eye₁) (second : played ≠ g.eye₂) (attached : Attached g played) :
    Holds (enlarge g played) colour (boardAfterPlay board colour played) := by
  have preserved := own_preserves inside played empty first second
  refine ⟨preserved.1, ?_, preserved.2.2.1, preserved.2.2.2⟩
  intro point member
  change point ∈ groupAt (boardAfterPlay board colour played) g.seed
  rcases Finset.mem_insert.mp member with newly | old
  · subst point
    obtain ⟨neighbour, core, adjacent⟩ := attached
    have neighbourIn := preserved.2.1 core
    have playedColour := placed_survives board colour played
    unfold groupAt at neighbourIn ⊢
    rw [preserved.1] at neighbourIn ⊢
    apply componentAt_closed neighbourIn
      (by simpa only [adjacentPoints, List.mem_toFinset] using adjacent)
    exact playedColour.trans preserved.1.symm
  · exact preserved.2.1 old

theorem seed_has_liberty {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (inside : Holds g colour board) : stoneHasLiberty board g.seed := by
  obtain ⟨neighbour, adjacent⟩ := g.neighbour₁
  refine ⟨neighbour, inside.2.1 (g.boundary₁ adjacent), g.eye₁, ?_, inside.2.2.1⟩
  exact mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
    (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent))

theorem growing_has_liberty {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (inside : Holds g colour board) (played : Point n) (empty : board played = none)
    (first : played ≠ g.eye₁) (second : played ≠ g.eye₂) (attached : Attached g played) :
    stoneHasLiberty (boardAfterPlay board colour played) played := by
  have grown := own_enlarges inside played empty first second attached
  have member := grown.2.1 (Finset.mem_insert_self played g.core)
  have same := groupAt_eq_of_mem grown.1 member
  unfold stoneHasLiberty
  rw [same]
  exact seed_has_liberty grown

/-- Only old signatures compatible with the permanent core can obstruct this growth. -/
def Virgin {n : Nat} (g : Geometry n) (colour : Polarity) (point : Point n)
    (history : List (Situation n)) : Prop :=
  ∀ old ∈ history, History.Compatible g colour old.board →
    History.signatureCell old.board point ≠ some colour

instance {n : Nat} (g : Geometry n) (colour : Polarity) (point : Point n)
    (history : List (Situation n)) : Decidable (Virgin g colour point history) :=
  inferInstanceAs (Decidable (∀ old ∈ history, History.Compatible g colour old.board →
    History.signatureCell old.board point ≠ some colour))

theorem virgin_step {n : Nat} {g : Geometry n} {colour : Polarity} {point : Point n}
    {frame target : Frame n} {move : Move n}
    (before : Virgin g colour point frame.positionHistory)
    (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (unowned : target.visible.board point ≠ some colour) :
    Virgin g colour point target.positionHistory := by
  intro old member compatible
  rw [nativeStep_positionHistory_eq step] at member
  rcases List.mem_append.mp member with oldMember | latest
  · exact before old oldMember compatible
  · have same := List.mem_singleton.mp latest
    subst old
    simpa only [VisiblePosition.situation, History.signatureCell_boardSignature] using unowned

theorem growing_fresh {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (inside : Holds g colour board) (played : Point n) (empty : board played = none)
    (first : played ≠ g.eye₁) (second : played ≠ g.eye₂)
    (history : List (Situation n)) (virgin : Virgin g colour played history) :
    ¬ violatesRepetition .positionalSuperko history
      ⟨boardSignature (boardAfterPlay board colour played), colour.other⟩ := by
  rintro ⟨old, member, same⟩
  have preserved := own_preserves inside played empty first second
  have compatible := History.compatible_of_holds preserved
  have absent := virgin old member (same ▸ compatible)
  apply absent
  rw [same, History.signatureCell_boardSignature]
  exact placed_survives board colour played

/-- A source-generated legal move; the history guard is paid by permanence plus one new stone. -/
def reply {n : Nat} {g : Geometry n} {colour : Polarity} (frame : Frame n)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (inside : Holds g colour frame.visible.board) (played : Point n)
    (empty : frame.visible.board played = none) (first : played ≠ g.eye₁)
    (second : played ≠ g.eye₂) (attached : Attached g played)
    (virgin : Virgin g colour played frame.positionHistory) : ScoringReply frame where
  move := .play played
  target := frame.advance {
    board := boardAfterPlay frame.visible.board colour played
    toMove := colour.other
    consecutivePasses := 0
    status := .playing
  }
  notResign := by simp
  step := by
    have legal := growing_has_liberty inside played empty first second attached
    have fresh := growing_fresh inside played empty first second frame.positionHistory virgin
    simp only [LegalStep, nativeStep?, stepVisible?, playVisible?, playing, owned,
      if_pos empty, if_pos legal, Law.positionalSuperko, if_neg fresh, Option.map_some]

theorem reply_enlarges {n : Nat} {g : Geometry n} {colour : Polarity} (frame : Frame n)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (inside : Holds g colour frame.visible.board) (played : Point n)
    (empty : frame.visible.board played = none) (first : played ≠ g.eye₁)
    (second : played ≠ g.eye₂) (attached : Attached g played)
    (virgin : Virgin g colour played frame.positionHistory) :
    Holds (enlarge g played) colour
      (reply frame playing owned inside played empty first second attached virgin).target.visible.board :=
  own_enlarges inside played empty first second attached

end SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye.Growth
