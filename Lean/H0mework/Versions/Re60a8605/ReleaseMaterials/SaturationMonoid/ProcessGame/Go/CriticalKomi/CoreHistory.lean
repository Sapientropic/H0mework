import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VirginHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CoreHistory

/-- Every previous actual board differs from this proposed own footprint at
some footprint point. Previously owned points may participate in a new joint core. -/
def Fresh {n : Nat} (frame : Frame n) (colour : Polarity) (core : Finset (Point n)) : Prop :=
  ∀ previous ∈ frame.positionHistory,
    ¬ ∀ point ∈ core, TwoEye.History.signatureCell previous.board point = some colour

instance {n : Nat} (frame : Frame n) (colour : Polarity) (core : Finset (Point n)) :
    Decidable (Fresh frame colour core) :=
  inferInstanceAs (Decidable (∀ previous ∈ frame.positionHistory,
    ¬ ∀ point ∈ core, TwoEye.History.signatureCell previous.board point = some colour))

theorem of_virgin {n : Nat} {frame : Frame n} {colour : Polarity}
    {core seen : Finset (Point n)} {point : Point n}
    (tracked : VirginHistory.Tracked frame colour seen) (member : point ∈ core)
    (virgin : point ∉ seen) : Fresh frame colour core := by
  intro previous old occupied
  exact virgin (tracked.2 previous old point (occupied point member))

theorem no_repetition {n : Nat} {frame : Frame n} {colour turn : Polarity}
    {core : Finset (Point n)} {board : Board n} (fresh : Fresh frame colour core)
    (occupied : ∀ point ∈ core, board point = some colour) :
    ¬ violatesRepetition .positionalSuperko frame.positionHistory ⟨boardSignature board, turn⟩ := by
  rintro ⟨previous, member, same⟩
  apply fresh previous member
  intro point inside
  rw [same, TwoEye.History.signatureCell_boardSignature]
  exact occupied point inside

theorem step {n : Nat} {frame target : Frame n} {colour : Polarity}
    {core : Finset (Point n)} {move : Move n} (fresh : Fresh frame colour core)
    (native : LegalStep (Law.positionalSuperko 0) frame move target)
    (missing : ∃ point ∈ core, target.visible.board point ≠ some colour) :
    Fresh target colour core := by
  intro previous member occupied
  rw [nativeStep_positionHistory_eq native] at member
  rcases List.mem_append.mp member with old | latest
  · exact fresh previous old occupied
  · have same := List.mem_singleton.mp latest
    subst previous
    obtain ⟨point, inside, absent⟩ := missing
    apply absent
    simpa only [VisiblePosition.situation, TwoEye.History.signatureCell_boardSignature]
      using occupied point inside

def reply {n : Nat} (frame : Frame n) (colour : Polarity) (core : Finset (Point n))
    (fresh : Fresh frame colour core) (point : Point n)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (empty : frame.visible.board point = none)
    (occupied : ∀ stone ∈ core, boardAfterPlay frame.visible.board colour point stone = some colour)
    (legal : stoneHasLiberty (boardAfterPlay frame.visible.board colour point) point) : ScoringReply frame where
  move := .play point
  target := frame.advance {
    board := boardAfterPlay frame.visible.board colour point
    toMove := colour.other
    consecutivePasses := 0
    status := .playing
  }
  notResign := by simp
  step := by
    have unseen := no_repetition (turn := colour.other) fresh occupied
    simp only [LegalStep, nativeStep?, stepVisible?, playVisible?, playing, owned,
      if_pos empty, if_pos legal, Law.positionalSuperko, if_neg unseen, Option.map_some]

end SaturationMonoid.ProcessGame.Go.CriticalKomi.CoreHistory
