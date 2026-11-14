import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.ComponentCorrectness
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.RulesKernel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye

structure Geometry (n : Nat) where
  seed : Point n
  core : Finset (Point n)
  eye₁ : Point n
  eye₂ : Point n
  distinct : eye₁ ≠ eye₂
  boundary₁ : adjacentPoints eye₁ ⊆ core
  boundary₂ : adjacentPoints eye₂ ⊆ core
  neighbour₁ : (adjacentPoints eye₁).Nonempty
  neighbour₂ : (adjacentPoints eye₂).Nonempty

def Holds {n : Nat} (g : Geometry n) (colour : Polarity) (board : Board n) : Prop :=
  board g.seed = some colour ∧
    g.core ⊆ groupAt board g.seed ∧
    board g.eye₁ = none ∧ board g.eye₂ = none

instance {n : Nat} (g : Geometry n) (colour : Polarity) (board : Board n) :
    Decidable (Holds g colour board) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem core_colour {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (inside : Holds g colour board) {point : Point n} (member : point ∈ g.core) :
    board point = some colour :=
  groupAt_member_colour inside.1 (inside.2.1 member)

private theorem adjacent_reverse {n : Nat} {left right : Point n}
    (adjacent : right ∈ adjacentPoints left) : left ∈ adjacentPoints right :=
  mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
    (orthogonallyAdjacent_symm
      (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent))

theorem placed_group_has_liberty {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (inside : Holds g colour board) (played : Point n)
    (empty : board played = none) :
    stoneHasLiberty (Board.set board played (some colour.other)) g.seed := by
  have sameGroup :
      groupAt (Board.set board played (some colour.other)) g.seed =
        groupAt board g.seed :=
    groupAt_placed_opponent_eq empty (by simpa using inside.1)
  unfold stoneHasLiberty
  rw [sameGroup]
  by_cases first : g.eye₁ = played
  · obtain ⟨stone, adjacent⟩ := g.neighbour₂
    refine ⟨stone, inside.2.1 (g.boundary₂ adjacent),
      g.eye₂, adjacent_reverse adjacent, ?_⟩
    rw [Board.set_other]
    · exact inside.2.2.2
    · intro second
      exact g.distinct (first.trans second.symm)
  · obtain ⟨stone, adjacent⟩ := g.neighbour₁
    refine ⟨stone, inside.2.1 (g.boundary₁ adjacent),
      g.eye₁, adjacent_reverse adjacent, ?_⟩
    rw [Board.set_other _ _ first]
    exact inside.2.2.1

private theorem not_captured_of_placed_liberty {n : Nat} {board : Board n}
    {colour : Polarity} {played point : Point n}
    (liberty : stoneHasLiberty (Board.set board played (some colour)) point) :
    point ∉ capturedStonesAfterPlay board colour played := by
  intro captured
  unfold capturedStonesAfterPlay at captured
  simp only [Finset.mem_biUnion] at captured
  obtain ⟨neighbour, _, member⟩ := captured
  split at member
  · rename_i capturedGroup
    have sameGroup := groupAt_eq_of_mem capturedGroup.1 member
    apply capturedGroup.2
    unfold stoneHasLiberty at liberty ⊢
    rw [← sameGroup]
    exact liberty
  · simp at member

theorem seed_not_captured {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (inside : Holds g colour board) (played : Point n)
    (empty : board played = none) :
    g.seed ∉ capturedStonesAfterPlay board colour.other played :=
  not_captured_of_placed_liberty (placed_group_has_liberty inside played empty)

theorem seed_survives {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (inside : Holds g colour board) (played : Point n)
    (empty : board played = none) :
    boardAfterPlay board colour.other played g.seed = some colour := by
  rw [boardAfterPlay_eq_placed_of_not_mem_captured (seed_not_captured inside played empty)]
  rw [Board.set_other]
  · exact inside.1
  · intro equal
    have incompatible := inside.1
    rw [equal, empty] at incompatible
    cases incompatible

theorem core_not_captured {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (inside : Holds g colour board) (played : Point n)
    (empty : board played = none) {point : Point n} (member : point ∈ g.core) :
    point ∉ capturedStonesAfterPlay board colour.other played :=
  source_group_not_captured_of_seed_survives empty inside.1
    (seed_survives inside played empty) (inside.2.1 member)

theorem core_survives {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (inside : Holds g colour board) (played : Point n)
    (empty : board played = none) {point : Point n} (member : point ∈ g.core) :
    boardAfterPlay board colour.other played point = some colour := by
  rw [boardAfterPlay_eq_placed_of_not_mem_captured
    (core_not_captured inside played empty member)]
  rw [Board.set_other]
  · exact core_colour inside member
  · intro equal
    have incompatible := core_colour inside member
    rw [equal, empty] at incompatible
    cases incompatible

private theorem played_survives {n : Nat} (board : Board n) (colour : Polarity)
    (played : Point n) : boardAfterPlay board colour played played = some colour := by
  have notCaptured : played ∉ capturedStonesAfterPlay board colour played := by
    intro captured
    have opposite := capturedStonesAfterPlay_member_placed_colour captured
    rw [Board.set_self] at opposite
    exact (Polarity.other_ne colour) (Option.some.inj opposite).symm
  rw [boardAfterPlay_eq_placed_of_not_mem_captured notCaptured, Board.set_self]

private theorem no_liberty_of_surrounded {n : Nat} {board : Board n}
    {colour : Polarity} {seed : Point n} (occupied : board seed = some colour)
    (surrounded : ∀ point ∈ adjacentPoints seed, board point = some colour.other) :
    ¬ stoneHasLiberty board seed := by
  have onlySeed : ∀ point ∈ componentAt board seed, point = seed := by
    apply componentAt_minimal (board := board) (seed := seed)
      (predicate := fun point => point = seed) rfl
    intro current _ currentSeed candidate candidateAdjacent candidateValue
    subst current
    have opposite := surrounded candidate
      (by simpa only [adjacentPoints, List.mem_toFinset] using candidateAdjacent)
    rw [occupied] at candidateValue
    exact False.elim ((Polarity.other_ne colour)
      (Option.some.inj (opposite.symm.trans candidateValue)))
  rintro ⟨stone, member, liberty, adjacent, empty⟩
  have stoneSeed : stone = seed := by
    apply onlySeed stone
    simpa only [groupAt, occupied] using member
  subst stone
  rw [surrounded liberty adjacent] at empty
  cases empty

theorem legal_play_ne_eyes {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (inside : Holds g colour board) (played : Point n)
    (empty : board played = none)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    played ≠ g.eye₁ ∧ played ≠ g.eye₂ := by
  constructor
  · intro equal
    subst played
    apply no_liberty_of_surrounded (played_survives board colour.other g.eye₁) _ legal
    intro point adjacent
    simpa only [Polarity.other_other] using
      core_survives inside g.eye₁ empty (g.boundary₁ adjacent)
  · intro equal
    subst played
    apply no_liberty_of_surrounded (played_survives board colour.other g.eye₂) _ legal
    intro point adjacent
    simpa only [Polarity.other_other] using
      core_survives inside g.eye₂ empty (g.boundary₂ adjacent)

theorem opponent_preserves {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (inside : Holds g colour board) (played : Point n)
    (empty : board played = none)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    Holds g colour (boardAfterPlay board colour.other played) := by
  have seedAfter := seed_survives inside played empty
  have eyes := legal_play_ne_eyes inside played empty legal
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
    · rw [Board.set_other _ _ (Ne.symm eyes.1)]
      exact inside.2.2.1
  · unfold boardAfterPlay
    split
    · rfl
    · rw [Board.set_other _ _ (Ne.symm eyes.2)]
      exact inside.2.2.2

theorem opponent_legalStep_preserves {n : Nat} {g : Geometry n} {colour : Polarity}
    {frame target : Frame n} {move : Move n}
    (inside : Holds g colour frame.visible.board)
    (opponent : frame.visible.toMove = colour.other) (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    Holds g colour target.visible.board := by
  have visible := nativeStep_visible_eq step
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass =>
      simp only [stepVisible?, passVisible?] at visible
      split at visible
      · simp at visible
      · simp only [Law.positionalSuperko, reduceCtorEq, false_and, ↓reduceIte] at visible
        have boardEq := congrArg VisiblePosition.board (Option.some.inj visible)
        rw [← boardEq]
        exact inside
  | play played =>
      simp only [stepVisible?, playVisible?] at visible
      split at visible
      · simp at visible
      · split at visible
        · rename_i empty
          split at visible
          · rename_i legal
            split at visible
            · simp at visible
            · have boardEq := congrArg VisiblePosition.board (Option.some.inj visible)
              rw [← boardEq]
              rw [opponent] at legal ⊢
              exact opponent_preserves inside played empty legal
          · simp at visible
        · simp at visible

end SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye
