import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.LibertyReserve
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeClosure
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionAction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalition

def mask {n : Nat} (core : Finset (Point n)) : Board n :=
  fun point => if point ∈ core then some .positive else none

def touching {n : Nat} (core eyes : Finset (Point n)) (seed : Point n) : Finset (Point n) :=
  eyes ∩ (groupAt (mask core) seed).biUnion adjacentPoints

/-- Different core components may use the same eyes.  Every component has
two such incidences, and every eye boundary belongs to the common core. -/
structure Geometry (n : Nat) where
  core : Finset (Point n)
  eyes : Finset (Point n)
  boundary : ∀ eye ∈ eyes, adjacentPoints eye ⊆ core
  neighbours : ∀ eye ∈ eyes, (adjacentPoints eye).Nonempty
  support : ∀ seed ∈ core, 2 ≤ (touching core eyes seed).card

def Holds {n : Nat} (g : Geometry n) (colour : Polarity) (board : Board n) : Prop :=
  (∀ point ∈ g.core, board point = some colour) ∧ ∀ eye ∈ g.eyes, board eye = none

instance {n : Nat} (g : Geometry n) (colour : Polarity) (board : Board n) :
    Decidable (Holds g colour board) :=
  inferInstanceAs (Decidable ((∀ point ∈ g.core, board point = some colour) ∧
    ∀ eye ∈ g.eyes, board eye = none))

theorem mask_component_subset {n : Nat} {core : Finset (Point n)} {colour : Polarity}
    {board : Board n} {seed : Point n} (inside : seed ∈ core)
    (occupied : ∀ point ∈ core, board point = some colour) :
    groupAt (mask core) seed ⊆ groupAt board seed := by
  have maskSeed : mask core seed = some .positive := by simp only [mask, if_pos inside]
  have seedColour := occupied seed inside
  simp only [groupAt, maskSeed, seedColour]
  apply componentAt_subset_of_component_values_preserved
  intro point member
  have value := (componentAt_member_value member).trans maskSeed
  have pointInside : point ∈ core := by
    by_contra outside
    simp only [mask, if_neg outside] at value
    cases value
  rw [occupied point pointInside, seedColour]

theorem touching_liberties {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) {seed : Point n} (inside : seed ∈ g.core) :
    touching g.core g.eyes seed ⊆ LibertyReserve.liberties board seed := by
  intro eye member
  obtain ⟨eyeMember, touchingMember⟩ := Finset.mem_inter.mp member
  obtain ⟨stone, groupMember, adjacent⟩ := Finset.mem_biUnion.mp touchingMember
  exact LibertyReserve.mem_liberties.mpr
    ⟨⟨stone, mask_component_subset inside holds.1 groupMember, adjacent⟩, holds.2 eye eyeMember⟩

theorem reserve {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) {seed : Point n} (inside : seed ∈ g.core) :
    2 ≤ (LibertyReserve.liberties board seed).card :=
  (g.support seed inside).trans (Finset.card_le_card (touching_liberties holds inside))

theorem core_survives {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) (played : Point n) (empty : board played = none)
    {point : Point n} (inside : point ∈ g.core) :
    boardAfterPlay board colour.other played point = some colour :=
  LibertyReserve.seed_survives_of_two (holds.1 point inside) (reserve holds inside) empty

private theorem no_liberty_surrounded {n : Nat} {board : Board n} {colour : Polarity}
    {seed : Point n} (occupied : board seed = some colour)
    (surrounded : ∀ point ∈ adjacentPoints seed, board point = some colour.other) :
    ¬ stoneHasLiberty board seed := by
  have singleton : ∀ point ∈ componentAt board seed, point = seed := by
    apply componentAt_minimal (board := board) (seed := seed)
      (predicate := fun point => point = seed) rfl
    intro current _ currentSeed candidate adjacent value
    subst current
    have opposite := surrounded candidate
      (by simpa only [adjacentPoints, List.mem_toFinset] using adjacent)
    rw [occupied] at value
    exact False.elim (Polarity.other_ne colour (Option.some.inj (opposite.symm.trans value)))
  rintro ⟨stone, member, liberty, adjacent, empty⟩
  have same : stone = seed := singleton stone (by simpa only [groupAt, occupied] using member)
  subst stone
  rw [surrounded liberty adjacent] at empty
  cases empty

theorem legal_not_eye {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) (played : Point n) (empty : board played = none)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    played ∉ g.eyes := by
  intro eye
  apply no_liberty_surrounded (TwoEye.Growth.placed_survives board colour.other played) _ legal
  intro stone adjacent
  simpa only [Polarity.other_other] using core_survives holds played empty (g.boundary played eye adjacent)

theorem opponent_preserves {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) (played : Point n) (empty : board played = none)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    Holds g colour (boardAfterPlay board colour.other played) := by
  refine ⟨fun _point member => core_survives holds played empty member, ?_⟩
  intro eye member
  have different : eye ≠ played := by
    intro same
    exact legal_not_eye holds played empty legal (same ▸ member)
  unfold boardAfterPlay
  split
  · rfl
  · rw [Board.set_other _ _ different]
    exact holds.2 eye member

theorem opponent_legalStep_preserves {n : Nat} {g : Geometry n} {colour : Polarity}
    {frame target : Frame n} {move : Move n} (holds : Holds g colour frame.visible.board)
    (opponent : frame.visible.toMove = colour.other) (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) : Holds g colour target.visible.board := by
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass => rw [(pass_step_facts step).2.1]; exact holds
  | play played =>
      have visible := nativeStep_visible_eq step
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
              exact opponent_preserves holds played empty legal
          · simp at visible
        · simp at visible

def points {n : Nat} (g : Geometry n) : Finset (Point n) := g.core ∪ g.eyes

theorem points_area {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) : (points g).card ≤ areaScore board colour := by
  apply Finset.card_le_card
  intro point member
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases Finset.mem_union.mp member with core | eye
  · exact Or.inl (holds.1 point core)
  · exact Or.inr (TwoEye.Score.singleton_eye_owner (holds.2 point eye)
      (fun _stone adjacent => holds.1 _ (g.boundary point eye adjacent)) (g.neighbours point eye))

def bound {n : Nat} (g : Geometry n) : Polarity → Int
  | .positive => 2 * ((points g).card : Int) - ((n * n : Nat) : Int)
  | .negative => ((n * n : Nat) : Int) - 2 * ((points g).card : Int)

def invariant {n : Nat} (g : Geometry n) (colour : Polarity) (frame : Frame n) : Bool :=
  (frame.visible.status == .playing || frame.visible.status == .terminal .twoPasses) &&
    decide (Holds g colour frame.visible.board)

theorem invariant_iff {n : Nat} (g : Geometry n) (colour : Polarity) (frame : Frame n) :
    invariant g colour frame = true ↔ ScoringStatus frame ∧ Holds g colour frame.visible.board := by
  simp [invariant, ScoringStatus]

theorem score_accepted {n : Nat} (g : Geometry n) (colour : Polarity) (board : Board n)
    (holds : Holds g colour board) : acceptsMargin colour (bound g colour) (areaMargin board) = true := by
  cases colour with
  | positive => exact decide_eq_true (TwoEye.Score.black_margin_bound board (points g).card (points_area holds))
  | negative => exact decide_eq_true (TwoEye.Score.white_margin_bound board (points g).card (points_area holds))

theorem closed {n : Nat} (g : Geometry n) (colour : Polarity) :
    ClosedUnderNativeForcing colour (bound g colour) (invariant g colour) := by
  intro frame recognized
  obtain ⟨scoring, holds⟩ := (invariant_iff g colour frame).mp recognized
  cases status : frame.visible.status with
  | terminal reason =>
      have scored : reason = .twoPasses := by
        rcases scoring with playing | scored
        · rw [status] at playing
          contradiction
        · rw [status] at scored
          exact Status.terminal.inj scored
      subst reason
      simpa only [forcingRead, status, terminalGood, beq_self_eq_true, Bool.true_and] using
        score_accepted g colour frame.visible.board holds
  | playing =>
      simp only [forcingRead, status]
      by_cases owned : frame.visible.toMove = colour
      · apply (preimage_own colour frame (invariant g colour) owned).mpr
        let reply := passReply frame status
        exact ⟨reply.move, reply.target, reply.step, reply.notResign,
          (invariant_iff g colour reply.target).mpr
            ⟨nonresigning_step_scoringStatus reply.notResign reply.step, holds⟩⟩
      · apply (preimage_opponent colour frame (invariant g colour) owned).mpr
        intro move target step permitted
        have opponent : frame.visible.toMove = colour.other := by
          cases colour <;> cases toMove : frame.visible.toMove <;> simp_all
        exact (invariant_iff g colour target).mpr
          ⟨nonresigning_step_scoringStatus permitted step,
            opponent_legalStep_preserves holds opponent permitted step⟩

def closure {n : Nat} (g : Geometry n) (colour : Polarity) :=
  compileSurvival colour (bound g colour) (invariant g colour) (closed g colour)

theorem against_every_policy {n : Nat} (g : Geometry n) (colour : Polarity) (frame : Frame n)
    (holds : Holds g colour frame.visible.board) (scoring : ScoringStatus frame)
    (opponent : ExecutablePolicy n) :
    acceptsMargin colour (bound g colour)
      (areaMargin (executePolicies (versus colour (closure g colour).policy opponent)
        frame scoring).replay.final.visible.board) = true :=
  (closure g colour).against_every_policy ((invariant_iff g colour frame).mpr ⟨scoring, holds⟩)
    scoring opponent

end SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalition
