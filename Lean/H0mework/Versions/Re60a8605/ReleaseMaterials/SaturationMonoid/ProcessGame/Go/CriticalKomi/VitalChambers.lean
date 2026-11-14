import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalition
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VirginHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalChambers

-- Quantify over the source collections. Generic Fintype quantification on
-- Finset (Point n) would construct the entire board powerset.
attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def vitalRooms {n : Nat} (core : Finset (Point n)) (rooms : Finset (Finset (Point n)))
    (seed : Point n) : Finset (Finset (Point n)) :=
  rooms.filter (fun room => room ⊆ (groupAt (EyeCoalition.mask core) seed).biUnion adjacentPoints)

structure Geometry (n : Nat) where
  core : Finset (Point n)
  rooms : Finset (Finset (Point n))
  separated : ∀ left ∈ rooms, ∀ right ∈ rooms, left ≠ right → Disjoint left right
  boundary : ∀ room ∈ rooms, ∀ point ∈ room, adjacentPoints point ⊆ core ∪ room
  neighbours : ∀ room ∈ rooms, ∀ point ∈ room, (adjacentPoints point).Nonempty
  support : ∀ seed ∈ core, 2 ≤ (vitalRooms core rooms seed).card

/-- Opponent stones may enter a room. Its last empty point remains an obligation
of the same current core, rather than an assumption that the entire room stays empty. -/
def Holds {n : Nat} (g : Geometry n) (colour : Polarity) (board : Board n) : Prop :=
  (∀ point ∈ g.core, board point = some colour) ∧
  (∀ room ∈ g.rooms, ∀ point ∈ room, board point ≠ some colour) ∧
  (∀ room ∈ g.rooms, ∃ point ∈ room, board point = none)

instance {n : Nat} (g : Geometry n) (colour : Polarity) (board : Board n) :
    Decidable (Holds g colour board) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem reserve {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) {seed : Point n} (inside : seed ∈ g.core) :
    2 ≤ (LibertyReserve.liberties board seed).card := by
  have two : 1 < (vitalRooms g.core g.rooms seed).card := by
    have := g.support seed inside
    omega
  obtain ⟨left, leftVital, right, rightVital, different⟩ := Finset.one_lt_card.mp two
  obtain ⟨leftMember, leftTouch⟩ := Finset.mem_filter.mp leftVital
  obtain ⟨rightMember, rightTouch⟩ := Finset.mem_filter.mp rightVital
  obtain ⟨first, firstMember, firstEmpty⟩ := holds.2.2 left leftMember
  obtain ⟨second, secondMember, secondEmpty⟩ := holds.2.2 right rightMember
  have distinct : first ≠ second := by
    intro same
    exact (Finset.disjoint_left.mp (g.separated left leftMember right rightMember different))
      firstMember (same ▸ secondMember)
  have liberty : ∀ room, room ⊆ (groupAt (EyeCoalition.mask g.core) seed).biUnion adjacentPoints →
      ∀ point ∈ room, board point = none → point ∈ LibertyReserve.liberties board seed := by
    intro room touches point member empty
    obtain ⟨stone, component, adjacent⟩ := Finset.mem_biUnion.mp (touches member)
    exact LibertyReserve.mem_liberties.mpr
      ⟨⟨stone, EyeCoalition.mask_component_subset inside holds.1 component, adjacent⟩, empty⟩
  have included : ({first, second} : Finset (Point n)) ⊆ LibertyReserve.liberties board seed := by
    intro point member
    rcases Finset.mem_insert.mp member with same | member
    · rw [same]
      exact liberty left leftTouch first firstMember firstEmpty
    · have same : point = second := Finset.mem_singleton.mp member
      subst point
      exact liberty right rightTouch second secondMember secondEmpty
  simpa only [Finset.card_pair distinct] using Finset.card_le_card included

theorem core_survives {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) (played : Point n) (empty : board played = none)
    {point : Point n} (inside : point ∈ g.core) :
    boardAfterPlay board colour.other played point = some colour :=
  LibertyReserve.seed_survives_of_two (holds.1 point inside) (reserve holds inside) empty

theorem no_liberty_filled {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    {room : Finset (Point n)} (member : room ∈ g.rooms)
    (core : ∀ point ∈ g.core, board point = some colour)
    (filled : ∀ point ∈ room, board point = some colour.other)
    {played : Point n} (inside : played ∈ room) : ¬ stoneHasLiberty board played := by
  have occupied := filled played inside
  have contained : ∀ point ∈ componentAt board played, point ∈ room := by
    apply componentAt_minimal (predicate := fun point => point ∈ room) inside
    intro current _ currentInside candidate adjacent value
    have boundary := g.boundary room member current currentInside
      (by simpa only [adjacentPoints, List.mem_toFinset] using adjacent)
    rcases Finset.mem_union.mp boundary with inCore | inRoom
    · rw [occupied] at value
      have opposite := (core candidate inCore).symm.trans value
      exact False.elim (Polarity.other_ne colour (Option.some.inj opposite.symm))
    · exact inRoom
  rintro ⟨stone, component, liberty, adjacent, empty⟩
  have stoneInside := contained stone (by simpa only [groupAt, occupied] using component)
  rcases Finset.mem_union.mp (g.boundary room member stone stoneInside adjacent) with inCore | inRoom
  · rw [core liberty inCore] at empty
    cases empty
  · rw [filled liberty inRoom] at empty
    cases empty

private theorem empty_after_other {n : Nat} {board : Board n} {colour : Polarity}
    {point played : Point n} (empty : board point = none) (different : point ≠ played) :
    boardAfterPlay board colour played point = none := by
  unfold boardAfterPlay
  split
  · rfl
  · rw [Board.set_other _ _ different]
    exact empty

theorem opponent_preserves {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) (played : Point n) (empty : board played = none)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    Holds g colour (boardAfterPlay board colour.other played) := by
  have core := fun point member => core_survives holds played empty (point := point) member
  refine ⟨core, ?_, ?_⟩
  · intro room roomMember point pointMember occupied
    have after : point ∈ RegionAction.stones (boardAfterPlay board colour.other played) colour :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, occupied⟩
    have before := VirginHistory.opponent_stones_subset board colour played after
    exact holds.2.1 room roomMember point pointMember (Finset.mem_filter.mp before).2
  · intro room member
    by_cases spare : ∃ point ∈ room, point ≠ played ∧ board point = none
    · obtain ⟨point, inside, different, vacant⟩ := spare
      exact ⟨point, inside, empty_after_other vacant different⟩
    · obtain ⟨point, inside, vacant⟩ := holds.2.2 room member
      have same : point = played := by
        by_contra different
        exact spare ⟨point, inside, different, vacant⟩
      subst point
      have filled : ∀ point ∈ room, boardAfterPlay board colour.other played point = some colour.other := by
        intro point pointMember
        by_cases same : point = played
        · subst point
          exact TwoEye.Growth.placed_survives board colour.other played
        · have notEmpty : board point ≠ none := fun absent => spare ⟨point, pointMember, same, absent⟩
          have notOwn := holds.2.1 room member point pointMember
          have opponent : board point = some colour.other := by
            cases value : board point with
            | none => exact False.elim (notEmpty value)
            | some occupant =>
                cases colour <;> cases occupant <;> simp_all
          exact TwoEye.Growth.own_stone_survives opponent played
      exact False.elim (no_liberty_filled member core filled inside legal)

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

def eyes {n : Nat} (g : Geometry n) : Finset (Point n) :=
  (g.rooms.filter (fun room => room.card = 1)).biUnion id

theorem eye_data {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) {point : Point n} (member : point ∈ eyes g) :
    board point = none ∧ (adjacentPoints point).Nonempty ∧
      ∀ stone ∈ adjacentPoints point, board stone = some colour := by
  obtain ⟨room, selected, inside⟩ := Finset.mem_biUnion.mp member
  obtain ⟨roomMember, one⟩ := Finset.mem_filter.mp selected
  obtain ⟨only, singleton⟩ := Finset.card_eq_one.mp one
  have same : point = only := by simpa only [id, singleton, Finset.mem_singleton] using inside
  subst only
  obtain ⟨vacant, vacantMember, vacantEmpty⟩ := holds.2.2 room roomMember
  have vacantSame : vacant = point := by simpa only [singleton, Finset.mem_singleton] using vacantMember
  refine ⟨vacantSame ▸ vacantEmpty, g.neighbours room roomMember point inside, ?_⟩
  intro stone adjacent
  rcases Finset.mem_union.mp (g.boundary room roomMember point inside adjacent) with core | inRoom
  · exact holds.1 stone core
  · have same : stone = point := by simpa only [singleton, Finset.mem_singleton] using inRoom
    subst stone
    exact False.elim (not_orthogonallyAdjacent_self point
      (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent))

def points {n : Nat} (g : Geometry n) : Finset (Point n) := g.core ∪ eyes g

theorem points_area {n : Nat} {g : Geometry n} {colour : Polarity} {board : Board n}
    (holds : Holds g colour board) : (points g).card ≤ areaScore board colour := by
  apply Finset.card_le_card
  intro point member
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases Finset.mem_union.mp member with core | eye
  · exact Or.inl (holds.1 point core)
  · obtain ⟨empty, neighbours, boundary⟩ := eye_data holds eye
    exact Or.inr (TwoEye.Score.singleton_eye_owner empty boundary neighbours)

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

structure Detected {n : Nat} (board : Board n) (colour : Polarity) where
  geometry : Geometry n
  holds : Holds geometry colour board

def geometry? {n : Nat} (core : Finset (Point n)) (rooms : Finset (Finset (Point n))) :
    Option (Geometry n) :=
  if separated : ∀ left ∈ rooms, ∀ right ∈ rooms, left ≠ right → Disjoint left right then
    if boundary : ∀ room ∈ rooms, ∀ point ∈ room, adjacentPoints point ⊆ core ∪ room then
      if neighbours : ∀ room ∈ rooms, ∀ point ∈ room, (adjacentPoints point).Nonempty then
        if support : ∀ seed ∈ core, 2 ≤ (vitalRooms core rooms seed).card then
          some ⟨core, rooms, separated, boundary, neighbours, support⟩
        else none
      else none
    else none
  else none

def freeMask {n : Nat} (board : Board n) (colour : Polarity) : Board n :=
  fun point => if board point = some colour then none else some .positive

private def collectRooms {n : Nat} (board : Board n) : Nat → Finset (Point n) → Finset (Finset (Point n))
  | 0, _ => ∅
  | fuel + 1, remaining =>
      match (allPoints n).find? (fun point => decide (point ∈ remaining)) with
      | none => ∅
      | some seed =>
          let room := groupAt board seed
          insert room (collectRooms board fuel (remaining \ room))

def sourceRooms {n : Nat} (board : Board n) (colour : Polarity) : Finset (Finset (Point n)) :=
  collectRooms (freeMask board colour) (n * n)
    (Finset.univ.filter (fun point => board point ≠ some colour))

def recognizeCore? {n : Nat} (board : Board n) (colour : Polarity)
    (source : Finset (Finset (Point n))) : Nat → Finset (Point n) → Option (Detected board colour)
  | 0, _ => none
  | fuel + 1, core =>
      let rooms := source.filter (fun room =>
        (∀ point ∈ room, adjacentPoints point ⊆ core ∪ room) ∧
        (∀ point ∈ room, board point ≠ some colour) ∧ (∃ point ∈ room, board point = none) ∧
        (∃ seed ∈ core, room ⊆ (groupAt (EyeCoalition.mask core) seed).biUnion adjacentPoints))
      match geometry? core rooms with
      | some geometry =>
          if holds : Holds geometry colour board then some ⟨geometry, holds⟩ else none
      | none =>
          let next := core.filter (fun seed => 2 ≤ (vitalRooms core rooms seed).card)
          recognizeCore? board colour source fuel next

def recognize? {n : Nat} (board : Board n) (colour : Polarity) : Option (Detected board colour) :=
  let core := RegionAction.stones board colour
  recognizeCore? board colour (sourceRooms board colour) (core.card + 1) core

end SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalChambers
