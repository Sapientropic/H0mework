import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthCapturing

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def RoomSource {n : Nat} (board : Board n) (colour : Polarity) (point : Point n)
    (room : Finset (Point n)) : Prop :=
  (∃ vacant ∈ room, board vacant = none) ∨
    ((∀ stone ∈ room, board stone = some colour.other) ∧
      ∃ neighbour ∈ room, neighbour ∈ adjacentPoints point)

instance {n : Nat} (board : Board n) (colour : Polarity) (point : Point n)
    (room : Finset (Point n)) : Decidable (RoomSource board colour point room) := by
  unfold RoomSource
  infer_instance

structure Plan {n : Nat} (board : Board n) (colour : Polarity) where
  point : Point n
  empty : board point = none
  geometry : VitalChambers.Geometry n
  participates : point ∈ geometry.core
  core : ∀ stone ∈ geometry.core, Board.set board point (some colour) stone = some colour
  notOwn : ∀ room ∈ geometry.rooms, ∀ stone ∈ room,
    Board.set board point (some colour) stone ≠ some colour
  rooms : ∀ room ∈ geometry.rooms, RoomSource board colour point room

def SavedCore {n : Nat} {board : Board n} {colour : Polarity} (plan : Plan board colour) : Prop :=
  ∀ stone ∈ plan.geometry.core, stone ≠ plan.point →
    2 ≤ (LibertyReserve.liberties board stone).card

instance {n : Nat} {board : Board n} {colour : Polarity} (plan : Plan board colour) :
    Decidable (SavedCore plan) :=
  inferInstanceAs (Decidable (∀ stone ∈ plan.geometry.core, stone ≠ plan.point →
    2 ≤ (LibertyReserve.liberties board stone).card))

theorem not_completion {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) {room : Finset (Point n)}
    (member : room ∈ plan.geometry.rooms) {point : Point n} (inside : point ∈ room) :
    point ≠ plan.point := by
  intro same
  have absent := plan.notOwn room member point inside
  rw [same, Board.set_self] at absent
  exact absent rfl

theorem room_not_own {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) {room : Finset (Point n)}
    (member : room ∈ plan.geometry.rooms) {point : Point n} (inside : point ∈ room) :
    board point ≠ some colour := by
  have absent := plan.notOwn room member point inside
  rw [Board.set_other _ _ (not_completion plan member inside)] at absent
  exact absent

theorem full_room_capture {n : Nat} {board : Board n} {colour : Polarity} {point : Point n}
    {geometry : VitalChambers.Geometry n} {room : Finset (Point n)}
    (member : room ∈ geometry.rooms)
    (core : ∀ stone ∈ geometry.core, Board.set board point (some colour) stone = some colour)
    (filled : ∀ stone ∈ room, Board.set board point (some colour) stone = some colour.other)
    (adjacent : ∃ stone ∈ room, stone ∈ adjacentPoints point) :
    ∃ stone ∈ room, boardAfterPlay board colour point stone = none := by
  obtain ⟨stone, inside, touching⟩ := adjacent
  have occupied := filled stone inside
  have noLiberty := VitalChambers.no_liberty_filled member core filled inside
  have captured : stone ∈ capturedStonesAfterPlay board colour point := by
    unfold capturedStonesAfterPlay
    apply Finset.mem_biUnion.mpr
    refine ⟨stone, touching, ?_⟩
    rw [if_pos ⟨occupied, noLiberty⟩]
    exact occupied_point_mem_groupAt occupied
  exact ⟨stone, inside, boardAfterPlay_eq_none_of_mem_captured captured⟩

/-- The existing opponent group is unchanged by the pure own placement.
Its lost original liberty identifies the actual adjacent group captured by that placement. -/
theorem capture_of_lost_liberty {n : Nat} {board : Board n} {colour : Polarity}
    {point seed : Point n} (empty : board point = none) (occupied : board seed = some colour.other)
    (legal : stoneHasLiberty board seed)
    (lost : ¬ stoneHasLiberty (Board.set board point (some colour)) seed) :
    seed ∈ capturedStonesAfterPlay board colour point := by
  have sameGroup := groupAt_placed_opponent_eq empty occupied
  obtain ⟨stone, stoneMember, liberty, adjacent, libertyEmpty⟩ := legal
  have memberPlaced : stone ∈ groupAt (Board.set board point (some colour)) seed := by
    rw [sameGroup]; exact stoneMember
  have onlyLiberty : liberty = point := by
    by_contra different
    apply lost
    refine ⟨stone, memberPlaced, liberty, adjacent, ?_⟩
    rw [Board.set_other _ _ different]
    exact libertyEmpty
  subst liberty
  have different : seed ≠ point := by
    intro same; subst seed; rw [empty] at occupied; cases occupied
  have seedPlaced : Board.set board point (some colour) seed = some colour.other := by
    rw [Board.set_other _ _ different]; exact occupied
  have stoneOccupied := groupAt_member_colour seedPlaced memberPlaced
  have reseeded := groupAt_eq_of_mem seedPlaced memberPlaced
  have noLibertyStone : ¬ stoneHasLiberty (Board.set board point (some colour)) stone := by
    simpa only [stoneHasLiberty, reseeded] using lost
  unfold capturedStonesAfterPlay
  apply Finset.mem_biUnion.mpr
  refine ⟨stone, mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
    (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent)), ?_⟩
  rw [if_pos ⟨stoneOccupied, noLibertyStone⟩, reseeded]
  exact occupied_point_mem_groupAt seedPlaced

theorem complete_capture {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) :
    VitalChambers.Holds plan.geometry colour (boardAfterPlay board colour plan.point) := by
  refine ⟨fun _stone member => TwoEye.Growth.own_placed_survives (plan.core _ member), ?_, ?_⟩
  · intro room member point inside
    unfold boardAfterPlay
    split
    · simp
    · exact plan.notOwn room member point inside
  · intro room member
    rcases plan.rooms room member with vacant | ⟨filled, adjacent⟩
    · obtain ⟨point, inside, empty⟩ := vacant
      exact ⟨point, inside, CoalitionBirth.empty_after_other empty (not_completion plan member inside)⟩
    · apply full_room_capture member plan.core _ adjacent
      intro point inside
      rw [Board.set_other _ _ (not_completion plan member inside)]
      exact filled point inside

theorem saved_after_opponent {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) (saved : SavedCore plan) {played : Point n}
    (empty : board played = none) {stone : Point n}
    (member : stone ∈ plan.geometry.core) (different : stone ≠ plan.point) :
    boardAfterPlay board colour.other played stone = some colour := by
  have original := plan.core stone member
  rw [Board.set_other _ _ different] at original
  exact LibertyReserve.seed_survives_of_two original (saved stone member different) empty

theorem finish_after_placement {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) (saved : SavedCore plan) {played : Point n}
    (empty : board played = none) (avoided : played ≠ plan.point)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    VitalChambers.Holds plan.geometry colour
      (boardAfterPlay (boardAfterPlay board colour.other played) colour plan.point) := by
  let intermediate := boardAfterPlay board colour.other played
  have middleEmpty : intermediate plan.point = none :=
    CoalitionBirth.empty_after_other plan.empty avoided.symm
  have opponentAt : intermediate played = some colour.other := TwoEye.Growth.placed_survives _ _ _
  have placedCore : ∀ stone ∈ plan.geometry.core,
      Board.set intermediate plan.point (some colour) stone = some colour := by
    intro stone member
    by_cases same : stone = plan.point
    · subst stone; exact Board.set_self _ _ _
    · rw [Board.set_other _ _ same]
      exact saved_after_opponent plan saved empty member same
  have middleNotOwn : ∀ room ∈ plan.geometry.rooms, ∀ point ∈ room,
      intermediate point ≠ some colour := by
    intro room member point inside occupied
    have old := VirginHistory.opponent_stones_subset board colour played
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, occupied⟩)
    exact room_not_own plan member inside (Finset.mem_filter.mp old).2
  refine ⟨fun _stone member => TwoEye.Growth.own_placed_survives (placedCore _ member), ?_, ?_⟩
  · intro room member point inside
    unfold boardAfterPlay
    split
    · simp
    · rw [Board.set_other _ _ (not_completion plan member inside)]
      exact middleNotOwn room member point inside
  · intro room member
    rcases plan.rooms room member with originalEmpty | ⟨originalFilled, adjacent⟩
    · by_cases spare : ∃ point ∈ room, point ≠ played ∧ board point = none
      · obtain ⟨point, inside, different, vacant⟩ := spare
        exact ⟨point, inside, CoalitionBirth.empty_after_other
          (CoalitionBirth.empty_after_other vacant different) (not_completion plan member inside)⟩
      · obtain ⟨last, inside, vacant⟩ := originalEmpty
        have same : last = played := by
          by_contra different
          exact spare ⟨last, inside, different, vacant⟩
        subst last
        have filled : ∀ point ∈ room, intermediate point = some colour.other := by
          intro point pointMember
          by_cases same : point = played
          · subst point; exact opponentAt
          · have notEmpty : board point ≠ none := fun vacant => spare ⟨point, pointMember, same, vacant⟩
            have notOwn := room_not_own plan member pointMember
            have opponent : board point = some colour.other := by
              cases value : board point with
              | none => exact False.elim (notEmpty value)
              | some occupant => cases colour <;> cases occupant <;> simp_all
            exact TwoEye.Growth.own_stone_survives opponent played
        have placedFilled : ∀ point ∈ room,
            Board.set intermediate plan.point (some colour) point = some colour.other := by
          intro point pointMember
          rw [Board.set_other _ _ (not_completion plan member pointMember)]
          exact filled point pointMember
        have lost := VitalChambers.no_liberty_filled member placedCore placedFilled inside
        exact ⟨played, inside, boardAfterPlay_eq_none_of_mem_captured
          (capture_of_lost_liberty middleEmpty opponentAt legal lost)⟩
    · apply full_room_capture member placedCore _ adjacent
      intro point inside
      rw [Board.set_other _ _ (not_completion plan member inside)]
      exact TwoEye.Growth.own_stone_survives (originalFilled point inside) played

theorem afterOpponent_ready {n : Nat} {frame target : Frame n} {colour : Polarity} {move : Move n}
    (plan : Plan frame.visible.board colour) (saved : SavedCore plan)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (avoided : move ≠ .play plan.point) :
    target.visible.status = .playing ∧ target.visible.toMove = colour ∧
      target.visible.board plan.point = none ∧ VitalChambers.Holds plan.geometry colour
        (boardAfterPlay target.visible.board colour plan.point) := by
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass =>
      have facts := pass_step_facts step
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [passes, Nat.zero_add, show ¬ 2 ≤ (1 : Nat) from by omega, ↓reduceIte]
          using facts.2.2.2
      · rw [CoalitionBirth.pass_turn step, opponent, Polarity.other_other]
      · rw [facts.2.1]; exact plan.empty
      · rw [facts.2.1]; exact complete_capture plan
  | play played =>
      have facts := CoalitionBirth.play_data step
      have different : played ≠ plan.point := by intro same; exact avoided (congrArg Move.play same)
      refine ⟨(play_step_facts step).2.1, ?_, ?_, ?_⟩
      · rw [facts.2.2.2, opponent, Polarity.other_other]
      · rw [facts.2.2.1, opponent]
        exact CoalitionBirth.empty_after_other plan.empty (Ne.symm different)
      · rw [facts.2.2.1, opponent]
        rw [opponent] at facts
        exact finish_after_placement plan saved facts.1 different facts.2.1

def afterOpponent {n : Nat} {frame target : Frame n} {colour : Polarity} {move : Move n}
    (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (plan : Plan frame.visible.board colour) (saved : SavedCore plan) (virgin : plan.point ∉ seen)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (avoided : move ≠ .play plan.point) (threshold : Int)
    (accepted : acceptsMargin colour threshold (VitalChambers.bound plan.geometry colour) = true) :
    Certificate colour threshold target :=
  let material := BufferedReplay.restore (BufferedReplay.capture target)
  have same : material = target := BufferedReplay.restore_capture target
  have native : LegalStep (Law.positionalSuperko 0) frame move material := by rw [same]; exact step
  let ready := afterOpponent_ready plan saved opponent passes scoring native avoided
  have retained : VirginHistory.Tracked material colour seen := by
    have next := VirginHistory.step tracked scoring native
    cases move <;> simpa only [VirginHistory.nextSeen, opponent, Polarity.other_ne, ↓reduceIte] using next
  have legal : stoneHasLiberty (boardAfterPlay material.visible.board colour plan.point) plan.point := by
    have reserve := VitalChambers.reserve ready.2.2.2 plan.participates
    obtain ⟨liberty, member⟩ := Finset.card_pos.mp
      (show 0 < (LibertyReserve.liberties (boardAfterPlay material.visible.board colour plan.point)
        plan.point).card from by omega)
    obtain ⟨⟨stone, groupMember, adjacent⟩, empty⟩ := LibertyReserve.mem_liberties.mp member
    exact ⟨stone, groupMember, liberty, adjacent, empty⟩
  let response := VirginHistory.reply material colour seen retained plan.point virgin ready.1 ready.2.1 ready.2.2.1 legal
  let next := BufferedReplay.restore (BufferedReplay.capture response.target)
  have nextSame : next = response.target := BufferedReplay.restore_capture response.target
  let stored : ScoringReply material :=
    ⟨response.move, next, response.notResign, by rw [nextSame]; exact response.step⟩
  have born : VitalChambers.Holds plan.geometry colour next.visible.board := by
    rw [nextSame]; exact ready.2.2.2
  let certificate : Certificate colour threshold material :=
    .choose ready.2.1 stored (.vitalChambers ⟨plan.geometry, born⟩
      (.inl (by change next.visible.status = .playing; rw [nextSame]; rfl)) accepted)
  same ▸ certificate

def plan? {n : Nat} (board : Board n) (colour : Polarity) (point : Point n)
    (geometry : VitalChambers.Geometry n) : Option (Plan board colour) :=
  if empty : board point = none then
    if participates : point ∈ geometry.core then
      if core : ∀ stone ∈ geometry.core, Board.set board point (some colour) stone = some colour then
        if notOwn : ∀ room ∈ geometry.rooms, ∀ stone ∈ room,
            Board.set board point (some colour) stone ≠ some colour then
          if rooms : ∀ room ∈ geometry.rooms, RoomSource board colour point room then
            some ⟨point, empty, geometry, participates, core, notOwn, rooms⟩
          else none
        else none
      else none
    else none
  else none

structure Candidate {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) where
  plan : Plan frame.visible.board colour
  virgin : plan.point ∉ seen
  accepted : acceptsMargin colour threshold (VitalChambers.bound plan.geometry colour) = true

def candidate? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) (point : Point n) (geometry : VitalChambers.Geometry n) :
    Option (Candidate frame colour threshold seen) :=
  if virgin : point ∉ seen then
    (plan? frame.visible.board colour point geometry).bind (fun plan =>
      if same : plan.point = point then
        if accepted : acceptsMargin colour threshold (VitalChambers.bound plan.geometry colour) = true then
          some ⟨plan, by rw [same]; exact virgin, accepted⟩
        else none
      else none)
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthCapturing
