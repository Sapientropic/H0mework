import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CoalitionBirth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirth

structure Plan {n : Nat} (board : Board n) (colour : Polarity) where
  point : Point n
  empty : board point = none
  detected : VitalChambers.Detected (Board.set board point (some colour)) colour
  participates : point ∈ detected.geometry.core

def SavedCore {n : Nat} {board : Board n} {colour : Polarity} (plan : Plan board colour) : Prop :=
  ∀ stone ∈ plan.detected.geometry.core, stone ≠ plan.point →
    2 ≤ (LibertyReserve.liberties board stone).card

instance {n : Nat} {board : Board n} {colour : Polarity} (plan : Plan board colour) :
    Decidable (SavedCore plan) :=
  inferInstanceAs (Decidable (∀ stone ∈ plan.detected.geometry.core, stone ≠ plan.point →
    2 ≤ (LibertyReserve.liberties board stone).card))

theorem pure_to_actual {n : Nat} {board : Board n} {colour : Polarity} {point : Point n}
    {g : VitalChambers.Geometry n}
    (holds : VitalChambers.Holds g colour (Board.set board point (some colour))) :
    VitalChambers.Holds g colour (boardAfterPlay board colour point) := by
  refine ⟨fun _stone member => TwoEye.Growth.own_placed_survives (holds.1 _ member), ?_, ?_⟩
  · intro room member candidate inside
    unfold boardAfterPlay
    split
    · simp
    · exact holds.2.1 room member candidate inside
  · intro room member
    obtain ⟨candidate, inside, empty⟩ := holds.2.2 room member
    refine ⟨candidate, inside, ?_⟩
    unfold boardAfterPlay
    split
    · rfl
    · exact empty

theorem not_completion {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) {room : Finset (Point n)}
    (member : room ∈ plan.detected.geometry.rooms) {point : Point n} (inside : point ∈ room) :
    point ≠ plan.point := by
  intro same
  have absent := plan.detected.holds.2.1 room member point inside
  rw [same, Board.set_self] at absent
  exact absent rfl

theorem room_not_own {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) {room : Finset (Point n)}
    (member : room ∈ plan.detected.geometry.rooms) {point : Point n} (inside : point ∈ room) :
    board point ≠ some colour := by
  have absent := plan.detected.holds.2.1 room member point inside
  rw [Board.set_other _ _ (not_completion plan member inside)] at absent
  exact absent

theorem saved_after_opponent {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) (saved : SavedCore plan) {played : Point n}
    (empty : board played = none) {stone : Point n}
    (member : stone ∈ plan.detected.geometry.core) (different : stone ≠ plan.point) :
    boardAfterPlay board colour.other played stone = some colour := by
  have original := plan.detected.holds.1 stone member
  rw [Board.set_other _ _ different] at original
  exact LibertyReserve.seed_survives_of_two original (saved stone member different) empty

/-- The last room invasion has an original liberty before the completion.
Its unchanged opponent group loses that liberty at the completion, so the
original adjacent-group capture restores a room point. -/
theorem finish_after_placement {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) (saved : SavedCore plan) {played : Point n}
    (empty : board played = none) (avoided : played ≠ plan.point)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    VitalChambers.Holds plan.detected.geometry colour
      (boardAfterPlay (boardAfterPlay board colour.other played) colour plan.point) := by
  let intermediate := boardAfterPlay board colour.other played
  have middleEmpty : intermediate plan.point = none :=
    CoalitionBirth.empty_after_other plan.empty avoided.symm
  have opponentAt : intermediate played = some colour.other := TwoEye.Growth.placed_survives _ _ _
  have placedCore : ∀ stone ∈ plan.detected.geometry.core,
      Board.set intermediate plan.point (some colour) stone = some colour := by
    intro stone member
    by_cases same : stone = plan.point
    · subst stone; exact Board.set_self _ _ _
    · rw [Board.set_other _ _ same]
      exact saved_after_opponent plan saved empty member same
  have middleNotOwn : ∀ room ∈ plan.detected.geometry.rooms, ∀ point ∈ room,
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
    by_cases spare : ∃ point ∈ room, point ≠ played ∧ board point = none
    · obtain ⟨point, inside, different, vacant⟩ := spare
      exact ⟨point, inside, CoalitionBirth.empty_after_other
        (CoalitionBirth.empty_after_other vacant different) (not_completion plan member inside)⟩
    · obtain ⟨last, inside, vacant⟩ := plan.detected.holds.2.2 room member
      rw [Board.set_other _ _ (not_completion plan member inside)] at vacant
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
      have noLiberty : ¬ stoneHasLiberty (Board.set intermediate plan.point (some colour)) played :=
        VitalChambers.no_liberty_filled member placedCore placedFilled inside
      have sameGroup := groupAt_placed_opponent_eq middleEmpty opponentAt
      obtain ⟨stone, stoneMember, liberty, adjacent, libertyEmpty⟩ := legal
      have memberPlaced : stone ∈ groupAt (Board.set intermediate plan.point (some colour)) played := by
        rw [sameGroup]; exact stoneMember
      have onlyLiberty : liberty = plan.point := by
        by_contra different
        apply noLiberty
        refine ⟨stone, memberPlaced, liberty, adjacent, ?_⟩
        rw [Board.set_other _ _ different]
        exact libertyEmpty
      subst liberty
      have playedPlaced := placedFilled played inside
      have stoneOccupied := groupAt_member_colour playedPlaced memberPlaced
      have reseeded := groupAt_eq_of_mem playedPlaced memberPlaced
      have noLibertyStone : ¬ stoneHasLiberty (Board.set intermediate plan.point (some colour)) stone := by
        simpa only [stoneHasLiberty, reseeded] using noLiberty
      have captured : played ∈ capturedStonesAfterPlay intermediate colour plan.point := by
        unfold capturedStonesAfterPlay
        apply Finset.mem_biUnion.mpr
        refine ⟨stone, mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
          (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent)), ?_⟩
        rw [if_pos ⟨stoneOccupied, noLibertyStone⟩, reseeded]
        exact occupied_point_mem_groupAt playedPlaced
      exact ⟨played, inside, boardAfterPlay_eq_none_of_mem_captured captured⟩

theorem afterOpponent_ready {n : Nat} {frame target : Frame n} {colour : Polarity} {move : Move n}
    (plan : Plan frame.visible.board colour) (saved : SavedCore plan)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (avoided : move ≠ .play plan.point) :
    target.visible.status = .playing ∧ target.visible.toMove = colour ∧
      target.visible.board plan.point = none ∧ VitalChambers.Holds plan.detected.geometry colour
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
      · rw [facts.2.1]; exact pure_to_actual plan.detected.holds
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
    (accepted : acceptsMargin colour threshold (VitalChambers.bound plan.detected.geometry colour) = true) :
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
  have born : VitalChambers.Holds plan.detected.geometry colour next.visible.board := by
    rw [nextSame]; exact ready.2.2.2
  let certificate : Certificate colour threshold material :=
    .choose ready.2.1 stored (.vitalChambers ⟨plan.detected.geometry, born⟩
      (.inl (by change next.visible.status = .playing; rw [nextSame]; rfl)) accepted)
  same ▸ certificate

def miaiCertificate {n : Nat} {frame : Frame n} {colour : Polarity}
    (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (left right : Plan frame.visible.board colour) (distinct : left.point ≠ right.point)
    (savedLeft : SavedCore left) (savedRight : SavedCore right)
    (virginLeft : left.point ∉ seen) (virginRight : right.point ∉ seen)
    (playing : frame.visible.status = .playing) (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) (threshold : Int)
    (leftAccepted : acceptsMargin colour threshold (VitalChambers.bound left.detected.geometry colour) = true)
    (rightAccepted : acceptsMargin colour threshold (VitalChambers.bound right.detected.geometry colour) = true) :
    Certificate colour threshold frame :=
  let delayed : Thunk (List (Move n × Frame n)) := ⟨fun _ => scoringExpansion frame⟩
  .all playing (by rw [opponent]; exact Polarity.other_ne colour) (fun port =>
    let expansion := delayed.get
    have native := mem_scoringExpansion_iff.mp (List.get_mem expansion port)
    if hitsLeft : (expansion.get port).1 = .play left.point then
      afterOpponent seen tracked right savedRight virginRight opponent passes native.2 native.1
        (fun hitsRight => distinct (Move.play.inj (hitsLeft.symm.trans hitsRight))) threshold rightAccepted
    else afterOpponent seen tracked left savedLeft virginLeft opponent passes native.2 native.1
      hitsLeft threshold leftAccepted)

def ownCertificate {n : Nat} {frame : Frame n} {colour : Polarity}
    (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (plan : Plan frame.visible.board colour) (virgin : plan.point ∉ seen)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (threshold : Int)
    (accepted : acceptsMargin colour threshold (VitalChambers.bound plan.detected.geometry colour) = true) :
    Certificate colour threshold frame :=
  let born := pure_to_actual plan.detected.holds
  have legal : stoneHasLiberty (boardAfterPlay frame.visible.board colour plan.point) plan.point := by
    have reserve := VitalChambers.reserve born plan.participates
    obtain ⟨liberty, member⟩ := Finset.card_pos.mp
      (show 0 < (LibertyReserve.liberties (boardAfterPlay frame.visible.board colour plan.point)
        plan.point).card from by omega)
    obtain ⟨⟨stone, groupMember, adjacent⟩, empty⟩ := LibertyReserve.mem_liberties.mp member
    exact ⟨stone, groupMember, liberty, adjacent, empty⟩
  let response := VirginHistory.reply frame colour seen tracked plan.point virgin playing owned plan.empty legal
  let next := BufferedReplay.restore (BufferedReplay.capture response.target)
  have nextSame : next = response.target := BufferedReplay.restore_capture response.target
  let stored : ScoringReply frame :=
    ⟨response.move, next, response.notResign, by rw [nextSame]; exact response.step⟩
  have nextBorn : VitalChambers.Holds plan.detected.geometry colour next.visible.board := by
    rw [nextSame]; exact born
  .choose owned stored (.vitalChambers ⟨plan.detected.geometry, nextBorn⟩
    (.inl (by change next.visible.status = .playing; rw [nextSame]; rfl)) accepted)

structure Candidate {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) where
  plan : Plan frame.visible.board colour
  virgin : plan.point ∉ seen
  accepted : acceptsMargin colour threshold (VitalChambers.bound plan.detected.geometry colour) = true

def candidate? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) (point : Point n) : Option (Candidate frame colour threshold seen) :=
  if virgin : point ∉ seen then
    if empty : frame.visible.board point = none then
      (VitalChambers.recognize? (Board.set frame.visible.board point (some colour)) colour).bind (fun detected =>
        if participates : point ∈ detected.geometry.core then
          if accepted : acceptsMargin colour threshold (VitalChambers.bound detected.geometry colour) = true then
            some ⟨⟨point, empty, detected, participates⟩, virgin, accepted⟩
          else none
        else none)
    else none
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirth
