import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CoalitionBirth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CapturingBirth

/-- Local board facts for a completion that removes occupied singleton eyes.
The opponent cannot fill the completion under the original no-suicide guard. -/
structure Plan {n : Nat} (board : Board n) (colour : Polarity) where
  point : Point n
  geometry : EyeCoalition.Geometry n
  participates : point ∈ geometry.core
  empty : board point = none
  core : ∀ stone ∈ geometry.core, stone ≠ point → board stone = some colour
  eyes : ∀ eye ∈ geometry.eyes, eye ≠ point ∧
    (board eye = none ∨ board eye = some colour.other)
  adjacent : ∀ eye ∈ geometry.eyes, board eye = some colour.other → point ∈ adjacentPoints eye
  saved : ∀ stone ∈ geometry.core, stone ≠ point →
    2 ≤ (LibertyReserve.liberties board stone).card
  forbidden : ¬ stoneHasLiberty (boardAfterPlay board colour.other point) point

theorem complete_capture {n : Nat} {board : Board n} {colour : Polarity} {point : Point n}
    (g : EyeCoalition.Geometry n)
    (core : ∀ stone ∈ g.core, stone ≠ point → board stone = some colour)
    (eyes : ∀ eye ∈ g.eyes, eye ≠ point ∧ (board eye = none ∨ board eye = some colour.other))
    (adjacent : ∀ eye ∈ g.eyes, board eye = some colour.other → point ∈ adjacentPoints eye) :
    EyeCoalition.Holds g colour (boardAfterPlay board colour point) := by
  have placedCore : ∀ stone ∈ g.core, Board.set board point (some colour) stone = some colour := by
    intro stone member
    by_cases same : stone = point
    · subst stone; exact Board.set_self _ _ _
    · rw [Board.set_other _ _ same]; exact core stone member same
  refine ⟨fun _stone member => TwoEye.Growth.own_placed_survives (placedCore _ member), ?_⟩
  intro eye member
  obtain ⟨different, vacant | occupied⟩ := eyes eye member
  · exact CoalitionBirth.empty_after_other vacant different
  · have placedOpponent : Board.set board point (some colour) eye = some colour.other := by
      rw [Board.set_other _ _ different]; exact occupied
    have noLiberty : ¬ stoneHasLiberty (Board.set board point (some colour)) eye :=
      CoalitionBirth.no_liberty_surrounded placedOpponent (fun stone touching => by
        simpa only [Polarity.other_other] using placedCore stone (g.boundary eye member touching))
    apply boardAfterPlay_eq_none_of_mem_captured
    unfold capturedStonesAfterPlay
    apply Finset.mem_biUnion.mpr
    refine ⟨eye, mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
      (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp
        (adjacent eye member occupied))), ?_⟩
    rw [if_pos ⟨placedOpponent, noLiberty⟩]
    exact occupied_point_mem_groupAt placedOpponent

theorem after_placement {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) {played : Point n} (empty : board played = none)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    EyeCoalition.Holds plan.geometry colour
      (boardAfterPlay (boardAfterPlay board colour.other played) colour plan.point) := by
  have avoided : played ≠ plan.point := by intro same; subst played; exact plan.forbidden legal
  have saved : ∀ stone ∈ plan.geometry.core, stone ≠ plan.point →
      boardAfterPlay board colour.other played stone = some colour := by
    intro stone member different
    exact LibertyReserve.seed_survives_of_two (plan.core stone member different)
      (plan.saved stone member different) empty
  apply complete_capture plan.geometry saved
  · intro eye member
    obtain ⟨different, vacant | occupied⟩ := plan.eyes eye member
    · refine ⟨different, ?_⟩
      by_cases invaded : eye = played
      · subst eye; exact Or.inr (TwoEye.Growth.placed_survives _ _ _)
      · exact Or.inl (CoalitionBirth.empty_after_other vacant invaded)
    · exact ⟨different, Or.inr (TwoEye.Growth.own_stone_survives occupied played)⟩
  · intro eye member occupied
    rcases (plan.eyes eye member).2 with vacant | old
    · have invaded : eye = played := by
        by_contra different
        rw [CoalitionBirth.empty_after_other vacant different] at occupied
        cases occupied
      subst eye
      by_contra absent
      apply CoalitionBirth.no_liberty_surrounded (TwoEye.Growth.placed_survives board colour.other played) _ legal
      intro stone touching
      have different : stone ≠ plan.point := by intro same; exact absent (same ▸ touching)
      simpa only [Polarity.other_other] using
        saved stone (plan.geometry.boundary played member touching) different
    · exact plan.adjacent eye member old

theorem afterOpponent_ready {n : Nat} {frame target : Frame n} {colour : Polarity} {move : Move n}
    (plan : Plan frame.visible.board colour)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    target.visible.status = .playing ∧ target.visible.toMove = colour ∧
      target.visible.board plan.point = none ∧ EyeCoalition.Holds plan.geometry colour
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
      · rw [facts.2.1]; exact complete_capture plan.geometry plan.core plan.eyes plan.adjacent
  | play played =>
      have facts := CoalitionBirth.play_data step
      rw [opponent] at facts
      have different : played ≠ plan.point := by intro same; subst played; exact plan.forbidden facts.2.1
      refine ⟨(play_step_facts step).2.1, ?_, ?_, ?_⟩
      · rw [facts.2.2.2, Polarity.other_other]
      · rw [facts.2.2.1]; exact CoalitionBirth.empty_after_other plan.empty (Ne.symm different)
      · rw [facts.2.2.1]; exact after_placement plan facts.1 facts.2.1

def afterOpponent {n : Nat} {frame target : Frame n} {colour : Polarity} {move : Move n}
    (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (plan : Plan frame.visible.board colour) (virgin : plan.point ∉ seen)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (threshold : Int) (accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.geometry colour) = true) :
    Certificate colour threshold target :=
  let material := BufferedReplay.restore (BufferedReplay.capture target)
  have same : material = target := BufferedReplay.restore_capture target
  have native : LegalStep (Law.positionalSuperko 0) frame move material := by rw [same]; exact step
  let ready := afterOpponent_ready plan opponent passes scoring native
  have retained : VirginHistory.Tracked material colour seen := by
    have next := VirginHistory.step tracked scoring native
    cases move <;> simpa only [VirginHistory.nextSeen, opponent, Polarity.other_ne, ↓reduceIte] using next
  have legal : stoneHasLiberty (boardAfterPlay material.visible.board colour plan.point) plan.point := by
    have reserve := EyeCoalition.reserve ready.2.2.2 plan.participates
    obtain ⟨liberty, member⟩ := Finset.card_pos.mp
      (show 0 < (LibertyReserve.liberties (boardAfterPlay material.visible.board colour plan.point)
        plan.point).card from by omega)
    obtain ⟨⟨stone, groupMember, adjacent⟩, empty⟩ := LibertyReserve.mem_liberties.mp member
    exact ⟨stone, groupMember, liberty, adjacent, empty⟩
  let response := VirginHistory.reply material colour seen retained plan.point virgin ready.1 ready.2.1 ready.2.2.1 legal
  let certificate : Certificate colour threshold material :=
    .choose ready.2.1 response (.eyeCoalition ⟨plan.geometry, ready.2.2.2⟩ (.inl rfl) accepted)
  same ▸ certificate

def certificate {n : Nat} {frame : Frame n} {colour : Polarity}
    (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (plan : Plan frame.visible.board colour) (virgin : plan.point ∉ seen)
    (playing : frame.visible.status = .playing) (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) (threshold : Int)
    (accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.geometry colour) = true) :
    Certificate colour threshold frame :=
  -- Untaken continuations keep their native enumeration deferred; every read shares it.
  let delayed : Thunk (List (Move n × Frame n)) := ⟨fun _ => scoringExpansion frame⟩
  .all playing (by rw [opponent]; exact Polarity.other_ne colour) (fun port =>
    let expansion := delayed.get
    have native := mem_scoringExpansion_iff.mp (List.get_mem expansion port)
    afterOpponent seen tracked plan virgin opponent passes native.2 native.1 threshold accepted)

def plan? {n : Nat} (board : Board n) (colour : Polarity) (point : Point n) :
    Option (Plan board colour) :=
  if empty : board point = none then
    if forbidden : ¬ stoneHasLiberty (boardAfterPlay board colour.other point) point then
      (EyeCoalition.recognize? (boardAfterPlay board colour point) colour).bind (fun detected =>
        let g := detected.geometry
        if participates : point ∈ g.core then
          if core : ∀ stone ∈ g.core, stone ≠ point → board stone = some colour then
            if eyes : ∀ eye ∈ g.eyes, eye ≠ point ∧ (board eye = none ∨ board eye = some colour.other) then
              if adjacent : ∀ eye ∈ g.eyes, board eye = some colour.other → point ∈ adjacentPoints eye then
                if saved : ∀ stone ∈ g.core, stone ≠ point → 2 ≤ (LibertyReserve.liberties board stone).card then
                  some ⟨point, g, participates, empty, core, eyes, adjacent, saved, forbidden⟩
                else none
              else none
            else none
          else none
        else none)
    else none
  else none

def recognizeAt? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (point : Point n) : Option (Certificate colour threshold frame) :=
  if playing : frame.visible.status = .playing then
    if opponent : frame.visible.toMove = colour.other then
      if passes : frame.visible.consecutivePasses = 0 then
        let seen := CoalitionBirth.retained frame colour
        if virgin : point ∉ seen then
          (plan? frame.visible.board colour point).bind (fun plan =>
            if same : plan.point = point then
              if accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.geometry colour) = true then
                some (certificate seen (CoalitionBirth.retained_tracked frame colour) plan
                  (by rw [same]; exact virgin) playing opponent passes threshold accepted)
              else none
            else none)
        else none
      else none
    else none
  else none

/-- Read only vacant neighbours of source singleton invaders whose remaining
boundary is already owned. The certificate still checks original legality. -/
def candidatePoints {n : Nat} (board : Board n) (colour : Polarity) : List (Point n) :=
  (allPoints n).filter (fun point => board point = none ∧
    ∃ eye ∈ adjacentPoints point, board eye = some colour.other ∧
      ∀ neighbour ∈ adjacentPoints eye, neighbour ≠ point → board neighbour = some colour)

/-- On the actual own turn the original rule compiler itself pays history and
legality. This includes a previously owned point when its new board is fresh. -/
def ownAt? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (point : Point n) (owned : frame.visible.toMove = colour) :
    Option (Certificate colour threshold frame) :=
  match generated : nativeStep? (Law.positionalSuperko 0) frame (.play point) with
  | none => none
  | some next =>
      let target := BufferedReplay.restore (BufferedReplay.capture next)
      have same : target = next := BufferedReplay.restore_capture next
      let reply : ScoringReply frame := ⟨.play point, target, by simp, by
        change nativeStep? (Law.positionalSuperko 0) frame (.play point) = some target
        rw [same]; exact generated⟩
      (EyeCoalition.recognize? target.visible.board colour).bind (fun detected =>
        if accepted : acceptsMargin colour threshold (EyeCoalition.bound detected.geometry colour) = true then
          some (.choose owned reply (.eyeCoalition detected
            (.inl (play_step_facts reply.step).2.1) accepted))
        else none)

def recognize? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int) :
    Option (Certificate colour threshold frame) :=
  if frame.visible.status = .playing then
    let points := candidatePoints frame.visible.board colour
    if owned : frame.visible.toMove = colour then
      points.findSome? (fun point => ownAt? frame colour threshold point owned)
    else points.findSome? (recognizeAt? frame colour threshold)
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.CapturingBirth
