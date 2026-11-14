import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VirginHistory
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StrategyCertificate
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.BufferedReplay

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CoalitionBirth

structure Plan {n : Nat} (board : Board n) (colour : Polarity) where
  point : Point n
  empty : board point = none
  detected : EyeCoalition.Detected (Board.set board point (some colour)) colour
  participates : point ∈ detected.geometry.core

/-- Only stones used by this completion must survive the opponent's next
event.  Other own groups may be captured and need no reserve. -/
def SavedCore {n : Nat} {board : Board n} {colour : Polarity} (plan : Plan board colour) : Prop :=
  ∀ stone ∈ plan.detected.geometry.core, stone ≠ plan.point →
    2 ≤ (LibertyReserve.liberties board stone).card

instance {n : Nat} {board : Board n} {colour : Polarity} (plan : Plan board colour) :
    Decidable (SavedCore plan) :=
  inferInstanceAs (Decidable (∀ stone ∈ plan.detected.geometry.core, stone ≠ plan.point →
    2 ≤ (LibertyReserve.liberties board stone).card))

def retained {n : Nat} (frame : Frame n) (colour : Polarity) : Finset (Point n) :=
  RegionAction.stones frame.visible.board colour ∪ Finset.univ.filter (fun point =>
    frame.positionHistory.any (fun previous =>
      decide (TwoEye.History.signatureCell previous.board point = some colour)) = true)

theorem retained_tracked {n : Nat} (frame : Frame n) (colour : Polarity) :
    VirginHistory.Tracked frame colour (retained frame colour) := by
  refine ⟨Finset.subset_union_left, ?_⟩
  intro previous member point occupied
  apply Finset.mem_union_right
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    List.any_eq_true.mpr ⟨previous, member, decide_eq_true occupied⟩⟩

theorem pure_to_actual {n : Nat} {board : Board n} {colour : Polarity} {point : Point n}
    {g : EyeCoalition.Geometry n}
    (holds : EyeCoalition.Holds g colour (Board.set board point (some colour))) :
    EyeCoalition.Holds g colour (boardAfterPlay board colour point) := by
  refine ⟨fun _stone member => TwoEye.Growth.own_placed_survives (holds.1 _ member), ?_⟩
  intro eye member
  unfold boardAfterPlay
  split
  · rfl
  · exact holds.2 eye member

private theorem not_completion {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) {eye : Point n} (member : eye ∈ plan.detected.geometry.eyes) :
    eye ≠ plan.point := by
  intro same
  have empty := plan.detected.holds.2 eye member
  rw [same, Board.set_self] at empty
  cases empty

theorem empty_after_other {n : Nat} {board : Board n} {colour : Polarity}
    {played point : Point n} (empty : board point = none) (different : point ≠ played) :
    boardAfterPlay board colour played point = none := by
  unfold boardAfterPlay
  split
  · rfl
  · rw [Board.set_other _ _ different]
    exact empty

theorem saved_after_opponent {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) (saved : SavedCore plan) {played : Point n}
    (empty : board played = none) {stone : Point n}
    (member : stone ∈ plan.detected.geometry.core) (different : stone ≠ plan.point) :
    boardAfterPlay board colour.other played stone = some colour := by
  have original := plan.detected.holds.1 stone member
  rw [Board.set_other _ _ different] at original
  exact LibertyReserve.seed_survives_of_two original (saved stone member different) empty

theorem no_liberty_surrounded {n : Nat} {board : Board n} {colour : Polarity}
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

/-- The opponent's real capture is retained.  The completion protects its
needed core and removes an actual eye invader; unrelated captured stones stay gone. -/
theorem finish_after_placement {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) (saved : SavedCore plan) {played : Point n}
    (empty : board played = none) (avoided : played ≠ plan.point)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    EyeCoalition.Holds plan.detected.geometry colour
      (boardAfterPlay (boardAfterPlay board colour.other played) colour plan.point) := by
  let intermediate := boardAfterPlay board colour.other played
  have placedCore : ∀ stone ∈ plan.detected.geometry.core,
      Board.set intermediate plan.point (some colour) stone = some colour := by
    intro stone member
    by_cases same : stone = plan.point
    · subst stone
      exact Board.set_self _ _ _
    · rw [Board.set_other _ _ same]
      exact saved_after_opponent plan saved empty member same
  refine ⟨fun _stone member => TwoEye.Growth.own_placed_survives (placedCore _ member), ?_⟩
  intro eye member
  have notPoint := not_completion plan member
  have oldEmpty : board eye = none := by
    have raw := plan.detected.holds.2 eye member
    rw [Board.set_other _ _ notPoint] at raw
    exact raw
  by_cases invaded : eye = played
  · subst eye
    have opponentAt : intermediate played = some colour.other := TwoEye.Growth.placed_survives _ _ _
    have completionAdjacent : plan.point ∈ adjacentPoints played := by
      by_contra absent
      apply no_liberty_surrounded opponentAt _ legal
      intro stone adjacent
      have different : stone ≠ plan.point := by intro same; exact absent (same ▸ adjacent)
      simpa only [Polarity.other_other] using saved_after_opponent plan saved empty
        (plan.detected.geometry.boundary played member adjacent) different
    have placedOpponent : Board.set intermediate plan.point (some colour) played = some colour.other := by
      rw [Board.set_other _ _ avoided]
      exact opponentAt
    have noLiberty : ¬ stoneHasLiberty (Board.set intermediate plan.point (some colour)) played :=
      no_liberty_surrounded placedOpponent (fun stone adjacent => by
        simpa only [Polarity.other_other] using placedCore stone
          (plan.detected.geometry.boundary played member adjacent))
    have captured : played ∈ capturedStonesAfterPlay intermediate colour plan.point := by
      unfold capturedStonesAfterPlay
      apply Finset.mem_biUnion.mpr
      refine ⟨played, mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
        (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp completionAdjacent)), ?_⟩
      rw [if_pos ⟨placedOpponent, noLiberty⟩]
      exact occupied_point_mem_groupAt placedOpponent
    exact boardAfterPlay_eq_none_of_mem_captured captured
  · exact empty_after_other (empty_after_other oldEmpty invaded) notPoint

theorem play_data {n : Nat} {frame target : Frame n} {played : Point n}
    (step : LegalStep (Law.positionalSuperko 0) frame (.play played) target) :
    frame.visible.board played = none ∧
      stoneHasLiberty (boardAfterPlay frame.visible.board frame.visible.toMove played) played ∧
      target.visible.board = boardAfterPlay frame.visible.board frame.visible.toMove played ∧
      target.visible.toMove = frame.visible.toMove.other := by
  have generated := nativeStep_visible_eq step
  simp only [stepVisible?, playVisible?] at generated
  split at generated
  · simp at generated
  · split at generated
    · rename_i empty
      split at generated
      · rename_i legal
        split at generated
        · simp at generated
        · have same := Option.some.inj generated
          refine ⟨empty, legal, ?_, ?_⟩ <;> rw [← same]
      · simp at generated
    · simp at generated

theorem pass_turn {n : Nat} {frame target : Frame n}
    (step : LegalStep (Law.positionalSuperko 0) frame .pass target) :
    target.visible.toMove = frame.visible.toMove.other := by
  have generated := nativeStep_visible_eq step
  simp only [stepVisible?, passVisible?] at generated
  split at generated
  · simp at generated
  · simp only [Law.positionalSuperko, reduceCtorEq, false_and, ↓reduceIte] at generated
    exact (congrArg VisiblePosition.toMove (Option.some.inj generated)).symm

theorem afterOpponent_ready {n : Nat} {frame target : Frame n} {colour : Polarity} {move : Move n}
    (plan : Plan frame.visible.board colour) (saved : SavedCore plan)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (avoided : move ≠ .play plan.point) :
    target.visible.status = .playing ∧ target.visible.toMove = colour ∧
      target.visible.board plan.point = none ∧ EyeCoalition.Holds plan.detected.geometry colour
        (boardAfterPlay target.visible.board colour plan.point) := by
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass =>
      have facts := pass_step_facts step
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [passes, Nat.zero_add, show ¬ 2 ≤ (1 : Nat) from by omega, ↓reduceIte]
          using facts.2.2.2
      · rw [pass_turn step, opponent, Polarity.other_other]
      · rw [facts.2.1]; exact plan.empty
      · rw [facts.2.1]; exact pure_to_actual plan.detected.holds
  | play played =>
      have facts := play_data step
      have different : played ≠ plan.point := by intro same; exact avoided (congrArg Move.play same)
      refine ⟨(play_step_facts step).2.1, ?_, ?_, ?_⟩
      · rw [facts.2.2.2, opponent, Polarity.other_other]
      · rw [facts.2.2.1, opponent]
        exact empty_after_other plan.empty (Ne.symm different)
      · rw [facts.2.2.1, opponent]
        rw [opponent] at facts
        exact finish_after_placement plan saved facts.1 different facts.2.1

def afterOpponent {n : Nat} {frame target : Frame n} {colour : Polarity} {move : Move n}
    (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (plan : Plan frame.visible.board colour) (saved : SavedCore plan) (virgin : plan.point ∉ seen)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (avoided : move ≠ .play plan.point) (threshold : Int)
    (accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.detected.geometry colour) = true) :
    Certificate colour threshold target :=
  let material := BufferedReplay.restore (BufferedReplay.capture target)
  have same : material = target := BufferedReplay.restore_capture target
  have native : LegalStep (Law.positionalSuperko 0) frame move material := by rw [same]; exact step
  let ready := afterOpponent_ready plan saved opponent passes scoring native avoided
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
    .choose ready.2.1 response (.eyeCoalition ⟨plan.detected.geometry, ready.2.2.2⟩ (.inl rfl) accepted)
  same ▸ certificate

def miaiCertificate {n : Nat} {frame : Frame n} {colour : Polarity}
    (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (left right : Plan frame.visible.board colour) (distinct : left.point ≠ right.point)
    (savedLeft : SavedCore left) (savedRight : SavedCore right)
    (virginLeft : left.point ∉ seen) (virginRight : right.point ∉ seen)
    (playing : frame.visible.status = .playing) (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) (threshold : Int)
    (leftAccepted : acceptsMargin colour threshold (EyeCoalition.bound left.detected.geometry colour) = true)
    (rightAccepted : acceptsMargin colour threshold (EyeCoalition.bound right.detected.geometry colour) = true) :
    Certificate colour threshold frame :=
  -- Untaken continuations keep their native enumeration deferred; every read shares it.
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
    (accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.detected.geometry colour) = true) :
    Certificate colour threshold frame :=
  let born := pure_to_actual plan.detected.holds
  have legal : stoneHasLiberty (boardAfterPlay frame.visible.board colour plan.point) plan.point := by
    have reserve := EyeCoalition.reserve born plan.participates
    obtain ⟨liberty, member⟩ := Finset.card_pos.mp
      (show 0 < (LibertyReserve.liberties (boardAfterPlay frame.visible.board colour plan.point)
        plan.point).card from by omega)
    obtain ⟨⟨stone, groupMember, adjacent⟩, empty⟩ := LibertyReserve.mem_liberties.mp member
    exact ⟨stone, groupMember, liberty, adjacent, empty⟩
  let response := VirginHistory.reply frame colour seen tracked plan.point virgin playing owned plan.empty legal
  .choose owned response (.eyeCoalition ⟨plan.detected.geometry, born⟩ (.inl rfl) accepted)

structure Candidate {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) where
  plan : Plan frame.visible.board colour
  virgin : plan.point ∉ seen
  accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.detected.geometry colour) = true

structure SavedCandidate {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) extends Candidate frame colour threshold seen where
  saved : SavedCore plan

def candidate? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) (point : Point n) : Option (Candidate frame colour threshold seen) :=
  if virgin : point ∉ seen then
    if empty : frame.visible.board point = none then
      (EyeCoalition.recognize? (Board.set frame.visible.board point (some colour)) colour).bind (fun detected =>
        if participates : point ∈ detected.geometry.core then
          if accepted : acceptsMargin colour threshold (EyeCoalition.bound detected.geometry colour) = true then
            some ⟨⟨point, empty, detected, participates⟩, virgin, accepted⟩
          else none
        else none)
    else none
  else none

def scanMiai? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (playing : frame.visible.status = .playing) (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) :
    List (Point n) → Option (SavedCandidate frame colour threshold seen) →
      Option (Certificate colour threshold frame)
  | [], _ => none
  | point :: rest, retainedFirst =>
      match candidate? frame colour threshold seen point with
      | none => scanMiai? frame colour threshold seen tracked playing opponent passes rest retainedFirst
      | some candidate =>
          if saved : SavedCore candidate.plan then
            match retainedFirst with
            | none => scanMiai? frame colour threshold seen tracked playing opponent passes rest
                (some ⟨candidate, saved⟩)
            | some first =>
                if distinct : first.plan.point ≠ candidate.plan.point then
                  some (miaiCertificate seen tracked first.plan candidate.plan distinct first.saved saved
                    first.virgin candidate.virgin playing opponent passes threshold first.accepted candidate.accepted)
                else scanMiai? frame colour threshold seen tracked playing opponent passes rest retainedFirst
          else scanMiai? frame colour threshold seen tracked playing opponent passes rest retainedFirst

/-- A one-point completion can add only that point and its physical neighbours
to the current own closed neighbourhood.  This source read avoids impossible scans. -/
def possibleArea {n : Nat} (board : Board n) (colour : Polarity) : Nat :=
  let occupied := RegionAction.stones board colour
  let old := occupied ∪ occupied.biUnion adjacentPoints
  let addition := (Finset.univ : Finset (Point n)).sup (fun point => 1 + (adjacentPoints point).card)
  min (n * n) (old.card + addition)

theorem plan_area_le_possible {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) : (EyeCoalition.points plan.detected.geometry).card ≤ possibleArea board colour := by
  let occupied := RegionAction.stones board colour
  let old := occupied ∪ occupied.biUnion adjacentPoints
  have core : ∀ stone ∈ plan.detected.geometry.core, stone ≠ plan.point → stone ∈ occupied := by
    intro stone member different
    have value := plan.detected.holds.1 stone member
    rw [Board.set_other _ _ different] at value
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, value⟩
  have included : EyeCoalition.points plan.detected.geometry ⊆ old ∪ insert plan.point (adjacentPoints plan.point) := by
    intro point member
    rcases Finset.mem_union.mp member with stone | eye
    · by_cases same : point = plan.point
      · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl same))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (core point stone same))
    · obtain ⟨stone, adjacent⟩ := plan.detected.geometry.neighbours point eye
      have reversed := mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
        (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent))
      by_cases same : stone = plan.point
      · subst stone
        exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr reversed))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨stone, core stone (plan.detected.geometry.boundary point eye adjacent) same, reversed⟩))
  have unionBound := (Finset.card_le_card included).trans (Finset.card_union_le _ _)
  have inserted := Finset.card_insert_le plan.point (adjacentPoints plan.point)
  have addition : 1 + (adjacentPoints plan.point).card ≤
      (Finset.univ : Finset (Point n)).sup (fun point => 1 + (adjacentPoints point).card) :=
    Finset.le_sup (f := fun point : Point n => 1 + (adjacentPoints point).card)
      (Finset.mem_univ plan.point)
  have whole := Finset.card_le_card (Finset.subset_univ (EyeCoalition.points plan.detected.geometry))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at whole
  change _ ≤ min (n * n) (old.card + _)
  exact Nat.le_min.mpr ⟨whole, by omega⟩

def possibleBound {n : Nat} (board : Board n) (colour : Polarity) : Int :=
  let area := possibleArea board colour
  match colour with
  | .positive => 2 * (area : Int) - ((n * n : Nat) : Int)
  | .negative => ((n * n : Nat) : Int) - 2 * (area : Int)

theorem plan_accepted_possible {n : Nat} {board : Board n} {colour : Polarity}
    (plan : Plan board colour) (threshold : Int)
    (accepted : acceptsMargin colour threshold (EyeCoalition.bound plan.detected.geometry colour) = true) :
    acceptsMargin colour threshold (possibleBound board colour) = true := by
  have area := plan_area_le_possible plan
  cases colour with
  | positive =>
      have bound : threshold ≤ 2 * ((EyeCoalition.points plan.detected.geometry).card : Int) -
          ((n * n : Nat) : Int) := of_decide_eq_true accepted
      apply decide_eq_true
      change threshold ≤ 2 * (possibleArea board .positive : Int) - ((n * n : Nat) : Int)
      omega
  | negative =>
      have bound : ((n * n : Nat) : Int) -
          2 * ((EyeCoalition.points plan.detected.geometry).card : Int) ≤ threshold := of_decide_eq_true accepted
      apply decide_eq_true
      change ((n * n : Nat) : Int) - 2 * (possibleArea board .negative : Int) ≤ threshold
      omega

def recognize? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int) :
    Option (Certificate colour threshold frame) :=
  if playing : frame.visible.status = .playing then
    if acceptsMargin colour threshold (possibleBound frame.visible.board colour) then
      let seen := retained frame colour
      have tracked := retained_tracked frame colour
      if owned : frame.visible.toMove = colour then
        (allPoints n).findSome? (fun point =>
          (candidate? frame colour threshold seen point).map (fun candidate =>
            ownCertificate seen tracked candidate.plan candidate.virgin playing owned threshold candidate.accepted))
      else
        have opponent : frame.visible.toMove = colour.other := by
          cases colour <;> cases turn : frame.visible.toMove <;> simp_all [Polarity.other]
        if passes : frame.visible.consecutivePasses = 0 then
          scanMiai? frame colour threshold seen tracked playing opponent passes (allPoints n) none
        else none
    else none
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.CoalitionBirth
