import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionAction
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StrategyCertificate

/-!
One-point two-eye birth potentials are read from a pure original-board placement.
The opponent's actual play is consumed before a completing move is chosen.
No future certificate or universal survival field occurs in the source plan.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.OnePointBirth

private theorem adjacent_reverse {n : Nat} {left right : Point n}
    (adjacent : right ∈ adjacentPoints left) : left ∈ adjacentPoints right :=
  mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
    (orthogonallyAdjacent_symm
      (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent))

private theorem no_liberty_surrounded {n : Nat} {board : Board n}
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

private theorem holds_of_preserved {n : Nat} {g : TwoEye.Geometry n}
    {colour : Polarity} {before after : Board n}
    (inside : TwoEye.Holds g colour before)
    (own : ∀ point, before point = some colour → after point = some colour)
    (first : after g.eye₁ = none) (second : after g.eye₂ = none) :
    TwoEye.Holds g colour after := by
  have seedAfter := own g.seed inside.1
  refine ⟨seedAfter, ?_, first, second⟩
  intro point member
  have beforeMember : point ∈ componentAt before g.seed := by
    simpa only [groupAt, inside.1] using inside.2.1 member
  have carried := componentAt_subset_of_component_values_preserved
    (before := before) (after := after) (seed := g.seed) (by
      intro old oldMember
      have oldColour := (componentAt_member_value oldMember).trans inside.1
      exact (own old oldColour).trans seedAfter.symm) beforeMember
  simpa only [groupAt, seedAfter] using carried

private theorem empty_after_own {n : Nat} (board : Board n) (colour : Polarity)
    (played : Point n) {point : Point n}
    (empty : Board.set board played (some colour) point = none) :
    boardAfterPlay board colour played point = none := by
  unfold boardAfterPlay
  split
  · rfl
  · exact empty

/-- Capture removes only the opposing colour, so a raw pure-placement
two-eye witness survives the actual native capture operation. -/
theorem pure_to_actual {n : Nat} {g : TwoEye.Geometry n} {colour : Polarity}
    {board : Board n} {played : Point n}
    (inside : TwoEye.Holds g colour (Board.set board played (some colour))) :
    TwoEye.Holds g colour (boardAfterPlay board colour played) :=
  holds_of_preserved inside
    (fun _point occupied => TwoEye.Growth.own_placed_survives occupied)
    (empty_after_own board colour played inside.2.2.1)
    (empty_after_own board colour played inside.2.2.2)

private theorem preserved_placed {n : Nat} {board : Board n} {colour : Polarity}
    {played completion : Point n} (empty : board played = none)
    (_different : played ≠ completion) {point : Point n}
    (occupied : Board.set board completion (some colour) point = some colour) :
    Board.set (Board.set board played (some colour.other)) completion
      (some colour) point = some colour := by
  by_cases completed : point = completion
  · subst point
    exact Board.set_self _ _ _
  · rw [Board.set_other _ _ completed] at occupied ⊢
    have notPlayed : point ≠ played := by
      intro same
      rw [same, empty] at occupied
      cases occupied
    rw [Board.set_other _ _ notPlayed]
    exact occupied

private theorem potential_eye_ne_completion {n : Nat} {board : Board n}
    {colour : Polarity} {completion eye : Point n}
    (empty : Board.set board completion (some colour) eye = none) :
    eye ≠ completion := by
  intro same
  rw [same, Board.set_self] at empty
  cases empty

private theorem finish_eye {n : Nat} {g : TwoEye.Geometry n} {colour : Polarity}
    {board : Board n} {completion played eye : Point n}
    (inside : TwoEye.Holds g colour (Board.set board completion (some colour)))
    (eyeEmpty : Board.set board completion (some colour) eye = none)
    (boundary : adjacentPoints eye ⊆ g.core)
    (empty : board played = none) (different : played ≠ completion)
    (legal : stoneHasLiberty (Board.set board played (some colour.other)) played) :
    boardAfterPlay (Board.set board played (some colour.other)) colour completion eye = none := by
  have eyeNotCompletion := potential_eye_ne_completion eyeEmpty
  by_cases invaded : eye = played
  · subst played
    have completionAdjacent : completion ∈ adjacentPoints eye := by
      by_contra separated
      apply no_liberty_surrounded
        (Board.set_self board eye (some colour.other)) _ legal
      intro point adjacent
      have own := TwoEye.core_colour inside (boundary adjacent)
      have pointNotCompletion : point ≠ completion := by
        intro same
        exact separated (same ▸ adjacent)
      rw [Board.set_other _ _ pointNotCompletion] at own
      have pointNotEye : point ≠ eye := by
        intro same
        subst point
        exact not_orthogonallyAdjacent_self eye
          (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent)
      simpa only [Board.set_other _ _ pointNotEye, Polarity.other_other] using own
    have opponentAt :
        Board.set (Board.set board eye (some colour.other)) completion
          (some colour) eye = some colour.other := by
      rw [Board.set_other _ _ eyeNotCompletion, Board.set_self]
    have surrounded : ∀ point ∈ adjacentPoints eye,
        Board.set (Board.set board eye (some colour.other)) completion
          (some colour) point = some colour := by
      intro point adjacent
      exact preserved_placed empty different (TwoEye.core_colour inside (boundary adjacent))
    have noLiberty :
        ¬ stoneHasLiberty
          (Board.set (Board.set board eye (some colour.other)) completion (some colour)) eye :=
      no_liberty_surrounded opponentAt
        (fun point adjacent => by simpa only [Polarity.other_other] using surrounded point adjacent)
    have captured : eye ∈ capturedStonesAfterPlay
        (Board.set board eye (some colour.other)) colour completion := by
      unfold capturedStonesAfterPlay
      apply Finset.mem_biUnion.mpr
      refine ⟨eye, adjacent_reverse completionAdjacent, ?_⟩
      rw [if_pos ⟨opponentAt, noLiberty⟩]
      exact occupied_point_mem_groupAt opponentAt
    exact boardAfterPlay_eq_none_of_mem_captured captured
  · apply empty_after_own
    rw [Board.set_other _ _ eyeNotCompletion]
    rw [Board.set_other _ _ eyeNotCompletion] at eyeEmpty
    rw [Board.set_other _ _ invaded]
    exact eyeEmpty

/-- A legal singleton eye invasion is captured by the original completion
move.  All other opponent placements leave both potential eyes empty. -/
theorem finish_after_placement {n : Nat} {g : TwoEye.Geometry n} {colour : Polarity}
    {board : Board n} {completion played : Point n}
    (inside : TwoEye.Holds g colour (Board.set board completion (some colour)))
    (empty : board played = none) (different : played ≠ completion)
    (legal : stoneHasLiberty (Board.set board played (some colour.other)) played) :
    TwoEye.Holds g colour
      (boardAfterPlay (Board.set board played (some colour.other)) colour completion) :=
  holds_of_preserved inside
    (fun _point occupied => TwoEye.Growth.own_placed_survives
      (preserved_placed empty different occupied))
    (finish_eye inside inside.2.2.1 g.boundary₁ empty different legal)
    (finish_eye inside inside.2.2.2 g.boundary₂ empty different legal)

/-- The own-colour source footprint is one actual generated component.
Other-colour stones may exist elsewhere; the proof does not erase them. -/
structure Source {n : Nat} (board : Board n) (colour : Polarity) where
  seed : Point n
  occupied : board seed = some colour
  single : RegionAction.OneGroup board colour seed

/-- A finite raw one-placement potential, with no strategy or future field. -/
structure Plan {n : Nat} {board : Board n} {colour : Polarity}
    (source : Source board colour) where
  point : Point n
  empty : board point = none
  liberty : point ∈ LibertyReserve.liberties board source.seed
  detected : TwoEye.Detected (Board.set board point (some colour)) colour
  atPoint : detected.geometry.seed = point

def recognizeSource? {n : Nat} (board : Board n) (colour : Polarity) (seed : Point n) :
    Option (Source board colour) :=
  if occupied : board seed = some colour then
    if single : ∀ point, board point = some colour → point ∈ groupAt board seed then
      some ⟨seed, occupied, single⟩
    else none
  else none

/-- Recognition first performs the pure placement, then calls the existing
two-eye source recognizer at that very point. -/
def recognizePlan? {n : Nat} {board : Board n} {colour : Polarity}
    (source : Source board colour) (point : Point n) : Option (Plan source) :=
  if empty : board point = none then
    if liberty : point ∈ LibertyReserve.liberties board source.seed then
      match TwoEye.recognizeSeed? (Board.set board point (some colour)) colour point with
      | none => none
      | some detected =>
          if atPoint : detected.geometry.seed = point then
            some ⟨point, empty, liberty, detected, atPoint⟩
          else none
    else none
  else none

private theorem twoEye_reserve {n : Nat} {g : TwoEye.Geometry n}
    {board : Board n} {colour : Polarity} (inside : TwoEye.Holds g colour board) :
    2 ≤ (LibertyReserve.liberties board g.seed).card := by
  apply Finset.one_lt_card.mpr
  obtain ⟨firstStone, firstAdjacent⟩ := g.neighbour₁
  obtain ⟨secondStone, secondAdjacent⟩ := g.neighbour₂
  refine ⟨g.eye₁, ?_, g.eye₂, ?_, g.distinct⟩
  · exact LibertyReserve.mem_liberties.mpr
      ⟨⟨firstStone, inside.2.1 (g.boundary₁ firstAdjacent), adjacent_reverse firstAdjacent⟩,
        inside.2.2.1⟩
  · exact LibertyReserve.mem_liberties.mpr
      ⟨⟨secondStone, inside.2.1 (g.boundary₂ secondAdjacent), adjacent_reverse secondAdjacent⟩,
        inside.2.2.2⟩

private theorem play_data {n : Nat} {frame target : Frame n} {played : Point n}
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

private theorem pass_turn {n : Nat} {frame target : Frame n}
    (step : LegalStep (Law.positionalSuperko 0) frame .pass target) :
    target.visible.toMove = frame.visible.toMove.other := by
  have generated := nativeStep_visible_eq step
  simp only [stepVisible?, passVisible?] at generated
  split at generated
  · simp at generated
  · simp only [Law.positionalSuperko, reduceCtorEq, false_and, ↓reduceIte] at generated
    exact (congrArg VisiblePosition.toMove (Option.some.inj generated)).symm

/-- All data needed by the own native reply are generated from the observed
opponent step.  The potential is not assumed stable under that opponent. -/
theorem afterOpponent_ready {n : Nat} {frame target : Frame n} {move : Move n}
    {colour : Polarity} (source : Source frame.visible.board colour) (plan : Plan source)
    (reserve : 2 ≤ (LibertyReserve.liberties frame.visible.board source.seed).card)
    (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) (history : RegionAction.HistoryBound frame colour)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (avoided : move ≠ .play plan.point) :
    target.visible.status = .playing ∧ target.visible.toMove = colour ∧
      target.visible.board plan.point = none ∧ RegionAction.HistoryBound target colour ∧
      TwoEye.Holds plan.detected.geometry colour
        (boardAfterPlay target.visible.board colour plan.point) := by
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass =>
      have facts := pass_step_facts step
      have playing : target.visible.status = .playing := by
        simpa only [passes, Nat.zero_add, show ¬ 2 ≤ (1 : Nat) from by omega, ↓reduceIte]
          using facts.2.2.2
      have owned : target.visible.toMove = colour := by
        rw [pass_turn step, opponent, Polarity.other_other]
      refine ⟨playing, owned, ?_, ?_, ?_⟩
      · rw [facts.2.1]
        exact plan.empty
      · apply RegionAction.historyBound_step history step
        rw [facts.2.1]
      · rw [facts.2.1]
        exact pure_to_actual plan.detected.holds
  | play played =>
      have facts := play_data step
      have different : played ≠ plan.point := by
        intro same
        apply avoided
        rw [same]
      have noCapture := RegionAction.opponent_is_placement source.occupied source.single reserve facts.1
      have boardEq : target.visible.board = Board.set frame.visible.board played (some colour.other) := by
        rw [facts.2.2.1, opponent, noCapture]
      have legal : stoneHasLiberty (Board.set frame.visible.board played (some colour.other)) played := by
        have legal := facts.2.1
        rw [opponent, noCapture] at legal
        exact legal
      have owned : target.visible.toMove = colour := by
        rw [facts.2.2.2, opponent, Polarity.other_other]
      refine ⟨(play_step_facts step).2.1, owned, ?_, ?_, ?_⟩
      · rw [boardEq, Board.set_other _ _ (Ne.symm different)]
        exact plan.empty
      · apply RegionAction.historyBound_step history step
        rw [facts.2.2.1, opponent,
          RegionAction.opponent_stones source.occupied source.single reserve facts.1]
      · rw [boardEq]
        exact finish_after_placement plan.detected.holds facts.1 different legal

def afterOpponent {n : Nat} {frame target : Frame n} {move : Move n}
    {colour : Polarity} (source : Source frame.visible.board colour) (plan : Plan source)
    (reserve : 2 ≤ (LibertyReserve.liberties frame.visible.board source.seed).card)
    (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) (history : RegionAction.HistoryBound frame colour)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (avoided : move ≠ .play plan.point) (threshold : Int)
    (accepted : acceptsMargin colour threshold (TwoEye.bound plan.detected.geometry colour) = true) :
    Certificate colour threshold target :=
  let ready := afterOpponent_ready source plan reserve opponent passes history scoring step avoided
  have two : 2 ≤ (LibertyReserve.liberties
      (boardAfterPlay target.visible.board colour plan.point) plan.point).card := by
    have two := twoEye_reserve ready.2.2.2.2
    rw [plan.atPoint] at two
    exact two
  let reply := RegionAction.playReply target colour plan.point ready.1 ready.2.1
    ready.2.2.1 ready.2.2.2.1 two
  let detected : TwoEye.Detected reply.target.visible.board colour :=
    ⟨plan.detected.geometry, ready.2.2.2.2⟩
  .choose ready.2.1 reply (.twoEye detected (Or.inl rfl) accepted)

/-- At an actual own turn, a single raw completion supplies the native legal
move.  A preceding pass is allowed because this placement resets the pass count. -/
def ownCertificate {n : Nat} {frame : Frame n} {colour : Polarity}
    (source : Source frame.visible.board colour) (plan : Plan source)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (history : RegionAction.HistoryBound frame colour) (threshold : Int)
    (accepted : acceptsMargin colour threshold (TwoEye.bound plan.detected.geometry colour) = true) :
    Certificate colour threshold frame :=
  have inside := pure_to_actual plan.detected.holds
  have reserve : 2 ≤ (LibertyReserve.liberties
      (boardAfterPlay frame.visible.board colour plan.point) plan.point).card := by
    have two := twoEye_reserve inside
    rw [plan.atPoint] at two
    exact two
  let reply := RegionAction.playReply frame colour plan.point playing owned plan.empty history reserve
  let detected : TwoEye.Detected reply.target.visible.board colour :=
    ⟨plan.detected.geometry, inside⟩
  .choose owned reply (.twoEye detected (Or.inl rfl) accepted)

/-- Distinct completion cells in the same source supply the two-liberty
reserve needed before the opponent is observed. -/
structure Miai {n : Nat} {board : Board n} {colour : Polarity}
    (source : Source board colour) where
  left : Plan source
  right : Plan source
  distinct : left.point ≠ right.point

theorem Miai.reserve {n : Nat} {board : Board n} {colour : Polarity}
    {source : Source board colour} (pair : Miai source) :
    2 ≤ (LibertyReserve.liberties board source.seed).card :=
  Finset.one_lt_card.mpr
    ⟨pair.left.point, pair.left.liberty, pair.right.point, pair.right.liberty, pair.distinct⟩

/-- The actual opponent move selects the surviving completion cell.  The
children range over the unchanged native scoring expansion, including pass. -/
def miaiCertificate {n : Nat} {frame : Frame n} {colour : Polarity}
    (source : Source frame.visible.board colour) (pair : Miai source)
    (playing : frame.visible.status = .playing)
    (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) (history : RegionAction.HistoryBound frame colour)
    (threshold : Int)
    (leftAccepted : acceptsMargin colour threshold (TwoEye.bound pair.left.detected.geometry colour) = true)
    (rightAccepted : acceptsMargin colour threshold (TwoEye.bound pair.right.detected.geometry colour) = true) :
    Certificate colour threshold frame :=
  .all playing (by rw [opponent]; exact Polarity.other_ne colour) (fun port =>
    have native := mem_scoringExpansion_iff.mp (List.get_mem (scoringExpansion frame) port)
    if hitsLeft : ((scoringExpansion frame).get port).1 = .play pair.left.point then
      have missesRight : ((scoringExpansion frame).get port).1 ≠ .play pair.right.point := by
        intro hitsRight
        exact pair.distinct (Move.play.inj (hitsLeft.symm.trans hitsRight))
      afterOpponent source pair.right pair.reserve opponent passes history native.2 native.1
        missesRight threshold rightAccepted
    else
      afterOpponent source pair.left pair.reserve opponent passes history native.2 native.1
        hitsLeft threshold leftAccepted)

/-- Accepted candidates retain the generated raw plan and only its arithmetic
area check; they do not store a future closure or an adversary guarantee. -/
structure AcceptedPlan {n : Nat} {board : Board n} {colour : Polarity}
    (source : Source board colour) (threshold : Int) where
  plan : Plan source
  accepted : acceptsMargin colour threshold (TwoEye.bound plan.detected.geometry colour) = true

def acceptedPlan? {n : Nat} {board : Board n} {colour : Polarity}
    (source : Source board colour) (threshold : Int) (point : Point n) :
    Option (AcceptedPlan source threshold) :=
  match recognizePlan? source point with
  | none => none
  | some plan =>
      if accepted : acceptsMargin colour threshold (TwoEye.bound plan.detected.geometry colour) = true then
        some ⟨plan, accepted⟩
      else none

/-- The pure completion adds one own stone; its two recognized eyes can
therefore certify no more than the current own count plus three area points. -/
theorem plan_area_le {n : Nat} {board : Board n} {colour : Polarity}
    {source : Source board colour} (plan : Plan source) :
    plan.detected.geometry.core.card + 2 ≤ (RegionAction.stones board colour).card + 3 := by
  have included : plan.detected.geometry.core ⊆
      RegionAction.stones (boardAfterPlay board colour plan.point) colour := by
    intro point member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      TwoEye.core_colour (pure_to_actual plan.detected.holds) member⟩
  have bound := Finset.card_le_card included
  rw [RegionAction.own_stones_card plan.empty] at bound
  omega

def possibleBound {n : Nat} (board : Board n) (colour : Polarity) : Int :=
  let possibleArea : Int := ((RegionAction.stones board colour).card + 3 : Nat)
  match colour with
  | .positive => 2 * possibleArea - ((n * n : Nat) : Int)
  | .negative => ((n * n : Nat) : Int) - 2 * possibleArea

theorem plan_accepted_possible {n : Nat} {board : Board n} {colour : Polarity}
    {source : Source board colour} (plan : Plan source) (threshold : Int)
    (accepted : acceptsMargin colour threshold (TwoEye.bound plan.detected.geometry colour) = true) :
    acceptsMargin colour threshold (possibleBound board colour) = true := by
  have area := plan_area_le plan
  cases colour with
  | positive =>
      have bound : threshold ≤ 2 * ((plan.detected.geometry.core.card + 2 : Nat) : Int) -
          ((n * n : Nat) : Int) := of_decide_eq_true accepted
      apply decide_eq_true
      change threshold ≤ 2 * (((RegionAction.stones board .positive).card + 3 : Nat) : Int) -
        ((n * n : Nat) : Int)
      omega
  | negative =>
      have bound : ((n * n : Nat) : Int) -
          2 * ((plan.detected.geometry.core.card + 2 : Nat) : Int) ≤ threshold :=
        of_decide_eq_true accepted
      apply decide_eq_true
      change ((n * n : Nat) : Int) -
        2 * (((RegionAction.stones board .negative).card + 3 : Nat) : Int) ≤ threshold
      omega

def recognizeOwnAt? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seed : Point n) (playing : frame.visible.status = .playing)
    (owned : frame.visible.toMove = colour) (history : RegionAction.HistoryBound frame colour) :
    Option (Certificate colour threshold frame) :=
  match recognizeSource? frame.visible.board colour seed with
  | none => none
  | some source =>
      let liberties := LibertyReserve.liberties frame.visible.board source.seed
      ((allPoints n).filter (fun point => decide (point ∈ liberties))).findSome? (fun point =>
        (acceptedPlan? source threshold point).map (fun found =>
          ownCertificate source found.plan playing owned history threshold found.accepted))

/-- The bounded source scan computes each one-placement potential once.  Only
after two distinct cells are found is the native universal node constructed. -/
def recognizeAt? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seed : Point n) (playing : frame.visible.status = .playing)
    (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) (history : RegionAction.HistoryBound frame colour) :
    Option (Certificate colour threshold frame) :=
  match recognizeSource? frame.visible.board colour seed with
  | none => none
  | some source =>
      let liberties := LibertyReserve.liberties frame.visible.board source.seed
      let candidates := ((allPoints n).filter (fun point => decide (point ∈ liberties))).filterMap
        (acceptedPlan? source threshold)
      match candidates with
      | [] => none
      | first :: rest => rest.findSome? (fun second =>
          if distinct : first.plan.point ≠ second.plan.point then
            some (miaiCertificate source ⟨first.plan, second.plan, distinct⟩ playing opponent
              passes history threshold first.accepted second.accepted)
          else none)

/-- All premises of the birth rule are finite tests of the current original
frame.  A failed source test leaves its obligation unresolved. -/
def recognize? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int) :
    Option (Certificate colour threshold frame) :=
  if playing : frame.visible.status = .playing then
    if acceptsMargin colour threshold (possibleBound frame.visible.board colour) then
      if history : ∀ previous ∈ frame.positionHistory,
          RegionAction.signatureCount previous.board colour ≤
            (RegionAction.stones frame.visible.board colour).card then
        match (allPoints n).find? (fun point => frame.visible.board point == some colour) with
        | none => none
        | some seed =>
            if owned : frame.visible.toMove = colour then
              recognizeOwnAt? frame colour threshold seed playing owned history
            else
              have opponent : frame.visible.toMove = colour.other := by
                cases colour <;> cases turn : frame.visible.toMove <;> simp_all [Polarity.other]
              if passes : frame.visible.consecutivePasses = 0 then
                recognizeAt? frame colour threshold seed playing opponent passes history
              else none
      else none
    else none
  else none


end SaturationMonoid.ProcessGame.Go.CriticalKomi.OnePointBirth
