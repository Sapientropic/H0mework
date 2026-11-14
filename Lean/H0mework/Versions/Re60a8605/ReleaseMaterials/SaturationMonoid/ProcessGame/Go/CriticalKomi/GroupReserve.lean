import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.LibertyReserve
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionAction
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.OnePointBirth

/-! A source-wide one-tempo reserve permits several own groups.  Each group
keeps its stones through the opponent event; only the born two-eye group is
retained by the resulting future certificate. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.GroupReserve

def Reserved {n : Nat} (board : Board n) (colour : Polarity) : Prop :=
  ∀ seed, board seed = some colour → 2 ≤ (LibertyReserve.liberties board seed).card

instance {n : Nat} (board : Board n) (colour : Polarity) : Decidable (Reserved board colour) :=
  inferInstanceAs (Decidable (∀ seed, board seed = some colour →
    2 ≤ (LibertyReserve.liberties board seed).card))

theorem opponent_capture_empty {n : Nat} {board : Board n} {colour : Polarity}
    (reserved : Reserved board colour) {played : Point n} (empty : board played = none) :
    capturedStonesAfterPlay board colour.other played = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro point captured
  have occupied := capturedStonesAfterPlay_member_placed_colour captured
  rw [Polarity.other_other] at occupied
  have different : point ≠ played := by
    intro same
    subst point
    rw [Board.set_self] at occupied
    exact Polarity.other_ne colour (Option.some.inj occupied)
  rw [Board.set_other _ _ different] at occupied
  exact LibertyReserve.whole_group_survives occupied (reserved point occupied) empty
    (occupied_point_mem_groupAt occupied) captured

theorem opponent_is_placement {n : Nat} {board : Board n} {colour : Polarity}
    (reserved : Reserved board colour) {played : Point n} (empty : board played = none) :
    boardAfterPlay board colour.other played = Board.set board played (some colour.other) := by
  funext point
  simp only [boardAfterPlay, opponent_capture_empty reserved empty,
    Finset.notMem_empty, ↓reduceIte]

theorem opponent_stones {n : Nat} {board : Board n} {colour : Polarity}
    (reserved : Reserved board colour) {played : Point n} (empty : board played = none) :
    RegionAction.stones (boardAfterPlay board colour.other played) colour =
      RegionAction.stones board colour := by
  rw [opponent_is_placement reserved empty]
  ext point
  simp only [RegionAction.stones, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases same : point = played
  · subst point
    rw [Board.set_self, empty]
    simp only [Option.some.injEq, Polarity.other_ne, reduceCtorEq]
  · rw [Board.set_other _ _ same]

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

theorem opponent_stones_step {n : Nat} {frame target : Frame n} {move : Move n}
    {colour : Polarity} (reserved : Reserved frame.visible.board colour)
    (opponent : frame.visible.toMove = colour.other) (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    RegionAction.stones target.visible.board colour = RegionAction.stones frame.visible.board colour := by
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass => rw [(pass_step_facts step).2.1]
  | play played =>
      have facts := play_data step
      rw [facts.2.2.1, opponent, opponent_stones reserved facts.1]

theorem opponent_history {n : Nat} {frame target : Frame n} {move : Move n}
    {colour : Polarity} (reserved : Reserved frame.visible.board colour)
    (opponent : frame.visible.toMove = colour.other) (history : RegionAction.HistoryBound frame colour)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    RegionAction.HistoryBound target colour := by
  apply RegionAction.historyBound_step history step
  rw [opponent_stones_step reserved opponent scoring step]

/-- Raw one-placement geometry attached to one designated source group.
Other own groups remain on the same original board. -/
structure Plan {n : Nat} (board : Board n) (colour : Polarity) (seed : Point n) where
  point : Point n
  empty : board point = none
  liberty : point ∈ LibertyReserve.liberties board seed
  detected : TwoEye.Detected (Board.set board point (some colour)) colour
  atPoint : detected.geometry.seed = point

structure Miai {n : Nat} (board : Board n) (colour : Polarity) where
  seed : Point n
  occupied : board seed = some colour
  left : Plan board colour seed
  right : Plan board colour seed
  distinct : left.point ≠ right.point

private theorem pass_turn {n : Nat} {frame target : Frame n}
    (step : LegalStep (Law.positionalSuperko 0) frame .pass target) :
    target.visible.toMove = frame.visible.toMove.other := by
  have generated := nativeStep_visible_eq step
  simp only [stepVisible?, passVisible?] at generated
  split at generated
  · simp at generated
  · simp only [Law.positionalSuperko, reduceCtorEq, false_and, ↓reduceIte] at generated
    exact (congrArg VisiblePosition.toMove (Option.some.inj generated)).symm

theorem afterOpponent_ready {n : Nat} {frame target : Frame n} {move : Move n}
    {colour : Polarity} {seed : Point n} (plan : Plan frame.visible.board colour seed)
    (reserved : Reserved frame.visible.board colour)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (avoided : move ≠ .play plan.point) :
    target.visible.status = .playing ∧ target.visible.toMove = colour ∧
      target.visible.board plan.point = none ∧ TwoEye.Holds plan.detected.geometry colour
        (boardAfterPlay target.visible.board colour plan.point) := by
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass =>
      have facts := pass_step_facts step
      have playing : target.visible.status = .playing := by
        simpa only [passes, Nat.zero_add, show ¬ 2 ≤ (1 : Nat) from by omega, ↓reduceIte]
          using facts.2.2.2
      refine ⟨playing, ?_, ?_, ?_⟩
      · rw [pass_turn step, opponent, Polarity.other_other]
      · rw [facts.2.1]
        exact plan.empty
      · rw [facts.2.1]
        exact OnePointBirth.pure_to_actual plan.detected.holds
  | play played =>
      have facts := play_data step
      have different : played ≠ plan.point := by
        intro same
        exact avoided (congrArg Move.play same)
      have boardEq : target.visible.board = Board.set frame.visible.board played (some colour.other) := by
        rw [facts.2.2.1, opponent, opponent_is_placement reserved facts.1]
      have legal : stoneHasLiberty (Board.set frame.visible.board played (some colour.other)) played := by
        have legal := facts.2.1
        rw [opponent, opponent_is_placement reserved facts.1] at legal
        exact legal
      refine ⟨(play_step_facts step).2.1, ?_, ?_, ?_⟩
      · rw [facts.2.2.2, opponent, Polarity.other_other]
      · rw [boardEq, Board.set_other _ _ (Ne.symm different)]
        exact plan.empty
      · rw [boardEq]
        exact OnePointBirth.finish_after_placement plan.detected.holds facts.1 different legal

/-- The already derived local born board supplies no-suicide; the retained
whole-board count supplies the original PSK guard. -/
private def bornReply {n : Nat} {g : TwoEye.Geometry n} {colour : Polarity}
    (frame : Frame n) (point : Point n) (playing : frame.visible.status = .playing)
    (owned : frame.visible.toMove = colour) (empty : frame.visible.board point = none)
    (history : RegionAction.HistoryBound frame colour)
    (born : TwoEye.Holds g colour (boardAfterPlay frame.visible.board colour point))
    (atPoint : g.seed = point) : ScoringReply frame where
  move := .play point
  target := frame.advance {
    board := boardAfterPlay frame.visible.board colour point
    toMove := colour.other
    consecutivePasses := 0
    status := .playing
  }
  notResign := by simp
  step := by
    have legal := TwoEye.Growth.seed_has_liberty born
    rw [atPoint] at legal
    have fresh := RegionAction.growth_fresh history empty
    simp only [LegalStep, nativeStep?, stepVisible?, playVisible?, playing, owned,
      if_pos empty, if_pos legal, Law.positionalSuperko, if_neg fresh, Option.map_some]

def afterOpponent {n : Nat} {frame target : Frame n} {move : Move n}
    {colour : Polarity} {seed : Point n} (plan : Plan frame.visible.board colour seed)
    (reserved : Reserved frame.visible.board colour)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (history : RegionAction.HistoryBound frame colour)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (avoided : move ≠ .play plan.point) (threshold : Int)
    (accepted : acceptsMargin colour threshold (TwoEye.bound plan.detected.geometry colour) = true) :
    Certificate colour threshold target :=
  let ready := afterOpponent_ready plan reserved opponent passes scoring step avoided
  let reply := bornReply target plan.point ready.1 ready.2.1 ready.2.2.1
    (opponent_history reserved opponent history scoring step) ready.2.2.2 plan.atPoint
  let detected : TwoEye.Detected reply.target.visible.board colour :=
    ⟨plan.detected.geometry, ready.2.2.2⟩
  .choose ready.2.1 reply (.twoEye detected (Or.inl rfl) accepted)

/-- Native universal branching with no single-group restriction.  Both raw
plans attach to the same designated group; the other groups pay a one-tempo reserve. -/
def miaiCertificate {n : Nat} {frame : Frame n} {colour : Polarity}
    (pair : Miai frame.visible.board colour) (reserved : Reserved frame.visible.board colour)
    (playing : frame.visible.status = .playing) (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0) (history : RegionAction.HistoryBound frame colour)
    (threshold : Int)
    (leftAccepted : acceptsMargin colour threshold (TwoEye.bound pair.left.detected.geometry colour) = true)
    (rightAccepted : acceptsMargin colour threshold (TwoEye.bound pair.right.detected.geometry colour) = true) :
    Certificate colour threshold frame :=
  .all playing (by rw [opponent]; exact Polarity.other_ne colour) (fun port =>
    have native := mem_scoringExpansion_iff.mp (List.get_mem (scoringExpansion frame) port)
    if hitsLeft : ((scoringExpansion frame).get port).1 = .play pair.left.point then
      afterOpponent pair.right reserved opponent passes history native.2 native.1
        (fun hitsRight => pair.distinct (Move.play.inj (hitsLeft.symm.trans hitsRight))) threshold rightAccepted
    else
      afterOpponent pair.left reserved opponent passes history native.2 native.1
        hitsLeft threshold leftAccepted)

def ownCertificate {n : Nat} {frame : Frame n} {colour : Polarity} {seed : Point n}
    (plan : Plan frame.visible.board colour seed)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (history : RegionAction.HistoryBound frame colour) (threshold : Int)
    (accepted : acceptsMargin colour threshold (TwoEye.bound plan.detected.geometry colour) = true) :
    Certificate colour threshold frame :=
  let born := OnePointBirth.pure_to_actual plan.detected.holds
  let reply := bornReply frame plan.point playing owned plan.empty history born plan.atPoint
  .choose owned reply (.twoEye ⟨plan.detected.geometry, born⟩ (Or.inl rfl) accepted)

structure AcceptedPlan {n : Nat} (board : Board n) (colour : Polarity)
    (seed : Point n) (threshold : Int) where
  plan : Plan board colour seed
  accepted : acceptsMargin colour threshold (TwoEye.bound plan.detected.geometry colour) = true

def recognizePlan? {n : Nat} (board : Board n) (colour : Polarity)
    (seed point : Point n) (threshold : Int) :
    Option (AcceptedPlan board colour seed threshold) :=
  if empty : board point = none then
    if liberty : point ∈ LibertyReserve.liberties board seed then
      match TwoEye.recognizeSeed? (Board.set board point (some colour)) colour point with
      | none => none
      | some detected =>
          if atPoint : detected.geometry.seed = point then
            if accepted : acceptsMargin colour threshold (TwoEye.bound detected.geometry colour) = true then
              some ⟨⟨point, empty, liberty, detected, atPoint⟩, accepted⟩
            else none
          else none
    else none
  else none

def recognizeAt? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (seed : Point n) (occupied : frame.visible.board seed = some colour)
    (playing : frame.visible.status = .playing)
    (history : RegionAction.HistoryBound frame colour) :
    Option (Certificate colour threshold frame) :=
  let candidates := (allPoints n).filterMap (fun point =>
    recognizePlan? frame.visible.board colour seed point threshold)
  if owned : frame.visible.toMove = colour then
    candidates.head?.map (fun candidate =>
      ownCertificate candidate.plan playing owned history threshold candidate.accepted)
  else
    have opponent : frame.visible.toMove = colour.other := by
      cases colour <;> cases turn : frame.visible.toMove <;> simp_all [Polarity.other]
    if passes : frame.visible.consecutivePasses = 0 then
      if reserved : Reserved frame.visible.board colour then
        match candidates with
        | [] => none
        | left :: rest => rest.findSome? (fun right =>
            if distinct : left.plan.point ≠ right.plan.point then
              some (miaiCertificate ⟨seed, occupied, left.plan, right.plan, distinct⟩ reserved
                playing opponent passes history threshold left.accepted right.accepted)
            else none)
      else none
    else none

/-- Visit each actual own component once.  The shared reserve is a current
board predicate; all later choices are generated in original opponent branches. -/
def scan? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (playing : frame.visible.status = .playing) (history : RegionAction.HistoryBound frame colour) :
    List (Point n) → Finset (Point n) → Option (Certificate colour threshold frame)
  | [], _ => none
  | seed :: rest, visited =>
      if seed ∈ visited then scan? frame colour threshold playing history rest visited
      else if occupied : frame.visible.board seed = some colour then
        match recognizeAt? frame colour threshold seed occupied playing history with
        | some certificate => some certificate
        | none => scan? frame colour threshold playing history rest
            (visited ∪ groupAt frame.visible.board seed)
      else scan? frame colour threshold playing history rest visited

def recognize? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int) :
    Option (Certificate colour threshold frame) :=
  if playing : frame.visible.status = .playing then
    if acceptsMargin colour threshold (OnePointBirth.possibleBound frame.visible.board colour) then
      if history : ∀ previous ∈ frame.positionHistory,
          RegionAction.signatureCount previous.board colour ≤
            (RegionAction.stones frame.visible.board colour).card then
        scan? frame colour threshold playing history (allPoints n) ∅
      else none
    else none
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.GroupReserve
