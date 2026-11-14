import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VirginRegionAction
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RetainedCoreHistory
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.BufferedReplay

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram

open RegionProjection RegionAction

-- These quantifiers range over supplied rows and rooms, whose elements are
-- themselves point sets; the generic finite-universe instance would enumerate 2^(n*n) sets.
attribute [local instance 2000] List.decidableBAll
attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def HistoryDominates {n : Nat} (left right : List (Finset (Point n))) : Prop :=
  ∀ old ∈ left, CoreHistory.covered right old = true

def HistoryMatches {n : Nat} (frame : Frame n) (colour : Polarity)
    (history : List (Finset (Point n))) : Prop :=
  HistoryDominates history (CoreHistory.retain colour frame.positionHistory) ∧
    HistoryDominates (CoreHistory.retain colour frame.positionHistory) history

instance {n : Nat} (frame : Frame n) (colour : Polarity) (history : List (Finset (Point n))) :
    Decidable (HistoryMatches frame colour history) :=
  inferInstanceAs (Decidable ((∀ old ∈ history, CoreHistory.covered
    (CoreHistory.retain colour frame.positionHistory) old = true) ∧
      ∀ old ∈ CoreHistory.retain colour frame.positionHistory, CoreHistory.covered history old = true))

theorem covered_mono {n : Nat} (history : List (Finset (Point n)))
    {small large : Finset (Point n)} (included : small ⊆ large)
    (covered : CoreHistory.covered history large = true) :
    CoreHistory.covered history small = true := by
  obtain ⟨old, member, contains⟩ := (CoreHistory.covered_iff history large).mp covered
  exact (CoreHistory.covered_iff history small).mpr ⟨old, member, included.trans contains⟩

theorem HistoryDominates.transfer {n : Nat} {left right : List (Finset (Point n))}
    (dominates : HistoryDominates left right) (core : Finset (Point n))
    (covered : CoreHistory.covered left core = true) : CoreHistory.covered right core = true := by
  obtain ⟨old, member, contains⟩ := (CoreHistory.covered_iff left core).mp covered
  exact covered_mono right contains (dominates old member)

theorem HistoryDominates.trans {n : Nat} {first middle last : List (Finset (Point n))}
    (earlier : HistoryDominates first middle) (later : HistoryDominates middle last) :
    HistoryDominates first last := by
  intro old member
  exact later.transfer old (earlier old member)

theorem HistoryMatches.of_equivalent {n : Nat} {frame : Frame n} {colour : Polarity}
    {first second : List (Finset (Point n))} (historyExact : HistoryMatches frame colour first)
    (forward : HistoryDominates first second) (backward : HistoryDominates second first) :
    HistoryMatches frame colour second :=
  ⟨backward.trans historyExact.1, historyExact.2.trans forward⟩

theorem historyMatches_iff {n : Nat} (frame : Frame n) (colour : Polarity)
    (history : List (Finset (Point n))) :
    HistoryMatches frame colour history ↔ ∀ core,
      CoreHistory.covered history core = CoreHistory.covered
        (CoreHistory.retain colour frame.positionHistory) core := by
  constructor
  · intro historyExact core
    apply Bool.eq_iff_iff.mpr
    exact ⟨historyExact.1.transfer core, historyExact.2.transfer core⟩
  · intro same
    constructor
    · intro old member
      rw [← same]
      exact (CoreHistory.covered_iff history old).mpr ⟨old, member, Finset.Subset.refl _⟩
    · intro old member
      rw [same]
      exact (CoreHistory.covered_iff _ old).mpr ⟨old, member, Finset.Subset.refl _⟩

theorem HistoryMatches.fresh {n : Nat} {frame : Frame n} {colour : Polarity}
    {history : List (Finset (Point n))} (historyExact : HistoryMatches frame colour history)
    (core : Finset (Point n)) (uncovered : CoreHistory.covered history core = false) :
    CoreHistory.Fresh frame colour core := by
  apply (CoreHistory.fresh_iff_retained frame colour core).mpr
  rw [← (historyMatches_iff frame colour history).mp historyExact core]
  exact uncovered

theorem covered_retain_step {n : Nat} {frame target : Frame n} {move : Move n}
    (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (colour : Polarity) (core : Finset (Point n)) :
    CoreHistory.covered (CoreHistory.retain colour target.positionHistory) core = true ↔
      core ⊆ stones target.visible.board colour ∨
        CoreHistory.covered (CoreHistory.retain colour frame.positionHistory) core = true := by
  rw [CoreHistory.covered_retain_iff, nativeStep_positionHistory_eq step]
  constructor
  · rintro ⟨previous, member, occupied⟩
    rcases List.mem_append.mp member with old | latest
    · exact .inr ((CoreHistory.covered_retain_iff colour frame.positionHistory core).mpr
        ⟨previous, old, occupied⟩)
    · have same := List.mem_singleton.mp latest
      subst previous
      apply Or.inl
      intro point inside
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [VisiblePosition.situation, TwoEye.History.signatureCell_boardSignature]
        using occupied point inside
  · rintro (inside | covered)
    · refine ⟨target.visible.situation, List.mem_append_right _ (by simp), ?_⟩
      intro point member
      simpa only [VisiblePosition.situation, TwoEye.History.signatureCell_boardSignature]
        using (Finset.mem_filter.mp (inside member)).2
    · obtain ⟨previous, member, occupied⟩ :=
        (CoreHistory.covered_retain_iff colour frame.positionHistory core).mp covered
      exact ⟨previous, List.mem_append_left _ member, occupied⟩

theorem HistoryMatches.step {n : Nat} {frame target : Frame n} {colour : Polarity}
    {history : List (Finset (Point n))} (historyExact : HistoryMatches frame colour history)
    {move : Move n} (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    HistoryMatches target colour (CoreHistory.insertFootprint (stones target.visible.board colour) history) := by
  apply (historyMatches_iff _ _ _).mpr
  intro core
  apply Bool.eq_iff_iff.mpr
  rw [CoreHistory.covered_insert_iff, covered_retain_step step,
    (historyMatches_iff frame colour history).mp historyExact core]

theorem HistoryMatches.after_subset {n : Nat} {frame target : Frame n} {colour : Polarity}
    {history : List (Finset (Point n))} (historyExact : HistoryMatches frame colour history)
    (recorded : CoreHistory.covered history (stones frame.visible.board colour) = true)
    {move : Move n} (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (included : stones target.visible.board colour ⊆ stones frame.visible.board colour) :
    HistoryMatches target colour history := by
  have already := covered_mono history included recorded
  simpa only [CoreHistory.insertFootprint, already, ↓reduceIte] using historyExact.step step

def postCore {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) : Finset (Point n) :=
  stones (boardAfterPlay (restrict region board) colour played) colour

theorem postCore_eq_original {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (confined : Confined region board colour) :
    postCore region board colour played = stones (boardAfterPlay board colour played) colour := by
  unfold postCore
  rw [own_stones, own_stones]
  congr 1
  ext stone
  simp only [stones, Finset.mem_filter, Finset.mem_univ, true_and]
  exact confined_colour region board colour confined stone

structure OwnStep {n : Nat} (region : Finset (Point n)) (frame : Frame n)
    (colour : Polarity) (history : List (Finset (Point n))) (played : Point n) where
  reply : ScoringReply frame
  move_eq : reply.move = .play played
  board_eq : restrict region reply.target.visible.board =
    boardAfterPlay (restrict region frame.visible.board) colour played
  history_matches : HistoryMatches reply.target colour
    (CoreHistory.insertFootprint (postCore region frame.visible.board colour played) history)
  confined : Confined region reply.target.visible.board colour
  interior : SupportInterior region reply.target.visible.board colour

/-- Local no-suicide and joint historical freshness generate an actual reply;
the played point may have been owned in an earlier original position. -/
def ownStep {n : Nat} (region : Finset (Point n)) (frame : Frame n)
    (colour : Polarity) (history : List (Finset (Point n)))
    (historyExact : HistoryMatches frame colour history) (played : Point n)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (inside : played ∈ region) (neighbours : adjacentPoints played ⊆ region)
    (confined : Confined region frame.visible.board colour)
    (interior : SupportInterior region frame.visible.board colour)
    (capacity : RegionSparse.Capacity region frame.visible.board colour)
    (empty : restrict region frame.visible.board played = none)
    (legal : stoneHasLiberty (boardAfterPlay (restrict region frame.visible.board) colour played) played)
    (fresh : CoreHistory.covered history (postCore region frame.visible.board colour played) = false) :
    OwnStep region frame colour history played := by
  let core := postCore region frame.visible.board colour played
  have originalEmpty := (restrict_at region frame.visible.board inside).symm.trans empty
  have coreEq := postCore_eq_original region frame.visible.board colour played confined
  have occupied : ∀ stone ∈ core, boardAfterPlay frame.visible.board colour played stone = some colour := by
    intro stone member
    change stone ∈ postCore region frame.visible.board colour played at member
    rw [coreEq] at member
    exact (Finset.mem_filter.mp member).2
  have originalLegal : stoneHasLiberty (boardAfterPlay frame.visible.board colour played) played := by
    rw [← RegionCapture.liberties_nonempty_iff] at legal ⊢
    rw [RegionLift.own_liberties_exact region frame.visible.board colour played inside neighbours
      confined interior originalEmpty capacity] at legal
    exact legal
  let raw := CoreHistory.reply frame colour core (historyExact.fresh core fresh) played
    playing owned originalEmpty occupied originalLegal
  let target := BufferedReplay.restore (BufferedReplay.capture raw.target)
  have same : target = raw.target := BufferedReplay.restore_capture raw.target
  let reply : ScoringReply frame := ⟨raw.move, target, raw.notResign, by rw [same]; exact raw.step⟩
  refine ⟨reply, rfl, ?_, ?_, ?_, ?_⟩
  · change restrict region target.visible.board = _
    rw [same]
    exact RegionSparse.own_board_exact region frame.visible.board colour played inside neighbours
      confined originalEmpty capacity
  · change HistoryMatches target colour _
    rw [same]
    have updated := historyExact.step raw.step
    change HistoryMatches raw.target colour _ at updated ⊢
    rw [coreEq]
    exact updated
  · change Confined region target.visible.board colour
    rw [same]
    exact RegionLift.own_confined region frame.visible.board colour played inside confined
  · change SupportInterior region target.visible.board colour
    rw [same]
    exact RegionLift.own_supportInterior region frame.visible.board colour played neighbours interior

theorem native_play_data {n : Nat} {frame target : Frame n} {played : Point n}
    (step : LegalStep (Law.positionalSuperko 0) frame (.play played) target) :
    frame.visible.board played = none ∧
      stoneHasLiberty (boardAfterPlay frame.visible.board frame.visible.toMove played) played ∧
      target.visible.board = boardAfterPlay frame.visible.board frame.visible.toMove played ∧
      target.visible.toMove = frame.visible.toMove.other := by
  have visible := nativeStep_visible_eq step
  simp only [stepVisible?, playVisible?, (play_step_facts step).1] at visible
  split at visible
  · rename_i empty
    split at visible
    · rename_i legal
      split at visible
      · simp at visible
      · have same := Option.some.inj visible
        exact ⟨empty, legal, (congrArg VisiblePosition.board same).symm,
          (congrArg VisiblePosition.toMove same).symm⟩
    · simp at visible
  · simp at visible

theorem native_pass_turn {n : Nat} {frame target : Frame n}
    (step : LegalStep (Law.positionalSuperko 0) frame .pass target) :
    target.visible.toMove = frame.visible.toMove.other := by
  have visible := nativeStep_visible_eq step
  simp only [stepVisible?, passVisible?, (pass_step_facts step).1, Law.positionalSuperko] at visible
  simp only [reduceCtorEq, false_and, ↓reduceIte, Option.some.injEq] at visible
  exact (congrArg VisiblePosition.toMove visible).symm

theorem opponent_stones_subset {n : Nat} {frame target : Frame n} {move : Move n} {colour : Polarity}
    (opponent : frame.visible.toMove = colour.other) (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    stones target.visible.board colour ⊆ stones frame.visible.board colour := by
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass => rw [(pass_step_facts step).2.1]
  | play point =>
      rw [(native_play_data step).2.2.1, opponent]
      exact VirginHistory.opponent_stones_subset frame.visible.board colour point

inductive WhitePort {n : Nat} (region : Finset (Point n)) where
  | play (point : {point : Point n // point ∈ region})
  | environment
  | pass
  deriving DecidableEq

def whitePort? {n : Nat} (region : Finset (Point n)) : Move n → Option (WhitePort region)
  | .play point => if inside : point ∈ region then some (.play ⟨point, inside⟩) else some .environment
  | .pass => some .pass
  | .resign => none

def WhitePort.nextBoard {n : Nat} {region : Finset (Point n)}
    (board : Board n) (colour : Polarity) : WhitePort region → Board n
  | .play point => boardAfterPlay board colour.other point.1
  | .environment | .pass => board

def WhitePort.nextPasses {n : Nat} {region : Finset (Point n)} : WhitePort region → Nat
  | .pass => 1
  | .play _ | .environment => 0

def WhitePort.Admitted {n : Nat} {region : Finset (Point n)}
    (board : Board n) (colour : Polarity) : WhitePort region → Prop
  | .play point => board point.1 = none ∧ stoneHasLiberty (boardAfterPlay board colour.other point.1) point.1
  | .environment | .pass => True

instance {n : Nat} {region : Finset (Point n)} (board : Board n) (colour : Polarity)
    (port : WhitePort region) : Decidable (port.Admitted board colour) := by
  cases port <;> unfold WhitePort.Admitted <;> infer_instance

structure WhiteStep {n : Nat} (region : Finset (Point n)) (frame target : Frame n)
    (colour : Polarity) (history : List (Finset (Point n))) (move : Move n) where
  port : WhitePort region
  port_eq : whitePort? region move = some port
  admitted : port.Admitted (restrict region frame.visible.board) colour
  board_eq : restrict region target.visible.board =
    port.nextBoard (restrict region frame.visible.board) colour
  history_matches : HistoryMatches target colour history
  confined : Confined region target.visible.board colour
  interior : SupportInterior region target.visible.board colour
  playing : target.visible.status = .playing
  owned : target.visible.toMove = colour
  passes : target.visible.consecutivePasses = port.nextPasses

/-- Every original White action maps to one admitted regional port. Outside
play and pass share the board reader but retain distinct native pass phases. -/
def whiteStep {n : Nat} (region : Finset (Point n)) {frame target : Frame n}
    (colour : Polarity) (history : List (Finset (Point n)))
    (historyExact : HistoryMatches frame colour history)
    (recorded : CoreHistory.covered history (stones frame.visible.board colour) = true)
    (confined : Confined region frame.visible.board colour)
    (interior : SupportInterior region frame.visible.board colour)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    {move : Move n} (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    WhiteStep region frame target colour history move := by
  have included := opponent_stones_subset opponent scoring step
  have retained := historyExact.after_subset recorded step included
  have nextConfined : Confined region target.visible.board colour := by
    intro point occupied
    exact confined point (Finset.mem_filter.mp (included
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, occupied⟩))).2
  have nextInterior : SupportInterior region target.visible.board colour := by
    intro point occupied
    exact interior point (Finset.mem_filter.mp (included
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, occupied⟩))).2
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass =>
      have facts := pass_step_facts step
      refine ⟨.pass, rfl, trivial, ?_, retained, nextConfined, nextInterior, ?_, ?_, ?_⟩
      · change restrict region target.visible.board = restrict region frame.visible.board
        rw [facts.2.1]
      · simpa [passes] using facts.2.2.2
      · rw [native_pass_turn step, opponent, Polarity.other_other]
      · simpa [passes, WhitePort.nextPasses] using facts.2.2.1
  | play played =>
      have facts := play_step_facts step
      have data := native_play_data step
      rw [opponent] at data
      by_cases inside : played ∈ region
      · refine ⟨.play ⟨played, inside⟩, by simp [whitePort?, inside], ?_, ?_,
          retained, nextConfined, nextInterior, facts.2.1, ?_, facts.2.2.1⟩
        · exact ⟨(restrict_at region frame.visible.board inside).trans data.1,
            RegionCapture.opponent_noSuicide region frame.visible.board colour played inside
              confined interior data.2.1⟩
        · change restrict region target.visible.board = boardAfterPlay (restrict region frame.visible.board) colour.other played
          rw [data.2.2.1]
          exact RegionCapture.opponent_board_exact region frame.visible.board colour played inside confined interior
        · simpa using data.2.2.2
      · have external := RegionProjection.outside_nativeStep region interior opponent inside step
        exact ⟨.environment, by simp [whitePort?, inside], trivial, external.1,
          retained, nextConfined, nextInterior, external.2.1, external.2.2.2.1, external.2.2.1⟩

/-- A raw regional state and a raw action are checked against the actual
current/past. No later node, strategy, or coverage assertion enters this check. -/
def ownStep? {n : Nat} (region : Finset (Point n)) (connected : ExteriorSource.Connected region)
    (frame : Frame n) (colour : Polarity) (rawBoard : Board n)
    (history : List (Finset (Point n))) (played : Point n) :
    Option (OwnStep region frame colour history played) :=
  if same : rawBoard = restrict region frame.visible.board then
    if historyExact : HistoryMatches frame colour history then
      if playing : frame.visible.status = .playing then
        if owned : frame.visible.toMove = colour then
          if inside : played ∈ region then
            if neighbours : adjacentPoints played ⊆ region then
              if confined : ∀ point, frame.visible.board point = some colour → point ∈ region then
                if interior : ∀ point, frame.visible.board point = some colour → adjacentPoints point ⊆ region then
                  if room : (stones frame.visible.board colour.other).card < (Finset.univ \ region).card then
                    if empty : rawBoard played = none then
                      if legal : stoneHasLiberty (boardAfterPlay rawBoard colour played) played then
                        if fresh : CoreHistory.covered history (stones (boardAfterPlay rawBoard colour played) colour) = false then
                          some (ownStep region frame colour history historyExact played playing owned inside neighbours
                            confined interior (connected.capacity frame.visible.board colour room)
                            (by rw [← same]; exact empty) (by rw [← same]; exact legal)
                            (by unfold postCore; rw [← same]; exact fresh))
                        else none
                      else none
                    else none
                  else none
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem vital_holds_lift {n : Nat} (region : Finset (Point n)) {board : Board n}
    {colour : Polarity} {g : VitalChambers.Geometry n}
    (roomsInside : ∀ room ∈ g.rooms, room ⊆ region)
    (holds : VitalChambers.Holds g colour (restrict region board)) :
    VitalChambers.Holds g colour board := by
  refine ⟨?_, ?_, ?_⟩
  · intro stone member
    exact ((restrict_colour region board colour stone).mp (holds.1 stone member)).2
  · intro room member point inside
    have absent := holds.2.1 room member point inside
    rw [restrict_at region board (roomsInside room member inside)] at absent
    exact absent
  · intro room member
    obtain ⟨point, inside, empty⟩ := holds.2.2 room member
    refine ⟨point, inside, ?_⟩
    rw [restrict_at region board (roomsInside room member inside)] at empty
    exact empty

/-- The retained vital geometry is checked on the current regional board,
then lifted to the original perpetual-area Certificate leaf. -/
def vitalLeaf? (region : Finset (Point 19)) (frame : Frame 19) (rawBoard : Board 19)
    (core : Finset (Point 19)) (rooms : Finset (Finset (Point 19))) :
    Option (Certificate .positive (-345) frame) :=
  if same : rawBoard = restrict region frame.visible.board then
    if scoring : frame.visible.status = .playing ∨ frame.visible.status = .terminal .twoPasses then
      (VitalChambers.geometry? core rooms).bind (fun geometry =>
        if roomsInside : ∀ room ∈ geometry.rooms, room ⊆ region then
          if holds : VitalChambers.Holds geometry .positive rawBoard then
            if accepted : acceptsMargin .positive (-345) (VitalChambers.bound geometry .positive) = true then
              some (.vitalChambers ⟨geometry, vital_holds_lift region roomsInside
                (by rw [← same]; exact holds)⟩ scoring accepted)
            else none
          else none
        else none)
    else none
  else none

structure Snapshot where
  board : Board 19
  history : List (Finset (Point 19))
  turn : Polarity
  remaining : Nat

def Snapshot.rank (state : Snapshot) : Nat :=
  2 * state.remaining + if state.turn = .negative then 1 else 0

def Snapshot.ownNext (state : Snapshot) (point : Point 19) : Snapshot :=
  let board := boardAfterPlay state.board .positive point
  ⟨board, CoreHistory.insertFootprint (stones board .positive) state.history,
    .negative, state.remaining - 1⟩

def Snapshot.whiteNext {region : Finset (Point 19)} (state : Snapshot)
    (port : WhitePort region) : Snapshot :=
  ⟨port.nextBoard state.board .positive, state.history, .positive, state.remaining⟩

/-- A placement's capture set is computed before its matrix is read. Returning
only a function-valued board can move that computation into every point read. -/
structure PlayEffect (board : Board 19) (colour : Polarity) (point : Point 19) where
  signature : BoardSignature 19
  exact : BufferedReplay.signatureBoard signature = boardAfterPlay board colour point

@[noinline] def capturePlayEffect (board : Board 19) (colour : Polarity) (point : Point 19) :
    PlayEffect board colour point := by
  let captured := capturedStonesAfterPlay board colour point
  let placed := Board.set board point (some colour)
  let effect : Board 19 := fun candidate => if candidate ∈ captured then none else placed candidate
  refine ⟨boardSignature effect, ?_⟩
  exact BufferedReplay.signatureBoard_boardSignature effect

def PlayEffect.board {board : Board 19} {colour : Polarity} {point : Point 19}
    (effect : PlayEffect board colour point) : Board 19 :=
  BufferedReplay.signatureBoard effect.signature

theorem PlayEffect.board_eq {board : Board 19} {colour : Polarity} {point : Point 19}
    (effect : PlayEffect board colour point) : effect.board = boardAfterPlay board colour point :=
  effect.exact

def Snapshot.ownEffect (state : Snapshot) (point : Point 19)
    (effect : PlayEffect state.board .positive point) : Snapshot :=
  ⟨effect.board, CoreHistory.insertFootprint (stones effect.board .positive) state.history,
    .negative, state.remaining - 1⟩

theorem Snapshot.ownEffect_eq (state : Snapshot) (point : Point 19)
    (effect : PlayEffect state.board .positive point) : state.ownEffect point effect = state.ownNext point := by
  simp only [ownEffect, ownNext, effect.board_eq]

@[noinline] def Snapshot.whiteEffect {region : Finset (Point 19)} (state : Snapshot)
    (port : WhitePort region) : { next : Snapshot // next = state.whiteNext port } := by
  cases port with
  | play point =>
      let effect := capturePlayEffect state.board .negative point.1
      refine ⟨⟨effect.board, state.history, .positive, state.remaining⟩, ?_⟩
      simp only [whiteNext, WhitePort.nextBoard, Polarity.other_positive, effect.board_eq]
  | environment => exact ⟨state.whiteNext .environment, rfl⟩
  | pass => exact ⟨state.whiteNext .pass, rfl⟩

theorem Snapshot.own_rank (state : Snapshot) (point : Point 19)
    (owned : state.turn = .positive) (available : 0 < state.remaining) :
    (state.ownNext point).rank + 1 = state.rank := by
  simp only [rank, ownNext, owned, reduceCtorEq, ↓reduceIte]
  omega

theorem Snapshot.white_rank {region : Finset (Point 19)} (state : Snapshot)
    (port : WhitePort region) (opponent : state.turn = .negative) :
    (state.whiteNext port).rank + 1 = state.rank := by
  simp [rank, whiteNext, opponent]

def Snapshot.Equivalent (left right : Snapshot) : Prop :=
  left.board = right.board ∧ left.turn = right.turn ∧ left.remaining = right.remaining ∧
    HistoryDominates left.history right.history ∧ HistoryDominates right.history left.history

instance (left right : Snapshot) : Decidable (left.Equivalent right) :=
  inferInstanceAs (Decidable (left.board = right.board ∧ left.turn = right.turn ∧
    left.remaining = right.remaining ∧
    (∀ old ∈ left.history, CoreHistory.covered right.history old = true) ∧
    (∀ old ∈ right.history, CoreHistory.covered left.history old = true)))

/-- Current board, complete past, phase and unspent physical exterior capacity.
The credit is spent by each checked edge; it contains no future game result. -/
structure SourceAt (region : Finset (Point 19)) (state : Snapshot) (frame : Frame 19) : Prop where
  board_eq : restrict region frame.visible.board = state.board
  history_exact : HistoryMatches frame .positive state.history
  playing : frame.visible.status = .playing
  turn : frame.visible.toMove = state.turn
  passes : state.turn = .negative → frame.visible.consecutivePasses = 0
  confined : Confined region frame.visible.board .positive
  interior : SupportInterior region frame.visible.board .positive
  credit : (ExteriorLiberty.occupiedPoints frame.visible.board).card + state.rank <
    (Finset.univ \ region).card

theorem SourceAt.capacity {region : Finset (Point 19)} {state : Snapshot} {frame : Frame 19}
    (source : SourceAt region state frame) (connected : ExteriorSource.Connected region) :
    RegionSparse.Capacity region frame.visible.board .positive := by
  apply connected.capacity
  have occupied := ExteriorLiberty.stones_le_occupied frame.visible.board Polarity.positive.other
  have room := source.credit
  omega

theorem SourceAt.black_stones {region : Finset (Point 19)} {state : Snapshot} {frame : Frame 19}
    (source : SourceAt region state frame) : stones state.board .positive = stones frame.visible.board .positive := by
  rw [← source.board_eq]
  ext point
  simp only [stones, Finset.mem_filter, Finset.mem_univ, true_and]
  exact confined_colour region frame.visible.board .positive source.confined point

theorem occupied_step_le {frame target : Frame 19} {move : Move 19}
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    (ExteriorLiberty.occupiedPoints target.visible.board).card ≤
      (ExteriorLiberty.occupiedPoints frame.visible.board).card + 1 := by
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass => rw [(pass_step_facts step).2.1]; omega
  | play point =>
      rw [(native_play_data step).2.2.1]
      exact ExteriorLiberty.occupied_afterPlay_le frame.visible.board frame.visible.toMove point

theorem SourceAt.credit_step {region : Finset (Point 19)} {state next : Snapshot}
    {frame target : Frame 19} (source : SourceAt region state frame) {move : Move 19}
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (progress : next.rank + 1 ≤ state.rank) :
    (ExteriorLiberty.occupiedPoints target.visible.board).card + next.rank <
      (Finset.univ \ region).card := by
  have growth := occupied_step_le scoring step
  have credit := source.credit
  omega

theorem SourceAt.transport {region : Finset (Point 19)} {left right : Snapshot} {frame : Frame 19}
    (source : SourceAt region left frame) (same : left.Equivalent right) : SourceAt region right frame := by
  refine ⟨source.board_eq.trans same.1, source.history_exact.of_equivalent same.2.2.2.1 same.2.2.2.2,
    source.playing, source.turn.trans same.2.1, ?_, source.confined, source.interior, ?_⟩
  · intro opponent
    exact source.passes (same.2.1.trans opponent)
  · have ranks : left.rank = right.rank := by simp only [Snapshot.rank, same.2.1, same.2.2.1]
    rw [← ranks]
    exact source.credit

structure SourceWitness (region : Finset (Point 19)) (state : Snapshot) (frame : Frame 19) : Type where
  valid : SourceAt region state frame

def sourceAt? (region : Finset (Point 19)) (state : Snapshot) (frame : Frame 19) :
    Option (SourceWitness region state frame) :=
  if board : restrict region frame.visible.board = state.board then
    if historyExact : HistoryMatches frame .positive state.history then
      if playing : frame.visible.status = .playing then
        if turn : frame.visible.toMove = state.turn then
          if passes : state.turn = .negative → frame.visible.consecutivePasses = 0 then
            if confined : ∀ point, frame.visible.board point = some .positive → point ∈ region then
              if interior : ∀ point, frame.visible.board point = some .positive → adjacentPoints point ⊆ region then
                if credit : (ExteriorLiberty.occupiedPoints frame.visible.board).card + state.rank <
                    (Finset.univ \ region).card then
                  some ⟨⟨board, historyExact, playing, turn, passes, confined, interior, credit⟩⟩
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

structure OwnSource (region : Finset (Point 19)) (state : Snapshot) (frame : Frame 19)
    (point : Point 19) where
  reply : ScoringReply frame
  source : SourceAt region (state.ownNext point) reply.target

def ownSource (region : Finset (Point 19)) (connected : ExteriorSource.Connected region)
    (state : Snapshot) (frame : Frame 19) (source : SourceAt region state frame)
    (point : Point 19) (owned : state.turn = .positive) (available : 0 < state.remaining)
    (inside : point ∈ region) (neighbours : adjacentPoints point ⊆ region)
    (empty : state.board point = none)
    (legal : stoneHasLiberty (boardAfterPlay state.board .positive point) point)
    (fresh : CoreHistory.covered state.history (stones (boardAfterPlay state.board .positive point) .positive) = false) :
    OwnSource region state frame point := by
  have originalOwned := source.turn.trans owned
  let produced := ownStep region frame .positive state.history source.history_exact point
    source.playing originalOwned inside neighbours source.confined source.interior (source.capacity connected)
    (by rw [source.board_eq]; exact empty) (by rw [source.board_eq]; exact legal)
    (by unfold postCore; rw [source.board_eq]; exact fresh)
  have step : LegalStep (Law.positionalSuperko 0) frame (.play point) produced.reply.target := by
    rw [← produced.move_eq]
    exact produced.reply.step
  have data := native_play_data step
  refine ⟨produced.reply, ?_⟩
  refine ⟨?_, ?_, (play_step_facts step).2.1, ?_, fun _ => (play_step_facts step).2.2.1,
    produced.confined, produced.interior,
    source.credit_step produced.reply.notResign produced.reply.step (by rw [Snapshot.own_rank state point owned available])⟩
  · simpa only [Snapshot.ownNext, source.board_eq] using produced.board_eq
  · simpa only [Snapshot.ownNext, postCore, source.board_eq] using produced.history_matches
  · simpa only [Snapshot.ownNext, originalOwned, Polarity.other_positive] using data.2.2.2

structure WhiteSource (region : Finset (Point 19)) (state : Snapshot) (target : Frame 19) where
  port : WhitePort region
  admitted : port.Admitted state.board .positive
  source : SourceAt region (state.whiteNext port) target

def whiteSource (region : Finset (Point 19)) (state : Snapshot) {frame target : Frame 19}
    (source : SourceAt region state frame) (opponent : state.turn = .negative)
    (recorded : CoreHistory.covered state.history (stones state.board .positive) = true)
    {move : Move 19} (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) : WhiteSource region state target := by
  have originalOpponent : frame.visible.toMove = Polarity.positive.other := source.turn.trans opponent
  let represented := whiteStep region .positive state.history source.history_exact
    (by rw [← source.black_stones]; exact recorded) source.confined source.interior
    originalOpponent (source.passes opponent) scoring step
  refine ⟨represented.port, ?_, ?_⟩
  · simpa only [source.board_eq] using represented.admitted
  · refine ⟨?_, represented.history_matches, represented.playing, represented.owned,
      ?_, represented.confined, represented.interior,
      source.credit_step scoring step (by rw [Snapshot.white_rank state represented.port opponent])⟩
    · simpa only [Snapshot.whiteNext, source.board_eq] using represented.board_eq
    · intro impossible
      cases impossible

structure NodeProgram (region : Finset (Point 19)) (state : Snapshot) where
  run : (frame : Frame 19) → SourceAt region state frame → Certificate .positive (-345) frame

def NodeProgram.transport {region : Finset (Point 19)} {left right : Snapshot}
    (program : NodeProgram region right) (same : left.Equivalent right) : NodeProgram region left :=
  ⟨fun frame source => program.run frame (source.transport same)⟩

inductive PortCode where
  | play (point : Point 19)
  | environment
  | pass
  deriving DecidableEq

def WhitePort.code {region : Finset (Point 19)} : WhitePort region → PortCode
  | .play point => .play point.1
  | .environment => .environment
  | .pass => .pass

def whitePorts (region : Finset (Point 19)) : List (WhitePort region) :=
  (allPoints 19).filterMap (fun point =>
    if inside : point ∈ region then some (.play ⟨point, inside⟩) else none) ++ [.environment, .pass]

theorem mem_whitePorts {region : Finset (Point 19)} (port : WhitePort region) :
    port ∈ whitePorts region := by
  cases port with
  | play point =>
      exact List.mem_append_left _ (List.mem_filterMap.mpr
        ⟨point.1, point_mem_allPoints _, by simp [point.2]⟩)
  | environment => simp [whitePorts]
  | pass => simp [whitePorts]

def admittedPorts (region : Finset (Point 19)) (state : Snapshot) : List (WhitePort region) :=
  (whitePorts region).filter (fun port => decide (port.Admitted state.board .positive))

/-- Compute capture once before the liberty reader asks for board points. -/
def captureAdmitted {region : Finset (Point 19)} (board : Board 19) (colour : Polarity)
    (port : WhitePort region) : Bool :=
  match port with
  | .play point =>
      if board point.1 = none then
        let captured := capturedStonesAfterPlay board colour.other point.1
        let placed := Board.set board point.1 (some colour.other)
        decide (stoneHasLiberty (fun candidate => if candidate ∈ captured then none else placed candidate) point.1)
      else false
  | .environment | .pass => true

theorem captureAdmitted_eq {region : Finset (Point 19)} (board : Board 19) (colour : Polarity)
    (port : WhitePort region) : captureAdmitted board colour port = decide (port.Admitted board colour) := by
  cases port with
  | play point =>
      change (if board point.1 = none then
        decide (stoneHasLiberty (boardAfterPlay board colour.other point.1) point.1) else false) = _
      by_cases empty : board point.1 = none <;> simp [empty, WhitePort.Admitted]
  | environment => rfl
  | pass => rfl

def captureAdmittedPorts (region : Finset (Point 19)) (state : Snapshot) : List (WhitePort region) :=
  (whitePorts region).filter (fun port => captureAdmitted state.board .positive port)

theorem captureAdmittedPorts_eq (region : Finset (Point 19)) (state : Snapshot) :
    captureAdmittedPorts region state = admittedPorts region state := by
  simp only [captureAdmittedPorts, admittedPorts, captureAdmitted_eq]

theorem mem_admittedPorts {region : Finset (Point 19)} {state : Snapshot} (port : WhitePort region)
    (admitted : port.Admitted state.board .positive) : port ∈ admittedPorts region state :=
  List.mem_filter.mpr ⟨mem_whitePorts port, decide_eq_true admitted⟩

theorem mem_captureAdmittedPorts {region : Finset (Point 19)} {state : Snapshot}
    (port : WhitePort region) (admitted : port.Admitted state.board .positive) :
    port ∈ captureAdmittedPorts region state := by
  rw [captureAdmittedPorts_eq]
  exact mem_admittedPorts port admitted

private def collect? : (count : Nat) → (family : Fin count → Type) →
    ((index : Fin count) → Option (family index)) → Option ((index : Fin count) → family index)
  | 0, _, _ => some (fun index => Fin.elim0 index)
  | count + 1, family, read => do
      let first ← read 0
      let rest ← collect? count (fun index => family index.succ) (fun index => read index.succ)
      pure (fun index => match index with
        | ⟨0, _⟩ => first
        | ⟨later + 1, bound⟩ => rest ⟨later, Nat.lt_of_succ_lt_succ bound⟩)

inductive RawBody where
  | own (point : Point 19) (child : Nat)
  | white (edges : List (PortCode × Nat))
  | coalition
  | vital (core : Finset (Point 19)) (rooms : Finset (Finset (Point 19)))

structure RawNode where
  state : Snapshot
  body : RawBody

abbrev CheckedRows (region : Finset (Point 19)) (nodes : Array RawNode) :=
  Array (Option ((index : Fin nodes.size) × NodeProgram region nodes[index].state))

def checkedRow? {region : Finset (Point 19)} {nodes : Array RawNode}
    (rows : CheckedRows region nodes) (index : Fin nodes.size) :
    Option (NodeProgram region nodes[index].state) :=
  match rows[index.val]? with
  | some (some ⟨stored, program⟩) => if same : stored = index then some (same ▸ program) else none
  | _ => none

/-- Each used edge checks the actual source effect, all retained historical
queries and strict rank descent before consuming a previously compiled row. -/
def checkedEdge? {region : Finset (Point 19)} {nodes : Array RawNode}
    (rows : CheckedRows region nodes) (parent expected : Snapshot) (child : Nat) :
    Option (NodeProgram region expected) :=
  if bounded : child < nodes.size then
    let index : Fin nodes.size := ⟨child, bounded⟩
    if nodes[index].state.rank + 1 = parent.rank then
      if same : expected.Equivalent nodes[index].state then
        (checkedRow? rows index).map (fun program => program.transport same)
      else none
    else none
  else none

def compileNode? (region : Finset (Point 19)) (connected : ExteriorSource.Connected region)
    (nodes : Array RawNode) (rows : CheckedRows region nodes) (index : Fin nodes.size) :
    Option (NodeProgram region nodes[index].state) :=
  let state := nodes[index].state
  match nodes[index].body with
  | .coalition =>
      (EyeCoalition.recognize? state.board .positive).bind (fun detected =>
        if accepted : acceptsMargin .positive (-345) (EyeCoalition.bound detected.geometry .positive) = true then
          some ⟨fun frame source => VirginRegionAction.coalitionCertificate region frame .positive (-345)
            source.interior ⟨detected.geometry, by rw [source.board_eq]; exact detected.holds⟩
            (.inl source.playing) accepted⟩
        else none)
  | .vital core rooms =>
      (VitalChambers.geometry? core rooms).bind (fun geometry =>
        if roomsInside : ∀ room ∈ geometry.rooms, room ⊆ region then
          if holds : VitalChambers.Holds geometry .positive state.board then
            if accepted : acceptsMargin .positive (-345) (VitalChambers.bound geometry .positive) = true then
              some ⟨fun frame source => .vitalChambers
                ⟨geometry, vital_holds_lift region roomsInside (by rw [source.board_eq]; exact holds)⟩
                (.inl source.playing) accepted⟩
            else none
          else none
        else none)
  | .own point child =>
      if owned : state.turn = .positive then
        if available : 0 < state.remaining then
          if inside : point ∈ region then
            if neighbours : adjacentPoints point ⊆ region then
              if empty : state.board point = none then
                let effect := capturePlayEffect state.board .positive point
                if legal : stoneHasLiberty effect.board point then
                  if fresh : CoreHistory.covered state.history
                      (stones effect.board .positive) = false then
                    (checkedEdge? rows state (state.ownEffect point effect) child).map (fun continuation =>
                      ⟨fun frame source =>
                        let original : NodeProgram region (state.ownNext point) :=
                          state.ownEffect_eq point effect ▸ continuation
                        let next := ownSource region connected state frame source point owned available
                          inside neighbours empty (by simpa only [effect.board_eq] using legal)
                          (by simpa only [effect.board_eq] using fresh)
                        .choose (source.turn.trans owned) next.reply
                          (original.run next.reply.target next.source)⟩)
                  else none
                else none
              else none
            else none
          else none
        else none
      else none
  | .white edges =>
      if opponent : state.turn = .negative then
        if recorded : CoreHistory.covered state.history (stones state.board .positive) = true then
          let ports := captureAdmittedPorts region state
          if edges.length = ports.length then
            (collect? ports.length (fun port => NodeProgram region (state.whiteNext (ports.get port)))
              (fun port =>
                (edges.find? (fun edge => edge.1 == (ports.get port).code)).bind
                  (fun edge =>
                    let expected := state.whiteEffect (ports.get port)
                    (checkedEdge? rows state expected.val edge.2).map
                      (fun continuation => expected.property ▸ continuation)))).map
              (fun continuations => ⟨fun frame source =>
                let expansion := scoringExpansion frame
                .all source.playing (by rw [source.turn, opponent]; decide) (fun originalPort => by
                  let observed := expansion.get originalPort
                  let target := BufferedReplay.restore (BufferedReplay.capture observed.2)
                  have targetSame : target = observed.2 := BufferedReplay.restore_capture observed.2
                  have native := mem_scoringExpansion_iff.mp (List.get_mem expansion originalPort)
                  have step : LegalStep (Law.positionalSuperko 0) frame observed.1 target := by
                    rw [targetSame]; exact native.1
                  let next := whiteSource region state source opponent recorded native.2 step
                  have member := mem_captureAdmittedPorts next.port next.admitted
                  let selected : Fin ports.length := ⟨ports.idxOf next.port, List.idxOf_lt_length_iff.mpr member⟩
                  have selectedEq : ports.get selected = next.port := by
                    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr member)
                  let result := (continuations selected).run target (by rw [selectedEq]; exact next.source)
                  exact targetSame ▸ result)⟩)
          else none
        else none
      else none

structure Compiled (region : Finset (Point 19)) (nodes : Array RawNode) where
  root : Fin nodes.size
  program : NodeProgram region nodes[root].state

/-- Ascending rank visits each supplied node once. The cache stores the typed
program already paid at that exact raw row; it never stores a C++ win assertion. -/
def compileDAG (region : Finset (Point 19)) (connected : ExteriorSource.Connected region)
    (nodes : Array RawNode) (root : Nat) : Except Nat (Compiled region nodes) := do
  if bounded : root < nodes.size then
    let order := (List.finRange nodes.size).mergeSort (fun left right => nodes[left].state.rank ≤ nodes[right].state.rank)
    let rows ← order.foldlM (m := Except Nat) (fun rows index => do
      let some program := compileNode? region connected nodes rows index | throw index.val
      pure (rows.set! index.val (some ⟨index, program⟩)))
      (Array.replicate nodes.size none : CheckedRows region nodes)
    let index : Fin nodes.size := ⟨root, bounded⟩
    let some program := checkedRow? rows index | throw root
    pure ⟨index, program⟩
  else throw root

def compileDAG? (region : Finset (Point 19)) (connected : ExteriorSource.Connected region)
    (nodes : Array RawNode) (root : Nat) : Option (Compiled region nodes) :=
  (compileDAG region connected nodes root).toOption

def Compiled.at? {region : Finset (Point 19)} {nodes : Array RawNode}
    (compiled : Compiled region nodes) (frame : Frame 19) : Option (Certificate .positive (-345) frame) := do
  let source ← sourceAt? region nodes[compiled.root].state frame
  pure (compiled.program.run frame source.valid)

def interpret? (region : Finset (Point 19)) (connected : ExteriorSource.Connected region)
    (nodes : Array RawNode) (root : Nat) (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  (compileDAG? region connected nodes root).bind (fun program => program.at? frame)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram
