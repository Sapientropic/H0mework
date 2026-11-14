import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ForcingClosure
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StrategyCertificate
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.PassSettlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.InitialColourPass

def swapCell (cell : Option Polarity) : Option Polarity := cell.map Polarity.other

@[simp] theorem swapCell_involutive (cell : Option Polarity) :
    swapCell (swapCell cell) = cell := by
  cases cell <;> simp [swapCell]

theorem swapCell_injective : Function.Injective swapCell :=
  Function.LeftInverse.injective swapCell_involutive

@[simp] theorem swapCell_eq_iff (left right : Option Polarity) :
    swapCell left = swapCell right ↔ left = right := swapCell_injective.eq_iff

@[simp] theorem swapCell_none (cell : Option Polarity) :
    swapCell cell = none ↔ cell = none := by cases cell <;> simp [swapCell]

@[simp] theorem swapCell_some (cell : Option Polarity) (colour : Polarity) :
    swapCell cell = some colour ↔ cell = some colour.other := by
  cases cell with
  | none => simp [swapCell]
  | some present => cases present <;> cases colour <;> decide

def swapBoard {n : Nat} (board : Board n) : Board n := fun point => swapCell (board point)

@[simp] theorem swapBoard_apply_none {n : Nat} (board : Board n) (point : Point n) :
    swapBoard board point = none ↔ board point = none := swapCell_none _

@[simp] theorem swapBoard_apply_some {n : Nat} (board : Board n) (point : Point n)
    (colour : Polarity) : swapBoard board point = some colour ↔ board point = some colour.other :=
  swapCell_some _ _

@[simp] theorem swapBoard_involutive {n : Nat} (board : Board n) :
    swapBoard (swapBoard board) = board := by funext point; exact swapCell_involutive _

@[simp] theorem swapBoard_empty {n : Nat} : swapBoard (Board.empty : Board n) = Board.empty := rfl

theorem swapBoard_set {n : Nat} (board : Board n) (point : Point n) (cell : Option Polarity) :
    swapBoard (Board.set board point cell) = Board.set (swapBoard board) point (swapCell cell) := by
  funext other
  by_cases same : other = point
  · subst other; simp [swapBoard]
  · simp [swapBoard, Board.set_other _ _ same]

theorem componentWorklist_swap {n : Nat} (board : Board n) (cell : Option Polarity)
    (fuel : Nat) (pending seen : List (Point n)) :
    componentWorklist (swapBoard board) (swapCell cell) fuel pending seen =
      componentWorklist board cell fuel pending seen := by
  induction fuel generalizing pending seen with
  | zero => rfl
  | succ fuel ih =>
      cases pending with
      | nil => rfl
      | cons point rest => simp [componentWorklist, swapBoard, ih]

@[simp] theorem componentAt_swap {n : Nat} (board : Board n) (point : Point n) :
    componentAt (swapBoard board) point = componentAt board point := by
  exact congrArg List.toFinset (componentWorklist_swap board (board point) _ _ _)

@[simp] theorem groupAt_swap {n : Nat} (board : Board n) (point : Point n) :
    groupAt (swapBoard board) point = groupAt board point := by
  unfold groupAt
  cases value : board point <;> simp [swapBoard, swapCell, value, componentAt_swap]

@[simp] theorem emptyRegionAt_swap {n : Nat} (board : Board n) (point : Point n) :
    emptyRegionAt (swapBoard board) point = emptyRegionAt board point := by
  unfold emptyRegionAt
  cases value : board point <;> simp [swapBoard, swapCell, value, componentAt_swap]

@[simp] theorem groupHasLiberty_swap {n : Nat} (board : Board n) (group : Finset (Point n)) :
    GroupHasLiberty (swapBoard board) group ↔ GroupHasLiberty board group := by
  simp [GroupHasLiberty, swapBoard]

@[simp] theorem stoneHasLiberty_swap {n : Nat} (board : Board n) (point : Point n) :
    stoneHasLiberty (swapBoard board) point ↔ stoneHasLiberty board point := by
  simp [stoneHasLiberty]

@[simp] theorem capturedStonesAfterPlay_swap {n : Nat} (board : Board n)
    (colour : Polarity) (point : Point n) :
    capturedStonesAfterPlay (swapBoard board) colour.other point =
      capturedStonesAfterPlay board colour point := by
  unfold capturedStonesAfterPlay
  have placed : Board.set (swapBoard board) point (some colour.other) =
      swapBoard (Board.set board point (some colour)) := (swapBoard_set board point (some colour)).symm
  rw [placed]
  simp only [Polarity.other_other, swapBoard_apply_some, stoneHasLiberty_swap, groupAt_swap]

theorem boardAfterPlay_swap {n : Nat} (board : Board n) (colour : Polarity) (point : Point n) :
    boardAfterPlay (swapBoard board) colour.other point =
      swapBoard (boardAfterPlay board colour point) := by
  funext candidate
  unfold boardAfterPlay
  rw [capturedStonesAfterPlay_swap]
  by_cases captured : candidate ∈ capturedStonesAfterPlay board colour point
  · simp [captured, swapBoard, swapCell]
  · simp only [captured, ↓reduceIte, swapBoard]
    exact (congrFun (swapBoard_set board point (some colour)) candidate).symm

def swapSignature {n : Nat} (signature : BoardSignature n) : BoardSignature n :=
  signature.map (List.map swapCell)

@[simp] theorem swapSignature_involutive {n : Nat} (signature : BoardSignature n) :
    swapSignature (swapSignature signature) = signature := by
  simp [swapSignature, List.map_map, Function.comp_def]

theorem swapSignature_injective {n : Nat} :
    Function.Injective (swapSignature (n := n)) :=
  Function.LeftInverse.injective swapSignature_involutive

@[simp] theorem swapSignature_eq_iff {n : Nat} (left right : BoardSignature n) :
    swapSignature left = swapSignature right ↔ left = right := swapSignature_injective.eq_iff

theorem boardSignature_swap {n : Nat} (board : Board n) :
    boardSignature (swapBoard board) = swapSignature (boardSignature board) := by
  simp [boardSignature, swapSignature, List.map_ofFn, swapBoard, Function.comp_def]

def swapStatus : Status → Status
  | .playing => .playing
  | .terminal .twoPasses => .terminal .twoPasses
  | .terminal (.resignation winner) => .terminal (.resignation winner.other)

@[simp] theorem swapStatus_involutive (status : Status) : swapStatus (swapStatus status) = status := by
  cases status with
  | playing => rfl
  | terminal reason => cases reason <;> simp [swapStatus]

def swapSituation {n : Nat} (situation : Situation n) : Situation n :=
  ⟨swapSignature situation.board, situation.toMove.other⟩

def swapVisible {n : Nat} (visible : VisiblePosition n) : VisiblePosition n :=
  ⟨swapBoard visible.board, visible.toMove.other, visible.consecutivePasses, swapStatus visible.status⟩

def swapFrame {n : Nat} (frame : Frame n) : Frame n :=
  ⟨swapVisible frame.visible, frame.positionHistory.map swapSituation⟩

@[simp] theorem swapSituation_involutive {n : Nat} (situation : Situation n) :
    swapSituation (swapSituation situation) = situation := by
  cases situation; simp [swapSituation]

@[simp] theorem swapVisible_involutive {n : Nat} (visible : VisiblePosition n) :
    swapVisible (swapVisible visible) = visible := by
  cases visible; simp [swapVisible]

@[simp] theorem swapFrame_involutive {n : Nat} (frame : Frame n) :
    swapFrame (swapFrame frame) = frame := by
  cases frame; simp [swapFrame, List.map_map, Function.comp_def]

theorem swapVisible_situation {n : Nat} (visible : VisiblePosition n) :
    (swapVisible visible).situation = swapSituation visible.situation := by
  simp [swapVisible, swapSituation, VisiblePosition.situation, boardSignature_swap]

theorem swapFrame_advance {n : Nat} (frame : Frame n) (visible : VisiblePosition n) :
    swapFrame (frame.advance visible) = (swapFrame frame).advance (swapVisible visible) := by
  simp [swapFrame, Frame.advance, swapVisible_situation]

theorem repetition_swap {n : Nat} (history : List (Situation n)) (next : Situation n) :
    violatesRepetition .positionalSuperko (history.map swapSituation) (swapSituation next) ↔
      violatesRepetition .positionalSuperko history next := by
  simp [violatesRepetition, swapSituation]

theorem playVisible_swap {n : Nat} (frame : Frame n) (point : Point n) :
    playVisible? (Law.positionalSuperko 0) (swapFrame frame) point =
      (playVisible? (Law.positionalSuperko 0) frame point).map swapVisible := by
  have repetition : ∀ board colour,
      violatesRepetition (Law.positionalSuperko 0).repetition (frame.positionHistory.map swapSituation)
        ⟨boardSignature (swapBoard board), colour.other⟩ ↔
      violatesRepetition (Law.positionalSuperko 0).repetition frame.positionHistory
        ⟨boardSignature board, colour⟩ := by
    intro board colour
    simpa [Law.positionalSuperko, swapSituation, boardSignature_swap] using
      repetition_swap frame.positionHistory ⟨boardSignature board, colour⟩
  have repeated :
      violatesRepetition (Law.positionalSuperko 0).repetition (frame.positionHistory.map swapSituation)
        ⟨boardSignature (swapBoard (boardAfterPlay frame.visible.board frame.visible.toMove point)),
          frame.visible.toMove⟩ ↔
      violatesRepetition (Law.positionalSuperko 0).repetition frame.positionHistory
        ⟨boardSignature (boardAfterPlay frame.visible.board frame.visible.toMove point),
          frame.visible.toMove.other⟩ := by
    simpa using repetition (boardAfterPlay frame.visible.board frame.visible.toMove point)
      frame.visible.toMove.other
  cases status : frame.visible.status with
  | terminal reason => cases reason <;> simp [playVisible?, swapFrame, swapVisible, swapStatus, status]
  | playing =>
      simp only [playVisible?, swapFrame, swapVisible, status, swapStatus,
        boardAfterPlay_swap, swapBoard_apply_none,
        stoneHasLiberty_swap, Polarity.other_other, repeated]
      split_ifs <;> first | rfl | simp [swapVisible, swapStatus]

theorem stepVisible_swap {n : Nat} (frame : Frame n) (move : Move n) :
    stepVisible? (Law.positionalSuperko 0) (swapFrame frame) move =
      (stepVisible? (Law.positionalSuperko 0) frame move).map swapVisible := by
  cases move with
  | play point => exact playVisible_swap frame point
  | pass =>
      cases status : frame.visible.status with
      | terminal reason => cases reason <;> simp [stepVisible?, passVisible?, swapFrame, swapVisible, swapStatus, status]
      | playing =>
          simp [stepVisible?, passVisible?, swapFrame, swapVisible, swapStatus, status,
            Law.positionalSuperko]
          split <;> rfl
  | resign =>
      cases status : frame.visible.status with
      | terminal reason => cases reason <;> simp [stepVisible?, resignVisible?, swapFrame, swapVisible, swapStatus, status]
      | playing => simp [stepVisible?, resignVisible?, swapFrame, swapVisible, swapStatus, status]

theorem nativeStep_swap {n : Nat} (frame : Frame n) (move : Move n) :
    nativeStep? (Law.positionalSuperko 0) (swapFrame frame) move =
      (nativeStep? (Law.positionalSuperko 0) frame move).map swapFrame := by
  simp only [nativeStep?, stepVisible_swap, Option.map_map]
  congr 1
  funext visible
  exact (swapFrame_advance frame visible).symm

theorem legalStep_swap {n : Nat} {frame target : Frame n} {move : Move n}
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    LegalStep (Law.positionalSuperko 0) (swapFrame frame) move (swapFrame target) := by
  unfold LegalStep at *
  rw [nativeStep_swap, step, Option.map_some]

theorem borderingColour_swap {n : Nat} (board : Board n) (region : Finset (Point n))
    (colour : Polarity) :
    colour ∈ borderingColours (swapBoard board) region ↔
      colour.other ∈ borderingColours board region := by
  simp [borderingColours, swapBoard]

theorem borderingSingleton_swap {n : Nat} (board : Board n) (region : Finset (Point n))
    (colour : Polarity) :
    borderingColours (swapBoard board) region = {colour} ↔
      borderingColours board region = {colour.other} := by
  constructor
  · intro same
    ext present
    have read := borderingColour_swap board region present.other
    cases present <;> cases colour <;> simpa [same] using read.symm
  · intro same
    ext present
    have read := borderingColour_swap board region present
    rw [same] at read
    cases present <;> cases colour <;> simpa using read

theorem territoryOwner_swap {n : Nat} (board : Board n) (point : Point n) :
    territoryOwner? (swapBoard board) point = swapCell (territoryOwner? board point) := by
  simp only [territoryOwner?, swapBoard_apply_none,
    emptyRegionAt_swap, borderingSingleton_swap, Polarity.other_positive, Polarity.other_negative]
  split
  · by_cases positive : borderingColours board (emptyRegionAt board point) = {.positive}
    · simp [positive, swapCell]
    · by_cases negative : borderingColours board (emptyRegionAt board point) = {.negative}
      · simp [negative, swapCell]
      · simp [positive, negative, swapCell]
  · rfl

theorem areaScore_swap {n : Nat} (board : Board n) (colour : Polarity) :
    areaScore (swapBoard board) colour = areaScore board colour.other := by
  simp [areaScore, territoryOwner_swap, swapBoard]

theorem areaMargin_swap {n : Nat} (board : Board n) :
    areaMargin (swapBoard board) = -areaMargin board := by
  simp only [areaMargin, areaScore_swap, Polarity.other_positive, Polarity.other_negative]
  omega

/-- Proposition-only complete forcing trees. The constructors use only original
scoring terminals and original legal play/pass steps. -/
inductive Forces {n : Nat} (colour : Polarity) (threshold : Int) : Frame n → Prop
  | terminal {frame : Frame n}
      (finished : frame.visible.status = .terminal .twoPasses)
      (accepted : acceptsMargin colour threshold (areaMargin frame.visible.board) = true) :
      Forces colour threshold frame
  | choose {frame : Frame n} (playing : frame.visible.status = .playing)
      (owned : frame.visible.toMove = colour) (reply : ScoringReply frame)
      (next : Forces colour threshold reply.target) : Forces colour threshold frame
  | all {frame : Frame n} (playing : frame.visible.status = .playing)
      (opponent : frame.visible.toMove ≠ colour)
      (next : ∀ move target, move ≠ .resign →
        LegalStep (Law.positionalSuperko 0) frame move target → Forces colour threshold target) :
      Forces colour threshold frame

theorem Forces.scoring {n : Nat} {colour : Polarity} {threshold : Int} {frame : Frame n}
    (forced : Forces colour threshold frame) : ScoringStatus frame := by
  cases forced with
  | terminal finished _ => exact .inr finished
  | choose playing _ _ _ => exact .inl playing
  | all playing _ _ => exact .inl playing

/-- Finite determinacy is proved in Prop. No board tree is evaluated and this
declaration does not supply an executable branch selector. -/
theorem forcing_dichotomy (n : Nat) (threshold : Int) :
    ∀ frame : Frame n, ScoringStatus frame →
      Forces .negative threshold frame ∨ Forces .positive (threshold + 1) frame := by
  classical
  intro initial
  apply (measure terminationRank).wf.induction initial
  intro frame ih scoring
  rcases scoring with playing | terminal
  · cases owned : frame.visible.toMove with
    | positive =>
        by_cases found : ∃ reply : ScoringReply frame, Forces .positive (threshold + 1) reply.target
        · obtain ⟨reply, next⟩ := found
          exact .inr (.choose playing owned reply next)
        · apply Or.inl
          apply Forces.all playing (by rw [owned]; decide)
          intro move target notResign step
          rcases ih target (nonresigning_legalStep_rank_lt notResign step)
            (nonresigning_step_scoringStatus notResign step) with white | black
          · exact white
          · exact False.elim (found ⟨⟨move, target, notResign, step⟩, black⟩)
    | negative =>
        by_cases found : ∃ reply : ScoringReply frame, Forces .negative threshold reply.target
        · obtain ⟨reply, next⟩ := found
          exact .inl (.choose playing owned reply next)
        · apply Or.inr
          apply Forces.all playing (by rw [owned]; decide)
          intro move target notResign step
          rcases ih target (nonresigning_legalStep_rank_lt notResign step)
            (nonresigning_step_scoringStatus notResign step) with white | black
          · exact False.elim (found ⟨⟨move, target, notResign, step⟩, white⟩)
          · exact black
  · by_cases white : areaMargin frame.visible.board ≤ threshold
    · exact .inl (.terminal terminal (decide_eq_true white))
    · exact .inr (.terminal terminal (decide_eq_true (by omega)))

/-- This is an existence bridge; its classical choices are deliberately kept
under Nonempty and are not an executable Certificate producer. -/
theorem Forces.certificate_nonempty {n : Nat} {colour : Polarity} {threshold : Int}
    {frame : Frame n} (forced : Forces colour threshold frame) :
    Nonempty (Certificate colour threshold frame) := by
  classical
  induction forced with
  | terminal finished accepted => exact ⟨.terminal finished accepted⟩
  | choose _ owned reply _ ih => exact ⟨.choose owned reply (Classical.choice ih)⟩
  | @all frame playing opponent _ ih =>
      refine ⟨.all playing opponent (fun port => ?_)⟩
      have native := mem_scoringExpansion_iff.mp (List.get_mem (scoringExpansion frame) port)
      exact Classical.choice (ih _ _ native.2 native.1)

theorem Forces.incompatible {n : Nat} {lower upper : Int} {frame : Frame n}
    (black : Forces .positive lower frame) (white : Forces .negative upper frame)
    (separated : upper < lower) : False := by
  obtain ⟨blackCertificate⟩ := black.certificate_nonempty
  obtain ⟨whiteCertificate⟩ := white.certificate_nonempty
  let scoring := black.scoring
  have lowerBound := blackCertificate.guarantee scoring whiteCertificate.policy
  have upperBound := whiteCertificate.guarantee scoring blackCertificate.policy
  have same : versus .positive blackCertificate.policy whiteCertificate.policy =
      versus .negative whiteCertificate.policy blackCertificate.policy := by
    funext colour
    cases colour <;> rfl
  rw [same] at lowerBound
  simp only [acceptsMargin, decide_eq_true_eq] at lowerBound upperBound
  omega

theorem acceptsMargin_swap (colour : Polarity) (threshold margin : Int) :
    acceptsMargin colour.other (-threshold) (-margin) = acceptsMargin colour threshold margin := by
  cases colour <;> simp [acceptsMargin]

theorem Forces.swap {n : Nat} {colour : Polarity} {threshold : Int} {frame : Frame n}
    (forced : Forces colour threshold frame) :
    Forces colour.other (-threshold) (swapFrame frame) := by
  induction forced with
  | terminal finished accepted =>
      apply Forces.terminal
      · change swapStatus _ = _
        rw [finished]
        rfl
      · change acceptsMargin colour.other (-threshold) (areaMargin (swapBoard _)) = true
        rw [areaMargin_swap, acceptsMargin_swap]
        exact accepted
  | choose playing owned reply _ ih =>
      apply Forces.choose (by change swapStatus _ = _; rw [playing]; rfl)
        (by simpa only [swapFrame, swapVisible] using congrArg Polarity.other owned)
        ⟨reply.move, swapFrame reply.target, reply.notResign, legalStep_swap reply.step⟩ ih
  | @all frame playing opponent _ ih =>
      apply Forces.all (by change swapStatus _ = _; rw [playing]; rfl)
      · intro same
        apply opponent
        have reflected := congrArg Polarity.other same
        simpa [swapFrame, swapVisible] using reflected
      · intro move target notResign step
        have back := legalStep_swap step
        rw [swapFrame_involutive] at back
        simpa using ih move (swapFrame target) notResign back

theorem Forces.of_same_face {n : Nat} {colour : Polarity} {threshold : Int} {left : Frame n}
    (forced : Forces colour threshold left) {right : Frame n}
    (same : PositionFace.read left = PositionFace.read right) : Forces colour threshold right := by
  induction forced generalizing right with
  | terminal finished accepted =>
      have visible := congrArg PositionFace.State.visible same
      dsimp only [PositionFace.read] at visible
      exact .terminal (by rw [← visible]; exact finished) (by rw [← visible]; exact accepted)
  | choose playing owned reply _ ih =>
      have visible := congrArg PositionFace.State.visible same
      dsimp only [PositionFace.read] at visible
      obtain ⟨target, step, nextSame⟩ := PositionFace.legalStep_lift same reply.step
      exact .choose (by rw [← visible]; exact playing) (by rw [← visible]; exact owned)
        ⟨reply.move, target, reply.notResign, step⟩ (ih nextSame)
  | all playing opponent _ ih =>
      have visible := congrArg PositionFace.State.visible same
      dsimp only [PositionFace.read] at visible
      apply Forces.all (by rw [← visible]; exact playing) (by rw [← visible]; exact opponent)
      intro move target notResign step
      obtain ⟨previous, previousStep, nextSame⟩ := PositionFace.legalStep_lift same.symm step
      exact ih move previous notResign previousStep nextSame.symm

theorem Forces.terminal_accepted {n : Nat} {colour : Polarity} {threshold : Int} {frame : Frame n}
    (forced : Forces colour threshold frame)
    (finished : frame.visible.status = .terminal .twoPasses) :
    acceptsMargin colour threshold (areaMargin frame.visible.board) = true := by
  cases forced with
  | terminal _ accepted => exact accepted
  | choose playing _ _ _ => rw [playing] at finished; contradiction
  | all playing _ _ => rw [playing] at finished; contradiction

def openingPass (n : Nat) : ScoringReply (Frame.initial n) := passReply (Frame.initial n) rfl

def resetPasses {n : Nat} (frame : Frame n) : Frame n :=
  {frame with visible := {frame.visible with consecutivePasses := 0}}

theorem nativePlay_resetPasses {n : Nat} (frame : Frame n) (point : Point n) :
    nativeStep? (Law.positionalSuperko 0) (resetPasses frame) (.play point) =
      nativeStep? (Law.positionalSuperko 0) frame (.play point) := rfl

/-- The duplicate initial empty situation disappears only on the positional
calculation face; the real pass and its original history remain present. -/
theorem openingPass_reset_swap_face (n : Nat) :
    PositionFace.read (resetPasses (swapFrame (openingPass n).target)) =
      PositionFace.read (Frame.initial n) := by
  simp [PositionFace.read, resetPasses, swapFrame, swapVisible, swapStatus, openingPass,
    passReply, Frame.advance, Frame.initial, VisiblePosition.situation, swapSituation,
    ← boardSignature_swap]

/-- A supposed strictly winning White continuation cannot survive the actual
Black pass and the original colour-swapped first placement. -/
theorem initial_not_white_negative (n : Nat) :
    ¬ Forces .negative (-1) (Frame.initial n) := by
  intro white
  cases white with
  | terminal finished _ => cases finished
  | choose _ owned _ _ => cases owned
  | all _ _ allBlack =>
      have afterPass := allBlack .pass (openingPass n).target (by intro same; cases same) (openingPass n).step
      cases afterPass with
      | terminal finished _ => cases finished
      | all _ opponent _ => exact opponent rfl
      | choose _ _ reply afterWhite =>
          cases emitted : reply.move with
          | resign => exact reply.notResign emitted
          | pass =>
              have step : LegalStep (Law.positionalSuperko 0) (openingPass n).target .pass reply.target := by
                rw [← emitted]
                exact reply.step
              have facts := pass_step_facts step
              have terminal : reply.target.visible.status = .terminal .twoPasses := by
                simpa [openingPass, passReply, Frame.advance, Frame.initial] using facts.2.2.2
              have score : areaMargin reply.target.visible.board = 0 := by
                rw [facts.2.1]
                exact areaMargin_empty n
              have accepted := afterWhite.terminal_accepted terminal
              simp [acceptsMargin, score] at accepted
          | play point =>
              have reflected : LegalStep (Law.positionalSuperko 0)
                  (swapFrame (openingPass n).target) (.play point) (swapFrame reply.target) := by
                rw [← emitted]
                exact legalStep_swap reply.step
              have resetStep : LegalStep (Law.positionalSuperko 0)
                  (resetPasses (swapFrame (openingPass n).target)) (.play point)
                  (swapFrame reply.target) := by
                change nativeStep? _ _ _ = _
                rw [nativePlay_resetPasses]
                exact reflected
              obtain ⟨target, originalStep, same⟩ :=
                PositionFace.legalStep_lift (openingPass_reset_swap_face n) resetStep
              have blackAtTarget : Forces .positive 1 target := by
                exact afterWhite.swap.of_same_face same
              have whiteAtTarget := allBlack (.play point) target (by intro same; cases same) originalStep
              exact blackAtTarget.incompatible whiteAtTarget (by decide)

/-- A premise-free initial lower bound in Prop. The proof uses classical finite
determinacy; no executable Certificate value is extracted here. -/
theorem initial_nonnegative_certificate (n : Nat) :
    Nonempty (Certificate .positive 0 (Frame.initial n)) := by
  rcases forcing_dichotomy n (-1) (Frame.initial n) (.inl rfl) with white | black
  · exact False.elim (initial_not_white_negative n white)
  · exact black.certificate_nonempty

theorem initial_nonnegative_policy :
    ∃ black : ExecutablePolicy 19, ∀ opponent : ExecutablePolicy 19,
      0 ≤ areaMargin (initialPlay 19 (versus .positive black opponent)).replay.final.visible.board := by
  obtain ⟨certificate⟩ := initial_nonnegative_certificate 19
  refine ⟨certificate.policy, fun opponent => ?_⟩
  simpa only [initialPlay, acceptsMargin, decide_eq_true_eq] using
    certificate.guarantee (.inl rfl) opponent

/-- Mathematical bounds on the exact original value, independently of which
unilateral strategy data the running calculation has already materialized. -/
theorem exact_value_bounds (solution : ExactInitialMargin) :
    0 ≤ solution.value ∧ solution.value ≤ 361 := by
  obtain ⟨black, nonnegative⟩ := initial_nonnegative_policy
  have same : versus .negative solution.white black = versus .positive black solution.white := by
    funext colour
    cases colour <;> simp only [versus, reduceCtorEq, if_false, if_true]
  have ceiling := solution.white_guarantee black
  rw [same] at ceiling
  have lower := Int.le_trans (nonnegative solution.white) ceiling
  have guaranteed := solution.black_guarantee (passPolicy 19)
  have area := TwoEye.Score.white_margin_bound
    (initialPlay 19 (versus .positive solution.black (passPolicy 19))).replay.final.visible.board
    0 (Nat.zero_le _)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero] at area
  exact ⟨lower, Int.le_trans guaranteed area⟩

end SaturationMonoid.ProcessGame.Go.CriticalKomi.InitialColourPass
