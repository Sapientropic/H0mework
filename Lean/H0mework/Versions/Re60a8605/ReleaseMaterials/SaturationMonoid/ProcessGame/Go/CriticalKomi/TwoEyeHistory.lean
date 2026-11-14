import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyePreservation
import Mathlib.Data.List.GetD

/-!
History reduction from the source-generated two-eye core.  The actual replay
is retained; this filter is a calculation reader for positional superko.
Malformed historical signatures need no validity premise: any signature equal
to a compatible candidate is itself compatible.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye.History

def signatureCell {n : Nat} (signature : BoardSignature n) (point : Point n) :
    Option Polarity :=
  (signature.getD point.1.val []).getD point.2.val none

theorem signatureCell_boardSignature {n : Nat} (board : Board n) (point : Point n) :
    signatureCell (boardSignature board) point = board point := by
  unfold signatureCell boardSignature
  rw [List.getD_eq_getElem _ [] (by simp)]
  simp only [List.getElem_ofFn]
  rw [List.getD_eq_getElem _ none (by simp)]
  simp only [List.getElem_ofFn]

def Compatible {n : Nat} (g : Geometry n) (colour : Polarity)
    (signature : BoardSignature n) : Prop :=
  ∀ point ∈ g.core, signatureCell signature point = some colour

instance {n : Nat} (g : Geometry n) (colour : Polarity) (signature : BoardSignature n) :
    Decidable (Compatible g colour signature) :=
  inferInstanceAs (Decidable (∀ point ∈ g.core, signatureCell signature point = some colour))

theorem compatible_signature {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (core : ∀ point ∈ g.core, board point = some colour) :
    Compatible g colour (boardSignature board) := by
  intro point member
  rw [signatureCell_boardSignature]
  exact core point member

theorem compatible_of_holds {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (inside : Holds g colour board) :
    Compatible g colour (boardSignature board) :=
  compatible_signature (fun _point member => core_colour inside member)

def filterHistory {n : Nat} (g : Geometry n) (colour : Polarity)
    (history : List (Situation n)) : List (Situation n) :=
  history.filter (fun previous => decide (Compatible g colour previous.board))

/-- Exact original guard, with no validity assumption on any old signature. -/
theorem repetition_filter {n : Nat} (g : Geometry n) (colour : Polarity)
    (history : List (Situation n)) (next : Situation n)
    (compatible : Compatible g colour next.board) :
    violatesRepetition .positionalSuperko history next ↔
      violatesRepetition .positionalSuperko (filterHistory g colour history) next := by
  constructor
  · rintro ⟨previous, member, same⟩
    refine ⟨previous, List.mem_filter.mpr ⟨member, ?_⟩, same⟩
    apply decide_eq_true_eq.mpr
    rw [same]
    exact compatible
  · rintro ⟨previous, member, same⟩
    exact ⟨previous, (List.mem_filter.mp member).1, same⟩

theorem repetition_filter_of_holds {n : Nat} {g : Geometry n} {colour : Polarity}
    (history : List (Situation n)) {board : Board n} (toMove : Polarity)
    (inside : Holds g colour board) :
    violatesRepetition .positionalSuperko history ⟨boardSignature board, toMove⟩ ↔
      violatesRepetition .positionalSuperko (filterHistory g colour history)
        ⟨boardSignature board, toMove⟩ :=
  repetition_filter g colour history _ (compatible_of_holds inside)

/-- The actual two-eye source theorem supplies the candidate's retained core.
This stronger guard equality already holds before the suicide test. -/
theorem opponent_repetition_filter {n : Nat} {g : Geometry n} {colour : Polarity}
    {board : Board n} (inside : Holds g colour board) (played : Point n)
    (empty : board played = none) (history : List (Situation n)) (toMove : Polarity) :
    violatesRepetition .positionalSuperko history
      ⟨boardSignature (boardAfterPlay board colour.other played), toMove⟩ ↔
    violatesRepetition .positionalSuperko (filterHistory g colour history)
      ⟨boardSignature (boardAfterPlay board colour.other played), toMove⟩ :=
  repetition_filter g colour history _
    (compatible_signature (fun _point member => core_survives inside played empty member))

def filteredFrame {n : Nat} (g : Geometry n) (colour : Polarity) (frame : Frame n) :
    Frame n :=
  {frame with positionHistory := filterHistory g colour frame.positionHistory}

/-- A newly generated compatible board is retained, so paid history filtering
commutes with the original history append. -/
theorem filterHistory_append {n : Nat} (g : Geometry n) (colour : Polarity)
    (history : List (Situation n)) (next : Situation n)
    (compatible : Compatible g colour next.board) :
    filterHistory g colour (history ++ [next]) =
      filterHistory g colour history ++ [next] := by
  simp [filterHistory, compatible]

theorem filteredFrame_advance {n : Nat} (g : Geometry n) (colour : Polarity)
    (frame : Frame n) (next : VisiblePosition n)
    (compatible : Compatible g colour (boardSignature next.board)) :
    filteredFrame g colour (frame.advance next) =
      (filteredFrame g colour frame).advance next := by
  unfold filteredFrame Frame.advance
  congr 1
  exact filterHistory_append g colour frame.positionHistory next.situation compatible

/-- Local candidate-board condition for either polarity's selected placement. -/
theorem playVisible_filter_of_compatible {n : Nat} (g : Geometry n) (colour : Polarity)
    (frame : Frame n) (played : Point n)
    (compatible : Compatible g colour
      (boardSignature (boardAfterPlay frame.visible.board frame.visible.toMove played))) :
    playVisible? (Law.positionalSuperko 0) frame played =
      playVisible? (Law.positionalSuperko 0) (filteredFrame g colour frame) played := by
  have guard := repetition_filter g colour frame.positionHistory
    ⟨boardSignature (boardAfterPlay frame.visible.board frame.visible.toMove played),
      frame.visible.toMove.other⟩ compatible
  simp only [playVisible?, filteredFrame, Law.positionalSuperko, guard]
  rfl

/-- All opponent placements use the same reduced guard; no move is selected here. -/
theorem opponent_playVisible_filter {n : Nat} {g : Geometry n} {colour : Polarity}
    (frame : Frame n) (inside : Holds g colour frame.visible.board)
    (opponent : frame.visible.toMove = colour.other) (played : Point n) :
    playVisible? (Law.positionalSuperko 0) frame played =
      playVisible? (Law.positionalSuperko 0) (filteredFrame g colour frame) played := by
  by_cases empty : frame.visible.board played = none
  · apply playVisible_filter_of_compatible
    rw [opponent]
    exact compatible_signature (fun _point member => core_survives inside played empty member)
  · simp only [playVisible?, filteredFrame]
    cases frame.visible.status <;> simp [empty]

/-- Own selected target preservation is a local source fact and uses the same guard theorem. -/
theorem retained_playVisible_filter {n : Nat} {g : Geometry n} {colour : Polarity}
    (frame : Frame n) (played : Point n)
    (after : Holds g colour
      (boardAfterPlay frame.visible.board frame.visible.toMove played)) :
    playVisible? (Law.positionalSuperko 0) frame played =
      playVisible? (Law.positionalSuperko 0) (filteredFrame g colour frame) played :=
  playVisible_filter_of_compatible g colour frame played (compatible_of_holds after)

theorem opponent_stepVisible_filter {n : Nat} {g : Geometry n} {colour : Polarity}
    (frame : Frame n) (inside : Holds g colour frame.visible.board)
    (opponent : frame.visible.toMove = colour.other) (move : Move n) :
    stepVisible? (Law.positionalSuperko 0) frame move =
      stepVisible? (Law.positionalSuperko 0) (filteredFrame g colour frame) move := by
  cases move with
  | play played => exact opponent_playVisible_filter frame inside opponent played
  | pass => simp [stepVisible?, passVisible?, filteredFrame, Law.positionalSuperko]
  | resign => rfl

/-- Whole native successor computation commutes for every legal-opponent
play/pass option.  The source-owned two-eye theorem also pays the retained
target-board condition used by the incremental history append. -/
theorem opponent_nativeStep_filter {n : Nat} {g : Geometry n} {colour : Polarity}
    (frame : Frame n) (inside : Holds g colour frame.visible.board)
    (opponent : frame.visible.toMove = colour.other) (move : Move n)
    (scoring : move ≠ .resign) :
    (nativeStep? (Law.positionalSuperko 0) frame move).map (filteredFrame g colour) =
      nativeStep? (Law.positionalSuperko 0) (filteredFrame g colour frame) move := by
  unfold nativeStep?
  rw [← opponent_stepVisible_filter frame inside opponent move]
  cases emitted : stepVisible? (Law.positionalSuperko 0) frame move with
  | none => rfl
  | some next =>
      simp only [Option.map_some]
      have step : LegalStep (Law.positionalSuperko 0) frame move (frame.advance next) := by
        simp [LegalStep, nativeStep?, emitted]
      have preserved := opponent_legalStep_preserves inside opponent scoring step
      have compatible : Compatible g colour (boardSignature next.board) :=
        compatible_of_holds preserved
      exact congrArg some (filteredFrame_advance g colour frame next compatible)

private theorem played_target_board {n : Nat} {frame target : Frame n} {played : Point n}
    (step : LegalStep (Law.positionalSuperko 0) frame (.play played) target) :
    boardAfterPlay frame.visible.board frame.visible.toMove played = target.visible.board := by
  have visible := nativeStep_visible_eq step
  simp only [stepVisible?, playVisible?] at visible
  split at visible
  · simp at visible
  · split at visible
    · split at visible
      · split at visible
        · simp at visible
        · exact congrArg VisiblePosition.board (Option.some.inj visible)
      · simp at visible
    · simp at visible

/-- Any selected native action whose actual target retains the source core
can use the filtered history, regardless of which polarity selected it. -/
theorem retained_nativeStep_filter {n : Nat} {g : Geometry n} {colour : Polarity}
    {frame target : Frame n} {move : Move n}
    (step : LegalStep (Law.positionalSuperko 0) frame move target)
    (after : Holds g colour target.visible.board) :
    nativeStep? (Law.positionalSuperko 0) (filteredFrame g colour frame) move =
      some (filteredFrame g colour target) := by
  have visibleFilter : stepVisible? (Law.positionalSuperko 0) frame move =
      stepVisible? (Law.positionalSuperko 0) (filteredFrame g colour frame) move := by
    cases move with
    | play played =>
        apply playVisible_filter_of_compatible
        rw [played_target_board step]
        exact compatible_of_holds after
    | pass => simp [stepVisible?, passVisible?, filteredFrame, Law.positionalSuperko]
    | resign => rfl
  have filteredVisible := visibleFilter.symm.trans (nativeStep_visible_eq step)
  have targetEq : frame.advance target.visible = target := by
    have history := nativeStep_positionHistory_eq step
    cases target with
    | mk visible positionHistory =>
        unfold Frame.advance
        congr 1
        exact history.symm
  unfold nativeStep?
  rw [filteredVisible, Option.map_some, ← filteredFrame_advance g colour frame
    target.visible (compatible_of_holds after), targetEq]

end SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEye.History
