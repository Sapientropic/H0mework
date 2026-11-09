import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Step

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "W" => Window Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)

def Checked (origin : C) (command : List Party) (community : Party → Community) (civil : Bool) :
    W → Word → Prop
  | _, [] => True
  | window, input :: rest =>
      StepGood origin command community civil window input ∧ Checked origin command community civil (window.write input) rest

/-- This is the first failing original input, with its checked prefix and
the precise cut it consumed. The unexecuted suffix carries no authority. -/
structure FirstFailure (origin : C) (command : List Party) (community : Party → Community) (civil : Bool)
    (window : W) (word : Word) where
  before : Word
  input : Input
  after : Word
  split : word = before ++ input :: after
  earlier : Checked origin command community civil window before
  issue : StepFailure origin command community civil (window.run before) input

theorem checked_append (origin : C) (command : List Party) (community : Party → Community)
    (civil : Bool) (window : W) (first second : Word) :
    Checked origin command community civil window (first ++ second) ↔
      Checked origin command community civil window first ∧
        Checked origin command community civil (window.run first) second := by
  induction first generalizing window with
  | nil => simp only [List.nil_append, Checked, Window.run, true_and]
  | cons input rest ih =>
    simp only [List.cons_append, Checked, Window.run, ih, and_assoc]

theorem FirstFailure.refutes {origin : C} {command : List Party} {community : Party → Community}
    {civil : Bool} {window : W} {word : Word} (first : FirstFailure origin command community civil window word) :
    ¬ Checked origin command community civil window word := by
  intro claimed
  rw [first.split, checked_append] at claimed
  exact first.issue.refutes claimed.2.1

theorem FirstFailure.original_write {origin : C} {command : List Party} {community : Party → Community}
    {civil : Bool} {window : W} {word : Word} (first : FirstFailure origin command community civil window word) :
    Quantities.Recorded window.current (first.before ++ [first.input]) ∧
      Evolving.Epoch.Current.ClosedAt (Quantities.Execution.query (window.run first.before).current first.input) :=
  ⟨Quantities.record _ _, Quantities.Execution.actual_step _ _⟩

def inspectSegment (origin : C) (command : List Party) (community : Party → Community) (civil : Bool) :
    (window : W) → (word : Word) →
    FirstFailure origin command community civil window word ⊕ PLift (Checked origin command community civil window word)
  | _, [] => .inr ⟨trivial⟩
  | window, input :: rest =>
    match inspectStep origin command community civil window input with
    | .inl issue => .inl ⟨[], input, rest, rfl, trivial, issue⟩
    | .inr accepted =>
      match inspectSegment origin command community civil (window.write input) rest with
      | .inl failure =>
        .inl ⟨input :: failure.before, failure.input, failure.after,
          congrArg (List.cons input) failure.split, ⟨accepted.down, failure.earlier⟩, failure.issue⟩
      | .inr later => .inr ⟨⟨accepted.down, later.down⟩⟩

/-- The defender gets one finite intervention at its observed cut. The
rival can submit any finite original continuation, even one crossing
several due periods. Every intervening cut is checked. -/
structure RoundGood (origin : C) (command : List Party) (community : Party → Community)
    (window : W) (move reply : Word) : Prop where
  residents : window.residents origin command ≠ []
  own : Checked origin command community true window move
  renewal : window.current.raw.clock < (window.run move).current.raw.clock
  reply : Checked origin command community false (window.run move) reply

inductive RoundFailure (origin : C) (command : List Party) (community : Party → Community)
    (window : W) (move reply : Word)
  | noCivilian (empty : window.residents origin command = [])
  | intervention (failed : FirstFailure origin command community true window move)
  | noRenewal (own : Checked origin command community true window move)
      (clock : ¬ window.current.raw.clock < (window.run move).current.raw.clock)
  | counter (own : Checked origin command community true window move)
      (renewal : window.current.raw.clock < (window.run move).current.raw.clock)
      (failed : FirstFailure origin command community false (window.run move) reply)

theorem RoundFailure.refutes {origin : C} {command : List Party} {community : Party → Community}
    {window : W} {move reply : Word} (issue : RoundFailure origin command community window move reply) :
    ¬ RoundGood origin command community window move reply := by
  intro good
  cases issue with
  | noCivilian empty => exact good.residents empty
  | intervention failed => exact failed.refutes good.own
  | noRenewal _ clock => exact clock good.renewal
  | counter _ _ failed => exact failed.refutes good.reply

def inspectRound (origin : C) (command : List Party) (community : Party → Community)
    (window : W) (move reply : Word) :
    RoundFailure origin command community window move reply ⊕ PLift (RoundGood origin command community window move reply) :=
  if empty : window.residents origin command = [] then .inl (.noCivilian empty)
  else match inspectSegment origin command community true window move with
  | .inl issue => .inl (.intervention issue)
  | .inr own =>
    if renewed : window.current.raw.clock < (window.run move).current.raw.clock then
      match inspectSegment origin command community false (window.run move) reply with
      | .inl issue => .inl (.counter own.down renewed issue)
      | .inr later => .inr ⟨⟨empty, own.down, renewed, later.down⟩⟩
    else .inl (.noRenewal own.down renewed)

def RoundFailure.consumed {origin : C} {command : List Party} {community : Party → Community}
    {window : W} {move reply : Word} (issue : RoundFailure origin command community window move reply) : Word :=
  match issue with
  | .noCivilian _ => []
  | .intervention failed => failed.before ++ [failed.input]
  | .noRenewal .. => move
  | .counter _ _ failed => move ++ failed.before ++ [failed.input]

theorem RoundFailure.consumed_is_original_prefix {origin : C} {command : List Party} {community : Party → Community}
    {window : W} {move reply : Word} (issue : RoundFailure origin command community window move reply) :
    ∃ pending, move ++ reply = issue.consumed ++ pending := by
  cases issue with
  | noCivilian empty => exact ⟨move ++ reply, rfl⟩
  | intervention failed =>
    refine ⟨failed.after ++ reply, ?_⟩
    change move ++ reply = (failed.before ++ [failed.input]) ++ (failed.after ++ reply)
    calc
      move ++ reply = (failed.before ++ failed.input :: failed.after) ++ reply :=
        congrArg (fun word => word ++ reply) failed.split
      _ = _ := by simp only [List.append_assoc, List.cons_append, List.nil_append]
  | noRenewal _ _ => exact ⟨reply, rfl⟩
  | counter own renewal failed =>
    refine ⟨failed.after, ?_⟩
    change move ++ reply = (move ++ failed.before ++ [failed.input]) ++ failed.after
    calc
      move ++ reply = move ++ (failed.before ++ failed.input :: failed.after) :=
        congrArg (fun word => move ++ word) failed.split
      _ = _ := by simp only [List.append_assoc, List.singleton_append]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
