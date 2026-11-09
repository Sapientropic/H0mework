import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.ExitCounterexample
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Batch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {Observation : Type u}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "W" => Window Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "P" => Position Party Good Port Technology Instrument Observation
local notation "Strategy" => History Observation → Word
local notation "endAt" => Quantities.Execution.endAt

abbrev OriginalAttack (seed : C) (community : Party → Community) (word : Word) :=
  { row : Reparation.Actual.Occurrence seed community // word = row.past ++ [row.input] }

def FirstFailure.originalAttack {seed : C} {command : List Party} {community : Party → Community}
    {civil : Bool} {window : W} {word : Word}
    (first : FirstFailure seed command community civil window word) (past : Word)
    (same : window.current = endAt seed past) :
    Option (OriginalAttack seed community (past ++ (first.before ++ [first.input]))) :=
  match first.issue with
  | .attack damage =>
    have actual : (window.run first.before).current = endAt seed (past ++ first.before) :=
      (Window.run_current window first.before).trans (by rw [same, Quantities.Execution.endAt_append])
    some ⟨⟨past ++ first.before, first.input, actual ▸ damage⟩, (List.append_assoc _ _ _).symm⟩
  | _ => none

theorem FirstFailure.an_attack_is_located {seed : C} {command : List Party} {community : Party → Community}
    {civil : Bool} {window : W} {word : Word}
    (first : FirstFailure seed command community civil window word) (past : Word)
    (same : window.current = endAt seed past)
    (damage : Boundary.Actual.DamageAt (window.run first.before).current first.input community)
    (issue : first.issue = .attack damage) :
    (first.originalAttack past same).isSome = true := by
  simp only [FirstFailure.originalAttack, issue, Option.isSome_some]

def RoundFailure.originalAttack {seed : C} {command : List Party} {community : Party → Community}
    {window : W} {move reply : Word} (issue : RoundFailure seed command community window move reply)
    (past : Word) (same : window.current = endAt seed past) :
    Option (OriginalAttack seed community (past ++ issue.consumed)) := by
  cases issue with
  | noCivilian _ => exact none
  | noRenewal _ _ => exact none
  | intervention first => exact first.originalAttack past same
  | counter _ _ first =>
    have actual : (window.run move).current = endAt seed (past ++ move) :=
      (Window.run_current window move).trans (by rw [same, Quantities.Execution.endAt_append])
    simpa only [RoundFailure.consumed, List.append_assoc] using first.originalAttack (past ++ move) actual

def FailureWithExit.originalAttack {seed : C} {command : List Party} {community : Party → Community}
    {position : P} {move reply : Word} (issue : FailureWithExit seed command community position move reply)
    (past : Word) (same : position.window.current = endAt seed past) :
    Option (OriginalAttack seed community (past ++ issue.consumed)) :=
  match issue with
  | .actual failed => failed.originalAttack past same
  | .exit failed => failed.originalAttack past same

/-- The original debit belongs to the exact seed prefix at which the
strategy first failed. Its native item and harmed address are inherited. -/
def FirstFailureWithExit.originalAttack {seed : C} {command : List Party} {community : Party → Community}
    {read : C → Observation} {strategy : Strategy} {rival : List Word}
    (first : FirstFailureWithExit seed command community read strategy rival) :
    Option (OriginalAttack seed community first.originalScript) :=
  first.failure.originalAttack _ (play_is_the_original_execution seed read strategy (submitted rival) first.round)

theorem OriginalAttack.is_in_the_original_openings {seed : C} {community : Party → Community} {word : Word}
    (attack : OriginalAttack seed community word) :
    attack.val ∈ Reparation.Actual.openings seed community attack.val.past attack.val.input :=
  List.mem_map.mpr ⟨attack.val.damage, Boundary.Actual.every_actual_debit_is_assessed _, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
