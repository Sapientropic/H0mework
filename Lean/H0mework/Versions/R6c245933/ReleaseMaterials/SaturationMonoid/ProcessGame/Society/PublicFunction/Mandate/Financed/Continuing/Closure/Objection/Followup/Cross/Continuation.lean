import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Bounds
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Plan

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {fuel : ℚ} {originInputs : List (List Action)}

/-- The original responsibility vocabulary stays fixed while actual input
roots change. Only source-generated factories create stages. -/
structure Stage (original : Claim fuel originInputs) where
  private mk ::
  inputs : List (List Action)
  cut : Cut fuel inputs
  history : History original inputs
  within : history.Within (cut.depth + 2)

def initial (cut : Cut fuel originInputs) (original : Claim fuel originInputs)
    (inside : original.position.ordinal < cut.depth + 2) : Stage original :=
  ⟨originInputs, cut, History.inherit (Followup.through fuel originInputs original (cut.depth + 2)),
    inherit_within _ _ (local_through_within _ _ _ inside (Nat.le_refl _))⟩

variable {original : Claim fuel originInputs}

def emit (stage : Stage original) : List Action :=
  match stage.history with
  | .closed .. => (reply fuel stage.cut.past).word
  | .pending target _ _ =>
      if target.snapshot = stage.cut.past.frame.raw.technology then Response.word stage.cut.past.frame.raw
      else [submission]

def before (stage : Stage original) (word : List Action) := transportHistory stage.cut word stage.history stage.within

def after (stage : Stage original) (word : List Action) :=
  (positionsAt fuel (branchInputs stage.cut word) (stage.cut.depth + 2)).foldl History.receive (before stage word)

def submit (stage : Stage original) (word : List Action) : Stage original :=
  ⟨branchInputs stage.cut word, afterInput stage.cut word, after stage word, by
    apply fold_within _ _ _ (transported_within stage.cut word stage.history stage.within)
    intro position member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    cases same
    change stage.cut.depth + 2 < (branchInputs stage.cut word).length + 2
    rw [branchInputs_length]
    omega⟩

def advance (stage : Stage original) := submit stage (emit stage)

def crossing (stage : Stage original) (word : List Action) :
    (process original).Run stage.history.state.current (submit stage word).history.state.current := by
  have run := visitRun (before stage word) (positionsAt fuel (branchInputs stage.cut word) (stage.cut.depth + 2))
  rw [show (before stage word).state = stage.history.state from
    transport_preserves_the_entire_generated_state stage.cut word stage.history stage.within] at run
  exact run

def run (stage : Stage original) : Nat → Stage original
  | 0 => stage
  | count + 1 => advance (run stage count)

def runChain (stage : Stage original) : (count : Nat) →
    (process original).Run stage.history.state.current (run stage count).history.state.current
  | 0 => .nil
  | count + 1 => (runChain stage count).concatRuns _ (crossing (run stage count) (emit (run stage count)))

def alternate (stage : Stage original) : List (List Action) → Stage original
  | [] => stage
  | word :: tail => alternate (submit (advance stage) word) tail

def alternateChain (stage : Stage original) : (words : List (List Action)) →
    (process original).Run stage.history.state.current (alternate stage words).history.state.current
  | [] => .nil
  | word :: tail =>
      ((crossing stage (emit stage)).concatRuns _ (crossing (advance stage) word)).concatRuns _
        (alternateChain (submit (advance stage) word) tail)

theorem actual_word_uses_its_own_cut (stage : Stage original) (word : List Action) :
    (actualExecution fuel (submit stage word).inputs (stage.cut.depth + 1)).submitted = word ∧
    (actualExecution fuel (submit stage word).inputs (stage.cut.depth + 1)).before = stage.cut.past.frame.raw :=
  ⟨new_input_is_actually_emitted stage.cut word, new_input_uses_the_original_cut stage.cut word⟩

theorem next_is_the_actual_interpreted_effect (stage : Stage original) (word : List Action) :
    (submit stage word).cut.past = stage.cut.past.append word := afterInput_is_the_interpreted_original_cut stage.cut word

theorem original_history_is_prefix_after_every_step (stage : Stage original) (word : List Action) :
    stage.history.state.current.history <+: (submit stage word).history.state.current.history := by
  rw [(crossing stage word).history_eq]
  exact List.prefix_append _ _

theorem finite_recursive_closure_has_the_original_full_run (stage : Stage original) (count : Nat) :
    (run stage count).history.state.current.history = stage.history.state.current.history ++ (runChain stage count).events :=
  (runChain stage count).history_eq

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross
