import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Response
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Response

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (input : BoundSource base scope)

/-- The continuation changes the original decision branch, not a projection
of an already-emitted empty word. Law, seed task and first-payment fold stay
in the same Outstanding source. -/
def source : OutstandingSource Party Good Port (State Party Technology) Instrument :=
  {input.source with completionReport := fun current => (produce base scope current).report}

def bound : BoundSource base scope := ⟨source input, input.law_exact⟩

theorem original_seed_is_preserved : (source input).seed = input.source.seed := rfl

structure ActualResponse (depth : Nat) where
  private mk ::
  outcome : Outcome base scope ((source input).currentAt (depth + 1))
  produced : outcome = produce base scope ((source input).currentAt (depth + 1))
  complete : (source input).pendingSlots ((source input).frameAt (depth + 1)).payments = []
  quiet : (source input).incoming? ((source input).currentAt (depth + 1)) = none
  actual_word : ((source input).actualExecution depth).submitted = outcome.word
  actual_report : ((source input).writtenReceipt depth).val = outcome.report

def actualAt (depth : Nat) : Option (ActualResponse input depth) :=
  if started : 2 ≤ depth + 1 then
    match quiet : (source input).incoming? ((source input).currentAt (depth + 1)) with
    | some _ => none
    | none =>
      if complete : (source input).pendingSlots ((source input).frameAt (depth + 1)).payments = [] then
        some {
          outcome := produce base scope ((source input).currentAt (depth + 1))
          produced := rfl
          complete := complete
          quiet := quiet
          actual_word := by
            rw [(source input).actual_execution_word,
              ← ((source input).canonical_frame (depth + 1)).2]
            exact (source input).completed_word_is_source_continuation (depth + 1) 0 started complete quiet
          actual_report := by
            rw [(source input).written_report_exact]
            unfold OutstandingSource.reportAt
            rw [(source input).ordinal_exact, if_neg (by omega)]
            unfold OutstandingSource.decideAt
            rw [quiet, dif_pos complete]
            rfl }
      else none
  else none

theorem complete_generates_actual_response (depth : Nat) (started : 2 ≤ depth + 1)
    (complete : (source input).pendingSlots ((source input).frameAt (depth + 1)).payments = [])
    (quiet : (source input).incoming? ((source input).currentAt (depth + 1)) = none := by rfl) :
    ∃ response, actualAt input depth = some response := by
  unfold actualAt
  rw [dif_pos started]
  split
  · rename_i supplied generated
    rw [quiet] at generated
    cases generated
  · rw [dif_pos complete]
    exact ⟨_, rfl⟩

theorem active_complete_emits_actual_attempt (depth : Nat) (started : 2 ≤ depth + 1)
    (complete : (source input).pendingSlots ((source input).frameAt (depth + 1)).payments = [])
    (active : Active ((source input).currentAt (depth + 1)))
    (quiet : (source input).incoming? ((source input).currentAt (depth + 1)) = none := by rfl) :
    ∃ actor ∈ Delegation.members scope.task,
      ((source input).actualExecution depth).submitted =
        [request scope ((source input).currentAt (depth + 1)) actor .revoke] := by
  obtain ⟨response, _⟩ := complete_generates_actual_response input depth started complete quiet
  obtain ⟨actor, member, emitted⟩ := response.outcome.active_emits_an_actual_attempt active
  exact ⟨actor, member, response.actual_word.trans emitted⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Response
