import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Portfolio.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Review

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Mandate.Source (Port)

/-- Outstanding offers are active too. After all current financial words
are empty, the original task still generates a real review request. -/
def completionReport (current : Current) :=
  if Response.Active current then (Response.produce base scope current).report
  else if Portfolio.financialWord current = [] then (Review.produce base scope current).report
  else Portfolio.financialReport current

/-- Keep the generated obstruction evidence as well as its submitted word.
Financial slices use the state after the preceding positions actually run. -/
inductive Completion (current : Current) where
  | private authority (active : Response.Active current)
      (outcome : Response.Outcome base scope current)
      (exact : outcome = Response.produce base scope current)
  | private finance (inactive : ¬ Response.Active current)
      (nonempty : Portfolio.financialWord current ≠ [])
      (outcomes : (index : Fin Portfolio.positions.length) → Repayment.Response law Portfolio.positions[index]
        (Portfolio.slice current index).before)
      (exact : ∀ index, outcomes index = Repayment.respond law Portfolio.positions[index]
        (Portfolio.slice current index).before)
  | private review (inactive : ¬ Response.Active current)
      (quiet : Portfolio.financialWord current = [])
      (outcome : Review.Outcome base scope current)
      (exact : outcome = Review.produce base scope current)

def Completion.report {current : Current} : Completion current →
    ProgrammeSource.ProgrammeReport Bool Good Port (State Bool Unit) Unit
  | .authority _ outcome _ => outcome.report
  | .finance .. => Portfolio.financialReport current
  | .review _ _ outcome _ => outcome.report

def completion (current : Current) : Completion current :=
  if active : Response.Active current then .authority active (Response.produce base scope current) rfl
  else if quiet : Portfolio.financialWord current = [] then
    .review active quiet (Review.produce base scope current) rfl
  else .finance active quiet
    (fun index => Repayment.respond law Portfolio.positions[index] (Portfolio.slice current index).before)
    (fun _ => rfl)

theorem completion_evidence_and_word_have_one_producer (current : Current) :
    (completion current).report = completionReport current := by
  unfold completion completionReport
  split_ifs <;> rfl


def source (fuel : ℚ) : OutstandingSource Bool Good Port (State Bool Unit) Unit :=
  { Portfolio.source fuel with completionReport := completionReport }

def bound (fuel : ℚ) : BoundSource base scope := ⟨source fuel, rfl⟩
abbrev input (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.input (source fuel) inputs
abbrev currentAt (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.currentAt (source fuel) inputs
abbrev actualExecution (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.actualExecution (source fuel) inputs
abbrev trailAt (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.trailAt (source fuel) inputs

theorem zero_financial_genesis (fuel : ℚ) (inputs : List (List Action)) :
    (input fuel inputs).initial.claims = fun _ _ _ => 0 := rfl

theorem completion_always_attempts_authority_finance_or_review (current : Current) :
    (Response.Active current ∧ completionReport current = (Response.produce base scope current).report) ∨
    (¬ Response.Active current ∧ Portfolio.financialWord current ≠ [] ∧
      completionReport current = Portfolio.financialReport current) ∨
    (¬ Response.Active current ∧ Portfolio.financialWord current = [] ∧
      completionReport current = (Review.produce base scope current).report) := by
  unfold completionReport
  split_ifs with active quiet
  · exact Or.inl ⟨active, rfl⟩
  · exact Or.inr (Or.inr ⟨active, quiet, rfl⟩)
  · exact Or.inr (Or.inl ⟨active, quiet, rfl⟩)

theorem completion_word_is_never_empty (current : Current) : (completionReport current).word ≠ [] := by
  rcases completion_always_attempts_authority_finance_or_review current with
    ⟨active, report⟩ | ⟨inactive, nonempty, report⟩ | ⟨inactive, quiet, report⟩
  · rw [report]
    obtain ⟨actor, member, word⟩ := (Response.produce base scope current).active_emits_an_actual_attempt active
    change (Response.produce base scope current).word ≠ []
    rw [word]
    exact List.cons_ne_nil _ _
  · rw [report]; exact nonempty
  · rw [report]; exact List.cons_ne_nil _ _

theorem completed_quiet_phase_really_emits_review
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (quiet : (source fuel).incoming? (currentAt fuel inputs (depth + 2)) = none)
    (inactive : ¬ Response.Active (currentAt fuel inputs (depth + 2)))
    (noFinance : Portfolio.financialWord (currentAt fuel inputs (depth + 2)) = []) :
    (actualExecution fuel inputs (depth + 1)).submitted =
      (Review.produce base scope (currentAt fuel inputs (depth + 2))).word := by
  rw [OutstandingSource.History.residual_is_actually_emitted _ _ depth observed]
  unfold OutstandingSource.decideAt
  rw [quiet, dif_pos complete]
  change (completionReport _).word = _
  rw [completionReport, if_neg inactive, if_pos noFinance]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing

open Institutions.Capitalism.Universal.Root
open Mandate.Source (Port)

theorem residual_report_is_the_actual_original_row
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth) :
    (OutstandingSource.History.writtenReceipt (source fuel) inputs (depth + 1)).val =
      ((source fuel).decideAt (currentAt fuel inputs (depth + 2))
        (trailAt fuel inputs (depth + 2)).frame.payments).report := by
  have own := OutstandingSource.History.own_next_consumes_actual_residual (source fuel) inputs depth observed
  rw [← OutstandingSource.History.actual_payment_update, OutstandingSource.History.actual_next] at own
  exact own

/-- This receipt exists only at an actually emitted completion branch.
The outcome's refusal/repair evidence is retained in the root payload. -/
structure ActualCompletion (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) where
  private mk ::
  observed : inputs.length ≤ depth
  complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = []
  quiet : (source fuel).incoming? (currentAt fuel inputs (depth + 2)) = none
  response : Completion (currentAt fuel inputs (depth + 2))
  exact : response = completion (currentAt fuel inputs (depth + 2))
  actual_word : (actualExecution fuel inputs (depth + 1)).submitted = response.report.word
  actual_report : (OutstandingSource.History.writtenReceipt (source fuel) inputs (depth + 1)).val = response.report

def actualCompletionAt (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) :
    Option (ActualCompletion fuel inputs depth) :=
  if observed : inputs.length ≤ depth then
    if complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [] then
      if quiet : (source fuel).incoming? (currentAt fuel inputs (depth + 2)) = none then
        some ⟨observed, complete, quiet, completion _, rfl, by
          have emitted := OutstandingSource.History.residual_is_actually_emitted (source fuel) inputs depth observed
          unfold OutstandingSource.decideAt at emitted
          rw [quiet, dif_pos complete] at emitted
          exact emitted.trans (congrArg (fun report : ProgrammeSource.ProgrammeReport Bool Good Port (State Bool Unit) Unit => report.word)
            (completion_evidence_and_word_have_one_producer _).symm), by
          have written := residual_report_is_the_actual_original_row fuel inputs depth observed
          unfold OutstandingSource.decideAt at written
          rw [quiet, dif_pos complete] at written
          exact written.trans (completion_evidence_and_word_have_one_producer _).symm⟩
      else none
    else none
  else none

theorem every_actual_completion_retains_its_generated_evidence
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (quiet : (source fuel).incoming? (currentAt fuel inputs (depth + 2)) = none) :
    ∃ response, actualCompletionAt fuel inputs depth = some response := by
  unfold actualCompletionAt
  rw [dif_pos observed, dif_pos complete, dif_pos quiet]
  exact ⟨_, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing
