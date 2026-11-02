import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.History

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : Code Party Good Port (Mandate.State Party Technology) Instrument) (capacity : Nat)

/-- Only the original action grammar and ownership are premises; no successful trajectory is input. -/
structure Strategy where
  work : Fin base.sites → List (Notice base) → RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  supported : ∀ site history, history ∈ memories base capacity →
    work site history ∈ words base.actions base.actionLimit
  event : (site : Fin base.sites) → List (Notice base) → LocalMove (lift base capacity) site

def tabulate (strategy : Strategy base capacity) : Rule (lift base capacity) where
  work := ⟨Recall.tabulate base capacity strategy.work,
    every_supported_history_programme_is_actually_tabulated base capacity strategy.work strategy.supported⟩
  events := fun key _ => match decode base capacity key.2 with
    | none => ⟨none,List.mem_cons_self⟩
    | some history => strategy.event key.1 history

theorem every_complete_local_strategy_is_generated (strategy : Strategy base capacity) :
    tabulate base capacity strategy ∈ rules (lift base capacity) :=
  every_rule_is_source_generated _ _

/-- Recover the selected rule's complete-history programme without rerunning a planner. -/
def reify (rule : Rule (lift base capacity)) : Strategy base capacity where
  work := fun site history => rule.work.val (site,encode base capacity history) ((lift base capacity).key_mem _)
  supported := fun _ _ _ => (List.mem_pi _ _).mp rule.work.property _ ((lift base capacity).key_mem _)
  event := fun site history => rule.events (site,encode base capacity history) ((lift base capacity).key_mem _)

theorem tabulated_event_reads_the_entire_local_history (strategy : Strategy base capacity)
    (site : Fin base.sites) (history : List (Notice base)) (generated : history ∈ memories base capacity) :
    localEvent (lift base capacity) (tabulate base capacity strategy) site (encode base capacity history) =
      (strategy.event site history).val := by
  simp only [localEvent,tabulate,decode_encode base capacity history generated]

theorem tabulated_work_reads_the_entire_local_history (strategy : Strategy base capacity)
    (site : Fin base.sites) (history : List (Notice base)) (generated : history ∈ memories base capacity) :
    (lift base capacity).action (tabulate base capacity strategy).work.val site (encode base capacity history) =
      strategy.work site history :=
  tabulated_programme_reads_the_complete_actual_history base capacity strategy.work site history generated

theorem every_selected_rule_is_its_own_complete_history_programme (rule : Rule (lift base capacity))
    (site : Fin base.sites) (history : List (Notice base)) (generated : history ∈ memories base capacity) :
    localEvent (lift base capacity) (tabulate base capacity (reify base capacity rule)) site (encode base capacity history) =
      localEvent (lift base capacity) rule site (encode base capacity history) ∧
    (lift base capacity).action (tabulate base capacity (reify base capacity rule)).work.val site (encode base capacity history) =
      (lift base capacity).action rule.work.val site (encode base capacity history) := by
  constructor
  · exact tabulated_event_reads_the_entire_local_history base capacity _ site history generated
  · rw [tabulated_work_reads_the_entire_local_history base capacity _ site history generated]
    simp only [Code.action,decode_encode base capacity history generated,Option.isSome_some,↓reduceIte,reify]

theorem actual_own_decision_is_the_history_programme (strategy : Strategy base capacity)
    (start : Nat) (rival : Opponent (lift base capacity)) (past : Events (lift base capacity))
    (history : Reaction.History) (frame : (lift base capacity).Frame) (site : Fin base.sites)
    (owned : ownerAt (lift base capacity) start history.length = some site)
    (localHistory : List (Notice base)) (generated : localHistory ∈ memories base capacity)
    (observed : frame.inbox site = encode base capacity localHistory) :
    driver (lift base capacity) start (tabulate base capacity strategy) rival history past frame =
      (strategy.event site localHistory).val := by
  simp only [driver,owned,observed]
  exact tabulated_event_reads_the_entire_local_history base capacity strategy site localHistory generated

theorem actual_adaptive_decision_consumes_the_complete_paid_prefix
    (strategy : Strategy base capacity) (schedule : Residual.Schedule (lift base capacity))
    (supported : ∀ n policy, schedule n = some policy → policy ∈ (lift base capacity).policies)
    (input : Input (lift base capacity)) (seed : State (lift base capacity)) (site : Fin base.sites)
    (prior : List (Notice base)) (initial : seed.frame.inbox site = encode base capacity prior)
    (prior_generated : prior ∈ memories base capacity) (n : Nat) (bounded : prior.length+n ≤ capacity)
    (start : Nat) (rival : Opponent (lift base capacity))
    (owned : ownerAt (lift base capacity) start
      (Residual.run (lift base capacity) schedule input seed n).history.length = some site) :
    let actual := Residual.run (lift base capacity) schedule input seed n
    driver (lift base capacity) start (tabulate base capacity strategy) rival actual.history actual.past actual.frame =
      (strategy.event site
        (prior ++ Recall.Feedback.observations base capacity schedule input seed site n)).val := by
  have recall := Recall.Feedback.every_adaptive_cut_keeps_full_local_recall_across_planner_replacement
    base capacity schedule supported input seed site prior initial prior_generated n bounded
  dsimp only
  simp only [driver,owned,localEvent,tabulate,recall]

theorem exhausted_memory_waits_and_cannot_authorize_work (strategy : Strategy base capacity)
    (site : Fin base.sites) :
    localEvent (lift base capacity) (tabulate base capacity strategy) site (overflow base capacity) = none ∧
    (lift base capacity).action (tabulate base capacity strategy).work.val site (overflow base capacity) = [] := by
  constructor
  · simp only [localEvent,tabulate,decode_overflow]
  · exact exhausted_memory_cannot_authorize_further_work base capacity _ site

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.History
