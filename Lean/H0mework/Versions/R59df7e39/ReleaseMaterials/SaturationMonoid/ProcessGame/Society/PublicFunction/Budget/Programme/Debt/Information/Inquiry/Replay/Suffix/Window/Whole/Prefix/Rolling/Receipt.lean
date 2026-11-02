import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Review.Tensor.Choice
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Assembly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

/-- The local receipt restricts possibilities; it does not identify a private world. -/
theorem the_actual_local_record_generates_its_own_covered_planning_domain
    (views : List (View (code := code))) (actual : View (code := code))
    (covered : Knowledge.Contains views actual) (site : Fin code.sites) :
    Knowledge.Contains (fiber views site (observation actual site)) actual := by
  obtain ⟨representative,inside,matched⟩ := covered
  exact ⟨representative,(mem_fiber _ _ _ _).mpr ⟨inside,matched.faithful.observed site⟩,matched⟩

variable {fuel : Nat}
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- A planner consumes public possibilities and returns the original full selection contract. -/
abbrev Planner := ∀ (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  {fuel : Nat} (reference : Program model.source.code fuel), Selection.Outcome model domain original reference

def defaultPlanner : Planner model := fun domain original {_} reference =>
  Review.Tensor.Choice.compile model domain original reference

variable (views : List (View (code := model.source.code))) (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code fuel)

abbrev localDomain (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals) :=
  (fiber views site signal).map View.point

/-- Every receipt branch is prepared from public possibilities before the actual inbox is read. -/
def planWith (planner : Planner model) (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals) :
    Option (Selection.Outcome model (localDomain model views site signal) original reference) :=
  if (fiber views site signal).isEmpty then none
  else some (planner (localDomain model views site signal) original reference)

def plan := planWith model views original reference (defaultPlanner model)

variable (fallback : Prefix.Rule model.source.code)

def headWith (planner : Planner model) (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals) : Prefix.Rule model.source.code :=
  match planWith model views original reference planner site signal with
  | some (.selected choice) => choice.policy.protocol.at original 0
  | some (.blocked _) | none => fallback

def head := headWith model views original reference fallback (defaultPlanner model)

private def lookupHead (saved : List (model.source.code.Key × Prefix.Rule model.source.code))
    (key : model.source.code.Key) : Prefix.Rule model.source.code :=
  ((saved.find? (fun entry => decide (entry.1 = key))).map Prod.snd).getD fallback

private theorem lookup_mapped_head (planner : Planner model) (keys : List model.source.code.Key)
    (key : model.source.code.Key) (inside : key ∈ keys) :
    lookupHead model fallback (keys.map (fun value => (value,headWith model views original reference fallback planner value.1 value.2))) key =
      headWith model views original reference fallback planner key.1 key.2 := by
  induction keys with
  | nil => cases inside
  | cons first rest ih =>
      by_cases same : first = key
      · subst first
        simp [lookupHead]
      · have later : key ∈ rest := (List.mem_cons.mp inside).resolve_left (Ne.symm same)
        simpa [lookupHead,same] using ih later

/-- Materialize each source-selected head once; work and event are readouts of that same head. -/
def ruleWith (planner : Planner model) : Prefix.Rule model.source.code :=
  let saved := model.source.code.keys.map (fun key => (key,headWith model views original reference fallback planner key.1 key.2))
  ⟨⟨fun key inside => (lookupHead model fallback saved key).work.val key inside,
    model.source.code.every_local_policy_is_enumerated _ (by
      intro key inside
      exact (List.mem_pi _ _).mp (lookupHead model fallback saved key).work.property key inside)⟩,
    fun key inside => (lookupHead model fallback saved key).events key inside⟩

private theorem cached_head (planner : Planner model) (key : model.source.code.Key) :
    lookupHead model fallback (model.source.code.keys.map (fun value => (value,headWith model views original reference fallback planner value.1 value.2))) key =
      headWith model views original reference fallback planner key.1 key.2 :=
  lookup_mapped_head model views original reference fallback planner _ key (model.source.code.key_mem key)

def rule := ruleWith model views original reference fallback (defaultPlanner model)

theorem every_planner_generates_an_originally_registered_rule (planner : Planner model) :
    ruleWith model views original reference fallback planner ∈ rules model.source.code :=
  every_rule_is_source_generated _ _

theorem the_generated_receipt_controller_is_an_originally_registered_rule :
    rule model views original reference fallback ∈ rules model.source.code := every_rule_is_source_generated _ _

theorem every_planners_own_event_reads_its_own_receipt_selected_plan
    (planner : Planner model)
    (start : Nat) (rival : Opponent model.source.code) (history : History)
    (past : Events model.source.code) (frame : model.source.code.Frame)
    (site : Fin model.source.code.sites) (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code start history.length = some site) :
    Distributed.Recall.Information.Agency.Protocol.driver model.source.code start
      (ruleWith model views original reference fallback planner) rival history past frame =
      Distributed.Recall.Information.Agency.Protocol.localEvent model.source.code (headWith model views original reference fallback planner site (frame.inbox site)) site (frame.inbox site) := by
  simp only [Distributed.Recall.Information.Agency.Protocol.driver,owned,Distributed.Recall.Information.Agency.Protocol.localEvent,ruleWith,cached_head]

theorem every_planners_work_reads_the_same_receipt_selected_plan
    (planner : Planner model)
    (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals) :
    (ruleWith model views original reference fallback planner).work.val (site,signal) (model.source.code.key_mem _) =
      (headWith model views original reference fallback planner site signal).work.val (site,signal) (model.source.code.key_mem _) := by
  simp only [ruleWith,cached_head]

theorem the_actual_own_event_reads_only_its_own_receipt_selected_plan
    (start : Nat) (rival : Opponent model.source.code) (history : History)
    (past : Events model.source.code) (frame : model.source.code.Frame)
    (site : Fin model.source.code.sites) (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code start history.length = some site) :
    Distributed.Recall.Information.Agency.Protocol.driver model.source.code start
      (rule model views original reference fallback) rival history past frame =
      Distributed.Recall.Information.Agency.Protocol.localEvent model.source.code (head model views original reference fallback site (frame.inbox site)) site (frame.inbox site) :=
  every_planners_own_event_reads_its_own_receipt_selected_plan model views original reference fallback (defaultPlanner model)
    start rival history past frame site owned

theorem the_actual_work_reads_the_same_receipt_selected_plan
    (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals) :
    (rule model views original reference fallback).work.val (site,signal) (model.source.code.key_mem _) =
      (head model views original reference fallback site signal).work.val (site,signal) (model.source.code.key_mem _) :=
  every_planners_work_reads_the_same_receipt_selected_plan model views original reference fallback (defaultPlanner model) site signal

omit fallback in
theorem a_covered_actual_receipt_cannot_be_reclassified_as_absent
    (actual : View (code := model.source.code)) (covered : Knowledge.Contains views actual)
    (site : Fin model.source.code.sites) :
    plan model views original reference site (observation actual site) ≠ none := by
  obtain ⟨representative,inside,_⟩ := the_actual_local_record_generates_its_own_covered_planning_domain views actual covered site
  have nonempty : (fiber views site (observation actual site)).isEmpty = false := by
    cases same : fiber views site (observation actual site) with
    | nil => rw [same] at inside;cases inside
    | cons => rfl
  simp only [plan,planWith,nonempty,Bool.false_eq_true,if_false,ne_eq,reduceCtorEq,not_false_eq_true]

omit fallback in
theorem a_selected_local_future_protects_every_actual_source_with_that_receipt
    (site : Fin model.source.code.sites) (signal : Fin model.source.code.signals)
    (choice : Selection.Choice model (localDomain model views site signal) original reference)
    (actual : View (code := model.source.code)) (covered : Knowledge.Contains views actual)
    (observed : observation actual site = signal) (rival : Opponent model.source.code) :
    Synthesis.accepts model.source.code (economicAxes actual.point.source actual.point.cut)
      (actualEvaluation model actual.point original choice.policy.protocol rival)
      (actualEvaluation model actual.point original reference rival) := by
  have posterior :=  the_actual_local_record_generates_its_own_covered_planning_domain views actual covered site
  rw [observed] at posterior
  exact Observation.public_domain_acceptance_protects_every_covered_actual_source model actual.point original
    choice.policy.protocol rival (localDomain model views site signal) (Knowledge.cursor_covered _ _ posterior) reference choice.policy.accepted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt
