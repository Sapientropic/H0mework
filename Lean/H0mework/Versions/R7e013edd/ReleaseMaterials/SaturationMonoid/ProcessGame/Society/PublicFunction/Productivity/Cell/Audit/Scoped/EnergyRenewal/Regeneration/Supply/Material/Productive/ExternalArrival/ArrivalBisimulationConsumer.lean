import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.ArrivalBisimulation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalBisimulationConsumer
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open EnergyRenewal.Privacy (ResultRel)
open ArrivalBisimulation

theorem original_productive_source_generates_related_sessions (source : Lean.Json) :
    ResultRel (fun (left : Productive.Wire.Execution false) (right : Productive.Wire.Execution true) =>
      left.input = right.input ∧ Supply.Privacy.Source.SessionTwin left.state.session right.state.session)
      (Productive.Wire.execute false source) (Productive.Wire.execute true source) := by
  unfold Productive.Wire.execute
  cases parsed : Productive.Wire.decode source with
  | error message => exact .error message
  | ok decoded =>
    simp only [bind, Except.bind]
    have initial := Supply.Privacy.Source.original_source_generates_new_supply_initial_relation decoded.input
    cases left : Supply.Privacy.Source.initial false decoded.input with
    | error message =>
      cases right : Supply.Privacy.Source.initial true decoded.input with
      | error other =>
        rw [left, right] at initial
        cases initial
        exact .error message
      | ok value => rw [left, right] at initial; cases initial
    | ok first =>
      cases right : Supply.Privacy.Source.initial true decoded.input with
      | error message => rw [left, right] at initial; cases initial
      | ok second =>
        rw [left, right] at initial
        cases initial with
        | ok same =>
          have prior := Supply.Privacy.cumulative_related_own_states_and_complete_output first second same.1
            Supply.Privacy.Wire.render decoded.priorStrategy decoded.prior.size
          have generated := Productive.Wire.complete_adaptive_default_output_and_own_next _ _ prior.1
            decoded.strategy decoded.commands.size
          exact .ok ⟨rfl, generated.1⟩

theorem the_original_source_generates_every_arrival_history_relation
    (source : Lean.Json) (events : List Consume.Event) :
    ResultRel (fun (left : History.Execution false) (right : History.Execution true) => Related left.state right.state)
      (History.restore false source events) (History.restore true source events) := by
  have original := original_productive_source_generates_related_sessions source
  unfold History.restore
  cases left : Productive.Wire.execute false source with
  | error message =>
    cases right : Productive.Wire.execute true source with
    | error other =>
      rw [left, right] at original
      cases original
      exact .error message
    | ok value => rw [left, right] at original; cases original
  | ok first =>
    cases right : Productive.Wire.execute true source with
    | error message => rw [left, right] at original; cases original
    | ok second =>
      rw [left, right] at original
      cases original with
      | ok same =>
        apply ResultRel.ok
        apply every_event_word_has_related_actual_successors
        exact ⟨same.2, rfl⟩

structure MaterialObservation where
  current : Current
  scope : Scope
  target : Party
  history : Nat
  spent : Bool
  source : ProviderCurrent

def observe {plan : Plan} (state : Consume.State plan) : MaterialObservation :=
  ⟨Supply.Privacy.publicize state.service.session.current, state.service.session.window.scope,
    state.service.session.target, state.service.session.history.length, state.spent, Consume.sourceCurrent state⟩

theorem related_states_have_the_same_material_observation {lp rp : Plan}
    {left : Consume.State lp} {right : Consume.State rp} (same : Related left right) : observe left = observe right := by
  simp only [observe, Consume.sourceCurrent, same.session.current.publicize, same.session.scope, same.session.target,
    same.session.history, same.spent]

def sourceObservation (larger : Bool) (source : Lean.Json) (commands : List Lean.Json) :
    Except String MaterialObservation :=
  (History.restore larger source []).map fun initial => observe (commands.foldl Wire.advance initial.state)

theorem the_same_original_source_generates_equal_material_observations
    (source : Lean.Json) (commands : List Lean.Json) :
    sourceObservation false source commands = sourceObservation true source commands := by
  have original := the_original_source_generates_every_arrival_history_relation source []
  unfold sourceObservation
  cases left : History.restore false source [] with
  | error message =>
    cases right : History.restore true source [] with
    | error other => rw [left, right] at original; cases original; rfl
    | ok value => rw [left, right] at original; cases original
  | ok first =>
    cases right : History.restore true source [] with
    | error message => rw [left, right] at original; cases original
    | ok second =>
      rw [left, right] at original
      cases original with
      | ok same => exact congrArg Except.ok (related_states_have_the_same_material_observation
          (every_json_word_has_related_actual_successors same commands))

theorem every_json_word_keeps_its_own_private_frame {plan : Plan}
    (state : Consume.State plan) (commands : List Lean.Json) :
    Supply.Privacy.ownFrame (commands.foldl Wire.advance state).service.session.current =
      Supply.Privacy.ownFrame state.service.session.current := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    rw [List.foldl_cons, ih]
    unfold Wire.advance
    cases parsed : Wire.eventOfJson command with
    | error _ => rfl
    | ok event => exact step_keeps_own_private_frame state event

theorem every_json_word_keeps_every_original_financial_admission {plan : Plan}
    (state : Consume.State plan) (commands : List Lean.Json) :
    state.service.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (commands.foldl Wire.advance state).service.account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  induction commands generalizing state with
  | nil => exact List.prefix_rfl
  | cons command rest ih =>
    apply List.IsPrefix.trans (l₂ := (Wire.advance state command).service.account.current.slots.map
      (Financial.Family.slotClaim Finance.sources)) _ (ih _)
    unfold Wire.advance
    cases parsed : Wire.eventOfJson command with
    | error _ => exact List.prefix_rfl
    | ok event => exact step_keeps_original_financial_admissions state event

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalBisimulationConsumer
