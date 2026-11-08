import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Runtime

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Consume
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev quantity := Effect.quantity
abbrev elapsed := Effect.elapsed
abbrev rounds := Effect.rounds
abbrev credit := Effect.credit
abbrev receive := @Effect.receive
abbrev original_source_pays_three_units_and_six_steps := Effect.original_source_pays_three_units_and_six_steps

structure State (plan : Plan) where
  private mk ::
  service : Finance.State plan
  spent : Bool

private def start {plan : Plan} (state : Finance.State plan) : State plan := ⟨state,false⟩
def arrival {plan : Plan} (state : State plan) (requested : Nat) : State plan :=
  if !state.spent && decide ((requested:ℚ)=quantity) then ⟨Runtime.nativeReceive state.service,true⟩ else state
def operate {plan : Plan} (state : State plan) (command : Command) : State plan :=
  ⟨Productive.advance state.service command,state.spent⟩

inductive Event where
  | arrival (quantity : Nat)
  | service (command : Command)
def step {plan : Plan} (state : State plan) : Event → State plan
  | .arrival quantity => arrival state quantity
  | .service command => operate state command
private def replay {plan : Plan} (base : Finance.State plan) (events : List Event) : State plan :=
  events.foldl step (start base)

structure Execution where
  private mk ::
  input : EnergyRenewal.Privacy.SourceInput
  state : State (input.plan false)

/-- Recovery replays the original source and the entire local event word, never a caller's balance. -/
def restore (source : Lean.Json) (events : List Event) : Except String Execution := do
  let original ← Productive.Wire.execute false source
  return ⟨original.input,replay original.state events⟩

theorem replay_append {plan : Plan} (base : Finance.State plan) (first second : List Event) :
    replay base (first++second)=second.foldl step (replay base first) := by simp only [replay,List.foldl_append]

theorem step_keeps_consumed_source {plan : Plan} (state : State plan)
    (used : state.spent=true) (event : Event) : (step state event).spent=true := by
  cases event with
  | arrival quantity => simp [step,arrival,used]
  | service command => exact used

theorem every_future_suffix_keeps_consumed_source {plan : Plan} (state : State plan)
    (used : state.spent=true) (events : List Event) : (events.foldl step state).spent=true := by
  induction events generalizing state with
  | nil => exact used
  | cons event tail ih => exact ih (step state event) (step_keeps_consumed_source state used event)

noncomputable def source {plan : Plan} (state : State plan) := Packet.physical state.spent
def sourceCurrent {plan : Plan} (state : State plan) := Packet.current state.spent

theorem current_is_the_original_source_occurrence {plan : Plan} (state : State plan) :
    sourceCurrent state=(Protocol.SymbolicAuthentication.EventStep.seed (source state).2).current :=
  Packet.current_is_its_complete_source_occurrence state.spent

theorem actual_source_and_customer_material_commute {plan : Plan} (state : State plan) (fresh : state.spent=false) :
    (sourceCurrent (arrival state 3)).stock 1 .feedstock=Packet.after.stock 1 .feedstock ∧
    (arrival state 3).service.session.current.stock customer .feed=
      state.service.session.current.stock customer .feed+
        ((sourceCurrent state).stock 1 .feedstock-(sourceCurrent (arrival state 3)).stock 1 .feedstock) := by
  simp [arrival,fresh,original_source_pays_three_units_and_six_steps.1,sourceCurrent,Packet.current,
    Runtime.native_receive_effect,Effect.receive,Effect.credit,customer]
  exact Effect.original_source_pays_three_units_and_six_steps.1.symm

theorem no_repeated_credit {plan : Plan} (state : State plan) (spent : state.spent=true) (requested : Nat) :
    arrival state requested=state := by simp [arrival,spent]

theorem original_account_is_preserved {plan : Plan} (state : State plan) (requested : Nat) :
    (arrival state requested).service.account=state.service.account := by
  unfold arrival
  split
  · rw [Runtime.native_receive_effect];rfl
  · rfl

theorem private_stock_is_preserved {plan : Plan} (state : State plan) (requested : Nat) :
    Supply.Privacy.ownFrame (arrival state requested).service.session.current=
      Supply.Privacy.ownFrame state.service.session.current := by
  unfold arrival
  split
  · simp [Runtime.native_receive_effect,Effect.receive,Effect.credit,Supply.Privacy.ownFrame,receiver,customer]
  · rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Consume
