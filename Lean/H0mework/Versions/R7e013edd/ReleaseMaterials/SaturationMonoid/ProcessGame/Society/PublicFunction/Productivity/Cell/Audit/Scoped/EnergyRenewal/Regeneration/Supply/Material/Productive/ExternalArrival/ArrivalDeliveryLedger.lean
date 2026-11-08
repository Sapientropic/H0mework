import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.FinancialProjection

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalDeliveryLedger
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def unit (instrument : Instrument) : Good := match instrument with | .delivery => .energy | _ => .life
def Contract (source : Finance.Input) : Prop :=
  source.law.settlementUnit = unit ∧ source.law.settlementRate = fun _ => 1
def OriginalContracts (account : Finance.Account) : Prop :=
  ∀ claim ∈ account.current.slots.map (Financial.Family.slotClaim Finance.sources), Contract claim.1

theorem compatible_with_the_original_admissions (source : Finance.Input) (current : Contract source)
    (account : Finance.Account) (original : OriginalContracts account) :
    Financial.Family.BalanceConservation.Compatible Finance.sources source account.current := by
  intro claim member
  have prior := original claim member
  exact ⟨(congrFun current.1 claim.2.instrument).trans (congrFun prior.1 claim.2.instrument).symm,
    (congrFun current.2 claim.2.instrument).trans (congrFun prior.2 claim.2.instrument).symm⟩

theorem consume_keeps_original_contracts (source : Finance.Input) (native : Contract source)
    (origin : Financial.InstructionOrigin source) (account : Finance.Account) (old : OriginalContracts account) :
    OriginalContracts ((Financial.Family.consume Finance.sources ⟨source, origin⟩ account).next Finance.sources) := by
  intro claim member
  rw [Financial.Family.consume_exact_claims] at member
  rcases List.mem_append.mp member with prior | fresh
  · exact old claim prior
  · unfold Financial.Family.originsClaim? at fresh
    split at fresh
    · have same : claim.1 = source := by
        have claimed := List.mem_singleton.mp fresh
        exact congrArg Sigma.fst claimed
      rw [same]
      exact native
    · cases fresh

theorem origins_keep_original_contracts (source : Finance.Input) (native : Contract source)
    (origins : List (Financial.InstructionOrigin source)) (account : Finance.Account) (old : OriginalContracts account) :
    OriginalContracts (Financial.Family.consumeOrigins Finance.sources (origins.map (Sigma.mk source)) account) := by
  induction origins generalizing account with
  | nil => exact old
  | cons origin rest ih => exact ih _ (consume_keeps_original_contracts source native origin account old)

theorem visits_keep_original_contracts (source : Finance.Input) (native : Contract source)
    (start count : Nat) (account : Finance.Account) (old : OriginalContracts account) :
    OriginalContracts (Financial.Family.continueVisits Finance.sources source start count account) := by
  induction count with
  | zero => exact old
  | succ count ih => exact origins_keep_original_contracts source native _ _ ih

structure Tracked {plan : Plan} (state : Finance.State plan) : Prop where
  original : OriginalContracts state.account
  delivery : Financial.Family.ledgerClaims Finance.sources state.account.current .delivery = state.session.current.claims .delivery

theorem source_initial_is_tracked (larger : Bool) (input : EnergyRenewal.Privacy.SourceInput)
    (state : Finance.State (input.plan larger)) (generated : Supply.Privacy.Source.initial larger input = .ok state) : Tracked state := by
  refine ⟨?_, FinancialProjection.original_supply_starts_with_its_native_delivery_slice larger input state generated⟩
  unfold Supply.Privacy.Source.initial at generated
  cases seeded : EnergyRenewal.Privacy.Timing.sourceHandoffSeed larger input with
  | error message => simp only [seeded] at generated; cases generated
  | ok seed =>
    simp only [seeded] at generated
    cases Except.ok.inj generated
    intro claim member
    cases member

theorem productive_cycle_is_tracked {plan : Plan} (state : Finance.State plan) (old : Tracked state) (mode : Mode) :
    Tracked (Productive.next state mode) := by
  have native : Contract (Productive.input state mode) := ⟨rfl, rfl⟩
  refine ⟨visits_keep_original_contracts _ native 0 2 state.account old.original, ?_⟩
  change Financial.Family.ledgerClaims Finance.sources
    (Financial.Family.continueVisits Finance.sources (Productive.input state mode) 0 2 state.account).current .delivery =
      (Productive.Runtime.current state mode).claims .delivery
  rw [Productive.Runtime.current_is_own_root_next]
  exact Financial.Family.InstrumentProjection.continue_visits_source_slice Finance.sources (Productive.input state mode)
    0 2 state.account .delivery (compatible_with_the_original_admissions _ native state.account old.original) old.delivery

theorem service_is_tracked {plan : Plan} (state : Finance.State plan) (old : Tracked state)
    (query : Query) (mode : Supply.Mode) : Tracked (state.next query mode) := by
  have native : Contract (state.session.input query mode) := ⟨rfl, rfl⟩
  constructor
  · change OriginalContracts (Finance.Runtime.consume state query mode 1).account
    rw [Finance.Runtime.consume_account]
    exact visits_keep_original_contracts _ native 0 2 state.account old.original
  · change Financial.Family.ledgerClaims Finance.sources (Finance.Runtime.consume state query mode 1).account.current .delivery =
      (state.session.next query mode).current.claims .delivery
    rw [Finance.Runtime.consume_account, Session.next_is_the_same_actual_generated_next]
    exact Financial.Family.InstrumentProjection.continue_visits_source_slice Finance.sources (state.session.input query mode)
      0 2 state.account .delivery (compatible_with_the_original_admissions _ native state.account old.original) old.delivery

theorem advance_is_tracked {plan : Plan} (state : Finance.State plan) (old : Tracked state) (command : Command) :
    Tracked (Productive.advance state command) := by
  unfold Productive.advance
  cases requested : command.request with
  | error _ => exact old
  | ok request => cases request with
    | inl mode => exact productive_cycle_is_tracked state old mode
    | inr request => exact service_is_tracked state old request.1 request.2

theorem arrival_is_tracked {plan : Plan} (state : Consume.State plan) (old : Tracked state.service) (quantity : Nat) :
    Tracked (Consume.arrival state quantity).service := by
  unfold Consume.arrival
  split
  · exact ⟨old.original, old.delivery⟩
  · exact old

theorem step_is_tracked {plan : Plan} (state : Consume.State plan) (old : Tracked state.service) (event : Consume.Event) :
    Tracked (Consume.step state event).service := by
  cases event with
  | arrival quantity => exact arrival_is_tracked state old quantity
  | service command => exact advance_is_tracked state.service old command

theorem wire_advance_is_tracked {plan : Plan} (state : Consume.State plan) (old : Tracked state.service) (command : Lean.Json) :
    Tracked (Wire.advance state command).service := by
  unfold Wire.advance
  cases Wire.eventOfJson command with
  | error _ => exact old
  | ok event => exact step_is_tracked state old event

theorem supply_play_is_tracked {plan : Plan} (state : Finance.State plan) (old : Tracked state)
    (render : Supply.Privacy.Render) (strategy : Supply.Privacy.Strategy) (count : Nat) :
    Tracked (Supply.Privacy.play state render strategy count).1 := by
  induction count with
  | zero => exact old
  | succ n ih =>
    simp only [Supply.Privacy.play]
    cases requested : (strategy (Supply.Privacy.play state render strategy n).2 n).request with
    | error _ => simpa only [Supply.Privacy.advance, requested] using ih
    | ok request =>
      simpa only [Supply.Privacy.advance, requested] using service_is_tracked _ ih request.1 request.2

theorem productive_play_is_tracked {plan : Plan} (state : Finance.State plan) (old : Tracked state)
    (render : Render) (strategy : Strategy) (count : Nat) : Tracked (Productive.play state render strategy count).1 := by
  induction count with
  | zero => exact old
  | succ n ih => exact advance_is_tracked _ ih _

theorem productive_source_is_tracked (larger : Bool) (source : Lean.Json) (execution : Productive.Wire.Execution larger)
    (generated : Productive.Wire.execute larger source = .ok execution) : Tracked execution.state := by
  unfold Productive.Wire.execute at generated
  cases parsed : Productive.Wire.decode source with
  | error _ => simp only [parsed, bind, Except.bind] at generated; cases generated
  | ok decoded =>
    simp only [parsed, bind, Except.bind] at generated
    cases started : Supply.Privacy.Source.initial larger decoded.input with
    | error _ => simp only [started] at generated; cases generated
    | ok first =>
      simp only [started] at generated
      cases Except.ok.inj generated
      exact productive_play_is_tracked _
        (supply_play_is_tracked first (source_initial_is_tracked larger decoded.input first started)
          Supply.Privacy.Wire.render decoded.priorStrategy decoded.prior.size)
        Productive.Wire.render decoded.strategy decoded.commands.size

theorem event_word_is_tracked {plan : Plan} (state : Consume.State plan) (old : Tracked state.service)
    (events : List Consume.Event) : Tracked (events.foldl Consume.step state).service := by
  induction events generalizing state with
  | nil => exact old
  | cons event rest ih => exact ih _ (step_is_tracked state old event)

theorem restored_source_is_tracked (larger : Bool) (source : Lean.Json) (events : List Consume.Event)
    (execution : History.Execution larger) (generated : History.restore larger source events = .ok execution) :
    Tracked execution.state.service := by
  unfold History.restore at generated
  cases original : Productive.Wire.execute larger source with
  | error _ => simp only [original, bind, Except.bind] at generated; cases generated
  | ok first =>
    simp only [original, bind, Except.bind] at generated
    cases Except.ok.inj generated
    exact event_word_is_tracked _ (productive_source_is_tracked larger source first original) events

theorem json_word_is_tracked {plan : Plan} (state : Consume.State plan) (old : Tracked state.service)
    (commands : List Lean.Json) : Tracked (commands.foldl Wire.advance state).service := by
  induction commands generalizing state with
  | nil => exact old
  | cons command rest ih => exact ih _ (wire_advance_is_tracked state old command)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalDeliveryLedger
