import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.InstrumentProjection
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.ArrivalBisimulation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.FinancialProjection
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Financial.Family.InstrumentProjection

def publicIssue (item : Supply.Privacy.PublicItem) : Bool :=
  match item.request.operation with
  | .issue _ _ _ _ => item.accepted
  | _ => false

theorem productive_public_items_count_the_actual_issued_claims (scope : Scope) (current : Current)
    (actions : List JointAction) :
    ((law scope).rawItems current actions).countP (acceptedIssue (law scope)) =
      (Productive.publicItems scope current actions 0).countP publicIssue := by
  unfold Productive.publicItems
  rw [Productive.execute_exact, List.countP_map]
  apply congrArg (fun predicate => ((law scope).rawItems current actions).countP predicate)
  funext item
  cases operation : item.request.operation <;> simp [acceptedIssue, publicIssue, operation]

theorem actual_productive_cycle_generates_its_public_slot_count {plan : Plan}
    (state : Finance.State plan) (mode : Mode) :
    (Productive.next state mode).account.current.slots.length = state.account.current.slots.length +
      (Productive.observe state.session.window.scope mode state.session.current).actions.countP publicIssue := by
  have native := first_two_visits_generate_their_own_slot_count Finance.sources (Productive.input state mode) state.account
  change (Productive.next state mode).account.current.slots.length = state.account.current.slots.length +
    ((law state.session.window.scope).rawItems
      ((law state.session.window.scope).next state.session.current [])
      (Productive.word state.session.window.scope mode ((law state.session.window.scope).next state.session.current []))).countP
        (acceptedIssue (law state.session.window.scope)) at native
  rw [native]
  congr 1
  exact productive_public_items_count_the_actual_issued_claims _ _ _

theorem supply_public_items_count_the_actual_issued_claims (scope : Scope) (current : Current)
    (actions : List JointAction) :
    ((Supply.law scope).rawItems current actions).countP (acceptedIssue (Supply.law scope)) =
      (Supply.Privacy.publicItems scope current actions 0).countP publicIssue := by
  unfold Supply.Privacy.publicItems
  rw [List.countP_map]
  apply congrArg (fun predicate => ((Supply.law scope).rawItems current actions).countP predicate)
  funext item
  cases operation : item.request.operation <;> simp [acceptedIssue, publicIssue, operation]

theorem actual_service_generates_its_public_slot_count {plan : Plan}
    (state : Finance.State plan) (query : Query) (mode : Supply.Mode) :
    (state.next query mode).account.current.slots.length = state.account.current.slots.length +
      (Supply.Privacy.reply state query mode).observation.actions.countP publicIssue := by
  have native := first_two_visits_generate_their_own_slot_count Finance.sources (state.session.input query mode) state.account
  change (Financial.Family.continueVisits Finance.sources (state.session.input query mode) 0 2 state.account).current.slots.length =
    state.account.current.slots.length + ((Supply.law state.session.window.scope).rawItems
      state.session.prepared (state.session.actions query mode)).countP (acceptedIssue (Supply.law state.session.window.scope)) at native
  change (Finance.Runtime.consume state query mode 1).account.current.slots.length = _
  rw [Finance.Runtime.consume_account]
  rw [show state.postAccount query mode = Financial.Family.continueVisits Finance.sources
    (state.session.input query mode) 0 2 state.account from rfl, native]
  congr 1
  exact supply_public_items_count_the_actual_issued_claims _ _ _

theorem advance_generates_equal_slot_counts {lp rp : Plan}
    (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session)
    (slots : left.account.current.slots.length = right.account.current.slots.length) (command : Command) :
    (Productive.advance left command).account.current.slots.length =
      (Productive.advance right command).account.current.slots.length := by
  unfold Productive.advance
  cases requested : command.request with
  | error _ => exact slots
  | ok operation =>
    cases operation with
    | inl mode =>
      rw [actual_productive_cycle_generates_its_public_slot_count, actual_productive_cycle_generates_its_public_slot_count,
        slots, ← same.scope, Productive.observe_public same.current left.session.window.scope rfl mode]
    | inr request =>
      rw [actual_service_generates_its_public_slot_count, actual_service_generates_its_public_slot_count,
        slots, same.reply request.1 request.2]

theorem original_supply_starts_with_its_native_delivery_slice (larger : Bool)
    (input : EnergyRenewal.Privacy.SourceInput) (state : Finance.State (input.plan larger))
    (generated : Supply.Privacy.Source.initial larger input = .ok state) :
    Financial.Family.ledgerClaims Finance.sources state.account.current .delivery = state.session.current.claims .delivery := by
  unfold Supply.Privacy.Source.initial at generated
  cases seeded : EnergyRenewal.Privacy.Timing.sourceHandoffSeed larger input with
  | error message => simp only [seeded] at generated; cases generated
  | ok seed =>
    simp only [seeded] at generated
    cases Except.ok.inj generated
    funext debtor creditor
    simp only [Finance.start, Financial.Family.ledgerClaims, Supply.start, initialMemo_exact, join]
    rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.FinancialProjection
