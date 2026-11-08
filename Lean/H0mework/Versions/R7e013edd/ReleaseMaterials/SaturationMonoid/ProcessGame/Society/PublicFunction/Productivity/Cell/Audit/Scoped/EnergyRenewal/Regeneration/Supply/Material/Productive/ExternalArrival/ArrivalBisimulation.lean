import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Wire

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalBisimulation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Related {lp rp : Plan} (left : Consume.State lp) (right : Consume.State rp) : Prop where
  session : Supply.Privacy.Source.SessionTwin left.service.session right.service.session
  spent : left.spent = right.spent

theorem credit_related {left right : Current} (same : Supply.Privacy.Twin left right) :
    Supply.Privacy.Twin (Effect.credit left) (Effect.credit right) := by
  refine ⟨same.technology, congrArg (· + Effect.elapsed) same.clock,
    congrArg (· + Effect.rounds) same.round, same.claims, ?_⟩
  intro party good outside
  simp only [Effect.credit, same.stock party good outside]

theorem receive_related {lp rp : Plan} (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session) :
    Supply.Privacy.Source.SessionTwin (Runtime.nativeReceive left).session (Runtime.nativeReceive right).session :=
  ⟨credit_related same.current, same.scope, same.target, same.history⟩

theorem arrival_related {lp rp : Plan} {left : Consume.State lp} {right : Consume.State rp}
    (same : Related left right) (requested : Nat) : Related (Consume.arrival left requested) (Consume.arrival right requested) := by
  unfold Consume.arrival
  rw [← same.spent]
  split
  · exact ⟨receive_related left.service right.service same.session, rfl⟩
  · exact same

theorem step_related {lp rp : Plan} {left : Consume.State lp} {right : Consume.State rp}
    (same : Related left right) (event : Consume.Event) : Related (Consume.step left event) (Consume.step right event) := by
  cases event with
  | arrival requested => exact arrival_related same requested
  | service command => exact ⟨Productive.advance_public left.service right.service same.session command, same.spent⟩

theorem every_event_word_has_related_actual_successors {lp rp : Plan}
    {left : Consume.State lp} {right : Consume.State rp} (same : Related left right) (events : List Consume.Event) :
    Related (events.foldl Consume.step left) (events.foldl Consume.step right) := by
  induction events generalizing left right with
  | nil => exact same
  | cons event rest ih => exact ih (step_related same event)

theorem advance_related {lp rp : Plan} {left : Consume.State lp} {right : Consume.State rp}
    (same : Related left right) (command : Lean.Json) : Related (Wire.advance left command) (Wire.advance right command) := by
  unfold Wire.advance
  cases Wire.eventOfJson command with
  | error _ => exact same
  | ok event => exact step_related same event

theorem every_json_word_has_related_actual_successors {lp rp : Plan}
    {left : Consume.State lp} {right : Consume.State rp} (same : Related left right) (commands : List Lean.Json) :
    Related (commands.foldl Wire.advance left) (commands.foldl Wire.advance right) := by
  induction commands generalizing left right with
  | nil => exact same
  | cons command rest ih => exact ih (advance_related same command)

theorem every_json_word_keeps_the_same_actual_source {lp rp : Plan}
    {left : Consume.State lp} {right : Consume.State rp} (same : Related left right) (commands : List Lean.Json) :
    Consume.source (commands.foldl Wire.advance left) = Consume.source (commands.foldl Wire.advance right) ∧
      Consume.sourceCurrent (commands.foldl Wire.advance left) = Consume.sourceCurrent (commands.foldl Wire.advance right) := by
  have matched := every_json_word_has_related_actual_successors same commands
  exact ⟨congrArg Packet.physical matched.spent, congrArg Packet.current matched.spent⟩

theorem step_keeps_own_private_frame {plan : Plan} (state : Consume.State plan) (event : Consume.Event) :
    Supply.Privacy.ownFrame (Consume.step state event).service.session.current =
      Supply.Privacy.ownFrame state.service.session.current := by
  cases event with
  | arrival requested => exact Consume.private_stock_is_preserved state requested
  | service command =>
    simp only [Consume.step, Consume.operate, Productive.advance]
    cases requested : command.request with
    | error _ => rfl
    | ok operation =>
      cases operation with
      | inl mode => exact Productive.own_private_frame_survives state.service mode
      | inr request => exact Supply.Privacy.Session.own_private_frame_survives state.service.session request.1 request.2

theorem step_keeps_original_financial_admissions {plan : Plan} (state : Consume.State plan) (event : Consume.Event) :
    state.service.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (Consume.step state event).service.account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  cases event with
  | arrival requested => rw [show (Consume.step state (.arrival requested)).service.account = state.service.account from
      Consume.original_account_is_preserved state requested]
  | service command =>
    simp only [Consume.step, Consume.operate, Productive.advance]
    cases requested : command.request with
    | error _ => exact List.prefix_rfl
    | ok operation =>
      cases operation with
      | inl mode => exact Productive.original_financial_admissions_keep_their_identity state.service mode
      | inr request => exact Finance.State.every_original_issued_claim_keeps_its_identity state.service request.1 request.2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalBisimulation
