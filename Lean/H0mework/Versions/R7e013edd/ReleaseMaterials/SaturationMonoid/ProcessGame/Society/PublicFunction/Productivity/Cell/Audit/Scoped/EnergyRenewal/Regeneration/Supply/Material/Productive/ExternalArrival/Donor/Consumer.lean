import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Donor.Source

set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Consumer
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

theorem supplied_is_from_the_actual_funded_signer {plan : Plan} (state : Finance.State plan)
    (round : Nat) (signer : Actor) (enabled : Bool) (current : Current)
    (offered : status state round signer enabled current = .supplied) :
    signer = receiver ∧ quantity ≤ current.stock receiver .feed ∧
      (Productive.law state.session.window.scope).Valid current (request signer) := by
  unfold status at offered
  split_ifs at offered with stale withheld wrong missing refused
  exact ⟨of_not_not wrong,missing,refused⟩

theorem the_same_actual_occurrence_pays_and_delivers {plan : Plan} (state : Finance.State plan)
    (round : Nat) (signer : Actor) (enabled : Bool)
    (offered : status state round signer enabled (prepared state) = .supplied) :
    (nextFinance state round signer enabled).session.current.stock receiver .feed =
      state.session.current.stock receiver .feed - quantity ∧
    (nextFinance state round signer enabled).session.current.stock customer .feed =
      state.session.current.stock customer .feed + quantity := by
  have source := supplied_is_from_the_actual_funded_signer state round signer enabled _ offered
  have enough : quantity ≤ state.session.current.stock receiver .feed := source.2.1
  have actual := DonorRelease.actual_stock state.session.window.scope (prepared state) quantity
    (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native])
    (by simp [EnergyRenewal.Continuation.Window.scope,Scoped.native]) (by norm_num [quantity]) enough
  change (Runtime.current state round signer enabled).stock receiver .feed = _ ∧
    (Runtime.current state round signer enabled).stock customer .feed = _
  rw [runtime_is_the_actual_word]
  unfold expected word
  rw [if_pos offered]
  change ((Productive.law state.session.window.scope).step (prepared state) (request signer)).stock receiver .feed = _ ∧
    ((Productive.law state.session.window.scope).step (prepared state) (request signer)).stock customer .feed = _
  rw [source.1]
  exact ⟨actual.1,actual.2.1⟩

theorem refusal_does_not_create_a_payment_or_material {plan : Plan} (state : Finance.State plan)
    (round : Nat) (signer : Actor) (enabled : Bool)
    (refused : status state round signer enabled (prepared state) ≠ .supplied) :
    (nextFinance state round signer enabled).session.current.stock = state.session.current.stock := by
  change (Runtime.current state round signer enabled).stock = _
  rw [runtime_is_the_actual_word]
  simp only [expected,word,if_neg refused]
  rfl

theorem every_attempt_has_its_own_new_round {plan : Plan} (state : Finance.State plan)
    (round : Nat) (signer : Actor) (enabled : Bool) :
    origin (nextFinance state round signer enabled) = origin state + 2 := by
  change (Runtime.current state round signer enabled).round = state.session.current.round + 2
  rw [runtime_is_the_actual_word]
  unfold expected word
  split <;> simp [prepared,RawLaw.next,RawLaw.execute]

theorem replay_cannot_become_a_new_occurrence {plan : Plan} (state : Finance.State plan)
    (round : Nat) (signer replaySigner : Actor) (enabled replayEnabled : Bool) (current : Current)
    (matched : round = origin state) :
    status (nextFinance state round signer enabled) round replaySigner replayEnabled current = .blocked .stale := by
  have later := every_attempt_has_its_own_new_round state round signer enabled
  have stale : round ≠ origin (nextFinance state round signer enabled) := by omega
  simp only [status,if_pos stale]

theorem a_new_donor_never_reopens_the_old_complete_source {plan : Plan} (state : State plan)
    (round : Nat) (signer : Actor) (enabled : Bool) :
    (donate state round signer enabled).legacy.spent = state.legacy.spent ∧
    Packet.full (donate state round signer enabled).legacy.spent = Packet.full state.legacy.spent ∧
    Consume.sourceCurrent (donate state round signer enabled).legacy = Consume.sourceCurrent state.legacy :=
  ⟨rfl,rfl,rfl⟩

theorem the_whole_old_responsibility_and_financial_prefix_survive {plan : Plan} (state : Finance.State plan)
    (round : Nat) (signer : Actor) (enabled : Bool) :
    (nextFinance state round signer enabled).session.current.claims = state.session.current.claims ∧
    state.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (nextFinance state round signer enabled).account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  constructor
  · change (Runtime.current state round signer enabled).claims = _
    rw [runtime_is_the_actual_word]
    exact claims_preserved state round signer enabled
  · exact (Financial.Family.consumeOrigins_preserves_original_claims Finance.sources _ _).trans
      (Financial.Family.consumeOrigins_preserves_original_claims Finance.sources _ _)

theorem the_original_context_and_actual_history_are_not_replaced {plan : Plan} (state : Finance.State plan)
    (round : Nat) (signer : Actor) (enabled : Bool) :
    (nextFinance state round signer enabled).session.origin = state.session.origin ∧
    (nextFinance state round signer enabled).session.received = state.session.received ∧
    (nextFinance state round signer enabled).session.window = state.session.window ∧
    (nextFinance state round signer enabled).session.target = state.session.target ∧
    (nextFinance state round signer enabled).session.history = state.session.history ++ [⟨input state round signer enabled,1⟩] :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Consumer
