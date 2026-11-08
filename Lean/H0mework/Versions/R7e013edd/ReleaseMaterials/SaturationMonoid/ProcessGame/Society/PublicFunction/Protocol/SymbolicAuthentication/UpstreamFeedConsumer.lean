import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RoundEpisodeSource RoundEpisodePrefix
open UpstreamFeedSource

theorem arrival_boundary (state : State) (submit : Bool) :
    boundary (arrived state submit) = boundary state+1 := by
  change state.model.source.history.length+2+(state.cut+1) = _
  dsimp only [boundary]
  omega

theorem arrival_prefix (state : State) (submit : Bool) :
    Prefix state.model.source.input (arrived state submit).model.source.input (boundary state) := by
  apply (an_actual_continuation_keeps_the_complete_original_prefix state.model state.cut (incoming state submit)).weaken
  dsimp [boundary,MaterialRoundSource.depth,Machine.Continuation.depth]
  omega

theorem next_prefix (state : State) (submit : Bool) (control : Controller) :
    Prefix state.model.source.input (UpstreamFeedSource.next state submit control).model.source.input (boundary state) :=
  (arrival_prefix state submit).trans
    ((every_episode_keeps_the_complete_original_prefix (arrived state submit) (control (arrived state submit))).weaken
      (by rw [arrival_boundary];omega))

theorem next_boundary (state : State) (submit : Bool) (control : Controller) :
    boundary state+5 ≤ boundary (UpstreamFeedSource.next state submit control) := by
  have step := every_episode_advances_the_real_native_boundary (arrived state submit) (control (arrived state submit))
  rw [arrival_boundary] at step
  omega

theorem run_boundary (initial : State) (submit : State → Bool) (control : Controller) (n : Nat) :
    boundary initial+5*n ≤ boundary (UpstreamFeedSource.run initial submit control n) := by
  induction n with
  | zero => change boundary initial+5*0 ≤ boundary initial;omega
  | succ n prior =>
    have step := next_boundary (UpstreamFeedSource.run initial submit control n)
      (submit (UpstreamFeedSource.run initial submit control n)) control
    change boundary initial+5*(n+1) ≤ boundary (UpstreamFeedSource.next
      (UpstreamFeedSource.run initial submit control n) (submit (UpstreamFeedSource.run initial submit control n)) control)
    omega

theorem run_prefix (initial : State) (submit : State → Bool) (control : Controller) (n : Nat) :
    Prefix initial.model.source.input (UpstreamFeedSource.run initial submit control n).model.source.input (boundary initial) := by
  induction n with
  | zero => exact ⟨rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩
  | succ n prior =>
    have growing := run_boundary initial submit control n
    exact prior.trans ((next_prefix (UpstreamFeedSource.run initial submit control n)
      (submit (UpstreamFeedSource.run initial submit control n)) control).weaken (by omega))

theorem every_later_control_keeps_all_original_financial_accounts
    (initial : State) (submit : State → Bool) (control : Controller) (n ordinal : Nat)
    (earlier : ordinal ≤ boundary initial) :
    Native.Coupling.Match initial.model.source.code initial.model.source.input
      (UpstreamFeedSource.run initial submit control n).model.source.input
      (Financial.accountAt initial.model.source.input ordinal)
      (Financial.accountAt (UpstreamFeedSource.run initial submit control n).model.source.input ordinal) := by
  have prior := run_prefix initial submit control n
  have events : ∀ cut, cut < boundary initial →
      ProgrammeSource.rawEvent (UpstreamFeedSource.run initial submit control n).model.source.input
        (ProgrammeHistory.visitAt initial.model.source.input cut).current =
      ProgrammeSource.rawEvent initial.model.source.input (ProgrammeHistory.visitAt initial.model.source.input cut).current := by
    intro cut inside
    exact (congrArg (ProgrammeSource.rawEvent (UpstreamFeedSource.run initial submit control n).model.source.input)
      (prior.currents cut (by omega)).symm).trans (prior.words cut inside)
  exact Native.Coupling.History.complete_accounts initial.model.source.code initial.model.source.input
    (UpstreamFeedSource.run initial submit control n).model.source.input prior.law prior.initial (boundary initial) events
    initial.model.source.body (UpstreamFeedSource.run initial submit control n).model.source.body rfl rfl ordinal earlier

theorem every_feed_occurrence_consumes_its_native_responsibility_ledger_and_next
    (state : State) (submit : Bool) :
    RoundEpisodeConsumer.NativeConsumed (arrivalModel state submit) (MaterialRoundSource.depth state.model state.cut)
      (disposition state submit) := RoundEpisodeConsumer.native_generated_consumed _ _

theorem actual_feed_remains_in_the_next_native_archive (state : State) (submit : Bool) (control : Controller) :
    Archive.native (arrivalModel state submit) (MaterialRoundSource.depth state.model state.cut) (disposition state submit) ∈
      (UpstreamFeedSource.next state submit control).archive := by
  obtain ⟨more,same⟩ := RoundEpisodeConsumer.each_actual_next_retains_every_old_archive_record
    (arrived state submit) (control (arrived state submit))
  rw [same]
  exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

theorem every_later_controller_receives_all_original_archives
    (initial : State) (submit : State → Bool) (control : Controller) (n : Nat) :
    ∃ added, (UpstreamFeedSource.run initial submit control n).archive = initial.archive ++ added := by
  induction n with
  | zero => exact ⟨[],(List.append_nil _).symm⟩
  | succ n prior =>
    obtain ⟨old,sameOld⟩ := prior
    obtain ⟨fresh,sameNew⟩ := RoundEpisodeConsumer.each_actual_next_retains_every_old_archive_record
      (arrived (UpstreamFeedSource.run initial submit control n) (submit (UpstreamFeedSource.run initial submit control n)))
      (control (arrived (UpstreamFeedSource.run initial submit control n) (submit (UpstreamFeedSource.run initial submit control n))))
    refine ⟨old ++ [Archive.native
      (arrivalModel (UpstreamFeedSource.run initial submit control n) (submit (UpstreamFeedSource.run initial submit control n)))
      (MaterialRoundSource.depth (UpstreamFeedSource.run initial submit control n).model (UpstreamFeedSource.run initial submit control n).cut)
      (disposition (UpstreamFeedSource.run initial submit control n) (submit (UpstreamFeedSource.run initial submit control n)))] ++ fresh,?_⟩
    exact sameNew.trans (by
      change ((UpstreamFeedSource.run initial submit control n).archive ++ [_]) ++ fresh = _
      rw [sameOld]
      simp only [List.append_assoc])

theorem actual_external_supply_funds_the_original_preparation (state : State)
    (same : state.model.source.code.law = UpstreamProductionLaw.law)
    (demand : Demand state) (resources : UpstreamFeedLaw.Resources (current state)) :
    WorkerInputSource.incoming
      (rawSource (arrived state true) (UpstreamProductionSource.incoming (arrived state true)))
      ((arrived state true).cut+1) = WorkerInputLaw.word ∧
      let finish := MaterialRoundSource.prepared
        (supplied (arrived state true) (UpstreamProductionSource.incoming (arrived state true)))
        (count (arrived state true)) (arrival (arrived state true) (UpstreamProductionSource.incoming (arrived state true)))
      finish.stock 0 .feedstock = 0 ∧
      finish.stock 0 .energy = (current state).stock 0 .energy+1 ∧
      finish.stock 0 .labor = (current state).stock 0 .labor+1 ∧
      finish.stock 1 .waste = (current state).stock 1 .waste-1 ∧
      finish.stock 1 .service = (current state).stock 1 .service+3 ∧
      finish.stock 2 .energy = (current state).stock 2 .energy ∧
      finish.stock 2 .labor = (current state).stock 2 .labor ∧
      finish.claims = (current state).claims ∧ finish.technology = (current state).technology := by
  have selected := primitive_resources_generate_the_offer state same demand resources
  have generated := generated_primitive_inputs state true same selected
  have consumed := UpstreamProductionConsumer.actual_production_is_consumed_by_original_worker_fuel_and_service_steps
    (arrived state true) same generated.2.2.2.1 generated.2.2.2.2 generated.2.2.1
  rw [generated.2.1] at consumed
  simpa [UpstreamFeedLaw.successor] using consumed

abbrev productionConsumes (state : State) (submit : Bool) :=
  UpstreamProductionConsumer.production_and_all_preparation_attempts_use_their_original_native_ledger_and_next (arrived state submit)
abbrev communicationConsumes (state : State) (submit : Bool) (control : Controller)
    (entry : RoundEpisodeSource.Entry (arrived state submit) (control (arrived state submit)).raw) (n : Nat) :=
  RoundEpisodeConsumer.every_communication_attempt_consumes_native_responsibility_even_when_blocked
    (arrived state submit) (control (arrived state submit)) entry n
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedConsumer
