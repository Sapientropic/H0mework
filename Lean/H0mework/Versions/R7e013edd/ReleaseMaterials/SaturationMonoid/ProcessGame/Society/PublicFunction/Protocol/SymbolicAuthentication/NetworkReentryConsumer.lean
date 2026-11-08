import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentrySource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentryConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ActualRoundNetworkSource NetworkReentrySource

theorem completed_occurrence_consumes_its_native_ledger_and_next (attempt : Attempt) :
    RoundEpisodeConsumer.NativeConsumed (model attempt) (completedOrdinal attempt) (disposition attempt) :=
  RoundEpisodeConsumer.native_generated_consumed _ _

theorem completed_occurrence_is_in_the_actual_successor (attempt : Attempt) :
    RoundEpisodeSource.Archive.native (model attempt) (completedOrdinal attempt) (disposition attempt) ∈
      (after attempt).archive := by simp [after]

theorem admitted_network_uses_the_actual_prepared_state (state : State) (produce feed : Bool)
    (settings : Settings) (net : Network) (made : NetworkReentrySource.inspect state produce feed settings = some net) :
    net.state = prepared state produce feed := by
  unfold NetworkReentrySource.inspect ActualRoundNetworkSource.inspect at made
  cases same : RoundEpisodeSource.inspect (prepared state produce feed) (incoming state produce feed) with
  | none => simp [same] at made
  | some entry => simp only [same,Option.map_some,Option.some.injEq] at made; subst net; rfl

theorem admitted_network_preserves_the_original_material_law (net : Network) :
    (code net).law = net.state.model.source.code.law :=
  net.entry.bound.law_exact.trans net.state.model.law_exact.symm

theorem admitted_next_uses_the_actual_network_endpoint (state : State) (produce feed : Bool)
    (settings : Settings) (callbacks : Callbacks) (net : Network)
    (made : NetworkReentrySource.inspect state produce feed settings = some net) :
    next state produce feed settings callbacks =
      ⟨after (execute net (callbacks net)),state.evidence ++ [execute net (callbacks net)]⟩ := by
  simp only [next,made]

theorem every_next_retains_all_actual_attempts (state : State) (produce feed : Bool)
    (settings : Settings) (callbacks : Callbacks) :
    ∃ added, (next state produce feed settings callbacks).evidence = state.evidence ++ added := by
  unfold next
  split <;> simp

theorem every_next_retains_all_original_archives (state : State) (produce feed : Bool)
    (settings : Settings) (callbacks : Callbacks) :
    ∃ added, (next state produce feed settings callbacks).episode.archive = state.episode.archive ++ added := by
  have prior : ∃ added, (prepared state produce feed).archive = state.episode.archive ++ added := by
    exact ⟨[RoundEpisodeSource.Archive.native (DonorRegenerationSource.productionModel state.episode produce)
        (MaterialRoundSource.depth state.episode.model state.episode.cut) (DonorRegenerationSource.disposition state.episode produce)] ++
        [RoundEpisodeSource.Archive.native (UpstreamFeedSource.arrivalModel (DonorRegenerationSource.generated state.episode produce) feed)
          (MaterialRoundSource.depth (DonorRegenerationSource.generated state.episode produce).model (state.episode.cut+1))
          (UpstreamFeedSource.disposition (DonorRegenerationSource.generated state.episode produce) feed)],
        by simp only [prepared,UpstreamFeedSource.arrived,DonorRegenerationSource.generated,List.append_assoc]⟩
  obtain ⟨old,sameOld⟩ := prior
  unfold next
  split
  · obtain ⟨fresh,sameNew⟩ := RoundEpisodeConsumer.each_actual_next_retains_every_old_archive_record
      (prepared state produce feed) (RoundEpisodeSource.normal (prepared state produce feed) (incoming state produce feed))
    exact ⟨old ++ fresh,sameNew.trans (by rw [sameOld];simp only [List.append_assoc])⟩
  · rename_i net made
    have bound := admitted_network_uses_the_actual_prepared_state state produce feed settings net made
    refine ⟨old ++ RoundEpisodeSource.nativeArchive net.state (RoundEpisodeSource.normal net.state net.raw) ++
      [.native (model (execute net (callbacks net))) (completedOrdinal (execute net (callbacks net)))
        (disposition (execute net (callbacks net)))],?_⟩
    dsimp only [after,execute]
    rw [bound,sameOld]
    simp only [List.append_assoc]

theorem every_later_callback_keeps_all_actual_attempts
    (initial : State) (produce feed : State → Bool) (settings : State → Settings)
    (callbacks : State → Callbacks) (n : Nat) :
    ∃ added, (NetworkReentrySource.run initial produce feed settings callbacks n).evidence = initial.evidence ++ added := by
  induction n with
  | zero => exact ⟨[],(List.append_nil _).symm⟩
  | succ n prior =>
    obtain ⟨old,sameOld⟩ := prior
    obtain ⟨fresh,sameNew⟩ := every_next_retains_all_actual_attempts
      (NetworkReentrySource.run initial produce feed settings callbacks n) _ _ _ _
    exact ⟨old ++ fresh,sameNew.trans (by rw [sameOld];simp only [List.append_assoc])⟩

theorem every_later_callback_keeps_all_original_archives
    (initial : State) (produce feed : State → Bool) (settings : State → Settings)
    (callbacks : State → Callbacks) (n : Nat) :
    ∃ added, (NetworkReentrySource.run initial produce feed settings callbacks n).episode.archive = initial.episode.archive ++ added := by
  induction n with
  | zero => exact ⟨[],(List.append_nil _).symm⟩
  | succ n prior =>
    obtain ⟨old,sameOld⟩ := prior
    obtain ⟨fresh,sameNew⟩ := every_next_retains_all_original_archives
      (NetworkReentrySource.run initial produce feed settings callbacks n) _ _ _ _
    exact ⟨old ++ fresh,sameNew.trans (by rw [sameOld];simp only [List.append_assoc])⟩

theorem generated_primitive_balances_cover_every_compliant_actual_endpoint
    (net : Network) (checked : replenishable net = true)
    (callbacks : Nat → Opponent (code net)) (within : Within net callbacks (window net)) :
    WorkerInputSource.Needed (RoundEpisodeSource.current (after (execute net callbacks))) ∧
      DonorRegenerationLaw.Inputs (RoundEpisodeSource.current (after (execute net callbacks))) := by
  obtain ⟨node,member,same⟩ := ActualRoundNetworkConsumer.every_compliant_actual_callback_has_a_generated_branch
    net callbacks (window net) within
  have primitive := (List.all_eq_true.mp checked) node member
  have states := ActualRoundNetworkConsumer.related_states net node _
    (generated_valid net _ node member) (actual_valid net callbacks _) same
  rw [successor_current_is_the_actual_final_feedback_state]
  change WorkerInputSource.Needed (ActualRoundNetworkConsumer.finished net callbacks).state.current ∧
    DonorRegenerationLaw.Inputs (ActualRoundNetworkConsumer.finished net callbacks).state.current
  rw [← states]
  exact decide_eq_true_eq.mp primitive

theorem every_compliant_endpoint_generates_actual_paid_donor_fuel_and_feed
    (net : Network) (checked : replenishable net = true)
    (law : (code net).law = DonorRegenerationLaw.law)
    (callbacks : Nat → Opponent (code net)) (within : Within net callbacks (window net)) :
    let state := after (execute net callbacks)
    DonorRegenerationSource.incoming state true = DonorRegenerationLaw.word ∧
      RoundEpisodeSource.current (DonorRegenerationSource.generated state true) =
        DonorRegenerationLaw.successor (RoundEpisodeSource.current state) ∧
      UpstreamFeedSource.select (DonorRegenerationSource.generated state true) true = .offered := by
  have inputs := generated_primitive_balances_cover_every_compliant_actual_endpoint net checked callbacks within
  exact DonorRegenerationSource.actual_new_donor_fuel_generates_the_original_feed _ law inputs.1 inputs.2

abbrev donorResponsibility (attempt : Attempt) :=
  DonorRegenerationConsumer.actual_production_consumes_its_native_ledger_and_next (after attempt) true
abbrev feedResponsibility (attempt : Attempt) :=
  DonorRegenerationConsumer.supplyResponsibility (after attempt) true true
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentryConsumer
