import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RoundEpisodeSource RoundEpisodePrefix
open DonorRegenerationSource

theorem arrival_boundary (state : State) (produce : Bool) :
    boundary (generated state produce) = boundary state+1 := by
  change state.model.source.history.length+2+(state.cut+1) = _
  dsimp only [boundary]
  omega

theorem arrival_prefix (state : State) (produce : Bool) :
    Prefix state.model.source.input (generated state produce).model.source.input (boundary state) := by
  apply (an_actual_continuation_keeps_the_complete_original_prefix state.model state.cut (incoming state produce)).weaken
  dsimp [boundary,MaterialRoundSource.depth,Machine.Continuation.depth]
  omega

theorem next_prefix (state : State) (produce feed : Bool) (control : Controller) :
    Prefix state.model.source.input (DonorRegenerationSource.next state produce feed control).model.source.input (boundary state) :=
  (arrival_prefix state produce).trans
    ((UpstreamFeedConsumer.next_prefix (generated state produce) feed control).weaken
      (by rw [arrival_boundary];omega))

theorem next_boundary (state : State) (produce feed : Bool) (control : Controller) :
    boundary state+6 ≤ boundary (DonorRegenerationSource.next state produce feed control) := by
  have step := UpstreamFeedConsumer.next_boundary (generated state produce) feed control
  rw [arrival_boundary] at step
  omega

theorem run_boundary (initial : State) (produce feed : State → Bool) (control : Controller) (n : Nat) :
    boundary initial+6*n ≤ boundary (DonorRegenerationSource.run initial produce feed control n) := by
  induction n with
  | zero => change boundary initial+6*0 ≤ boundary initial;omega
  | succ n prior =>
    have step := next_boundary (DonorRegenerationSource.run initial produce feed control n)
      (produce (DonorRegenerationSource.run initial produce feed control n))
      (feed (DonorRegenerationSource.run initial produce feed control n)) control
    change boundary initial+6*(n+1) ≤ boundary (DonorRegenerationSource.next
      (DonorRegenerationSource.run initial produce feed control n) (produce (DonorRegenerationSource.run initial produce feed control n))
      (feed (DonorRegenerationSource.run initial produce feed control n)) control)
    omega

theorem run_prefix (initial : State) (produce feed : State → Bool) (control : Controller) (n : Nat) :
    Prefix initial.model.source.input (DonorRegenerationSource.run initial produce feed control n).model.source.input (boundary initial) := by
  induction n with
  | zero => exact ⟨rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩
  | succ n prior =>
    have growing := run_boundary initial produce feed control n
    exact prior.trans ((next_prefix (DonorRegenerationSource.run initial produce feed control n)
      (produce (DonorRegenerationSource.run initial produce feed control n))
      (feed (DonorRegenerationSource.run initial produce feed control n)) control).weaken (by omega))

theorem every_later_control_keeps_all_original_financial_accounts
    (initial : State) (produce feed : State → Bool) (control : Controller) (n ordinal : Nat)
    (earlier : ordinal ≤ boundary initial) :
    Native.Coupling.Match initial.model.source.code initial.model.source.input
      (DonorRegenerationSource.run initial produce feed control n).model.source.input
      (Financial.accountAt initial.model.source.input ordinal)
      (Financial.accountAt (DonorRegenerationSource.run initial produce feed control n).model.source.input ordinal) := by
  have prior := run_prefix initial produce feed control n
  have events : ∀ cut, cut < boundary initial →
      ProgrammeSource.rawEvent (DonorRegenerationSource.run initial produce feed control n).model.source.input
        (ProgrammeHistory.visitAt initial.model.source.input cut).current =
      ProgrammeSource.rawEvent initial.model.source.input (ProgrammeHistory.visitAt initial.model.source.input cut).current := by
    intro cut inside
    exact (congrArg (ProgrammeSource.rawEvent (DonorRegenerationSource.run initial produce feed control n).model.source.input)
      (prior.currents cut (by omega)).symm).trans (prior.words cut inside)
  exact Native.Coupling.History.complete_accounts initial.model.source.code initial.model.source.input
    (DonorRegenerationSource.run initial produce feed control n).model.source.input prior.law prior.initial (boundary initial) events
    initial.model.source.body (DonorRegenerationSource.run initial produce feed control n).model.source.body rfl rfl ordinal earlier

theorem actual_production_consumes_its_native_ledger_and_next (state : State) (submit : Bool) :
    RoundEpisodeConsumer.NativeConsumed (productionModel state submit) (MaterialRoundSource.depth state.model state.cut)
      (disposition state submit) := RoundEpisodeConsumer.native_generated_consumed _ _

theorem every_next_retains_all_original_archives (state : State) (produce feed : Bool) (control : Controller) :
    ∃ added, (DonorRegenerationSource.next state produce feed control).archive = state.archive ++ added := by
  obtain ⟨more,same⟩ := UpstreamFeedConsumer.every_later_controller_receives_all_original_archives
    (generated state produce) (fun _ => feed) control 1
  refine ⟨[Archive.native (productionModel state produce) (MaterialRoundSource.depth state.model state.cut)
    (disposition state produce)] ++ more,?_⟩
  exact same.trans (by simp only [generated,List.append_assoc])

theorem production_remains_in_actual_next (state : State) (produce feed : Bool) (control : Controller) :
    Archive.native (productionModel state produce) (MaterialRoundSource.depth state.model state.cut) (disposition state produce) ∈
      (DonorRegenerationSource.next state produce feed control).archive := by
  obtain ⟨more,same⟩ := UpstreamFeedConsumer.every_later_controller_receives_all_original_archives
    (generated state produce) (fun _ => feed) control 1
  change Archive.native _ _ _ ∈ (UpstreamFeedSource.run (generated state produce) (fun _ => feed) control 1).archive
  rw [same]
  exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

theorem every_later_controller_receives_all_original_archives
    (initial : State) (produce feed : State → Bool) (control : Controller) (n : Nat) :
    ∃ added, (DonorRegenerationSource.run initial produce feed control n).archive = initial.archive ++ added := by
  induction n with
  | zero => exact ⟨[],(List.append_nil _).symm⟩
  | succ n prior =>
    obtain ⟨old,sameOld⟩ := prior
    obtain ⟨fresh,sameNew⟩ := every_next_retains_all_original_archives
      (DonorRegenerationSource.run initial produce feed control n)
      (produce (DonorRegenerationSource.run initial produce feed control n))
      (feed (DonorRegenerationSource.run initial produce feed control n)) control
    exact ⟨old ++ fresh,sameNew.trans (by rw [sameOld];simp only [List.append_assoc])⟩

theorem actual_donor_production_restores_the_original_preparation_capacity (state : State)
    (same : state.model.source.code.law = DonorRegenerationLaw.law)
    (needed : WorkerInputSource.Needed (current state))
    (inputs : DonorRegenerationLaw.Inputs (current state)) :
    let fresh := UpstreamFeedSource.arrived (generated state true) true
    WorkerInputSource.incoming (rawSource fresh (UpstreamProductionSource.incoming fresh)) (fresh.cut+1) = WorkerInputLaw.word ∧
      let finish := MaterialRoundSource.prepared (supplied fresh (UpstreamProductionSource.incoming fresh))
        (count fresh) (arrival fresh (UpstreamProductionSource.incoming fresh))
      finish.stock 0 .feedstock = 0 ∧
      finish.stock 0 .energy = (current state).stock 0 .energy ∧
      finish.stock 0 .labor = (current state).stock 0 .labor ∧
      finish.stock 1 .waste = (current state).stock 1 .waste-2 ∧
      finish.stock 1 .service = (current state).stock 1 .service+3 ∧
      finish.stock 2 .energy = (current state).stock 2 .energy ∧
      finish.stock 2 .labor = (current state).stock 2 .labor ∧
      finish.claims = (current state).claims ∧ finish.technology = (current state).technology := by
  have produced := actual_new_donor_fuel_generates_the_original_feed state same needed inputs
  have demand : UpstreamFeedSource.Demand (generated state true) := by
    change WorkerInputSource.Needed (current (generated state true)) ∧
      ¬ WorkerInputLaw.Inputs (current (generated state true)) ∧ ¬ UpstreamProductionLaw.Inputs (current (generated state true))
    rw [produced.2.1]
    exact DonorRegenerationLaw.new_fuel_leaves_the_worker_deficit_visible _ inputs needed
  have resources : UpstreamFeedLaw.Resources (current (generated state true)) :=
    produced.2.1 ▸ DonorRegenerationLaw.new_fuel_has_original_paid_inputs _ inputs
  have consumed := UpstreamFeedConsumer.actual_external_supply_funds_the_original_preparation
    (generated state true) same demand resources
  rw [produced.2.1] at consumed
  dsimp only at consumed ⊢
  obtain ⟨worker,fuel,energy,labor,waste,service,workerEnergy,workerLabor,claims,technology⟩ := consumed
  refine ⟨worker,fuel,?_,?_,?_,?_,?_,?_,claims,technology⟩
  · simpa [DonorRegenerationLaw.successor] using energy
  · simpa [DonorRegenerationLaw.successor] using labor
  · convert waste using 1
    simp [DonorRegenerationLaw.successor]
    ring
  · simpa [DonorRegenerationLaw.successor] using service
  · simpa [DonorRegenerationLaw.successor] using workerEnergy
  · simpa [DonorRegenerationLaw.successor] using workerLabor

abbrev supplyResponsibility (state : State) (produce feed : Bool) :=
  UpstreamFeedConsumer.every_feed_occurrence_consumes_its_native_responsibility_ledger_and_next
    (generated state produce) feed
abbrev preparationResponsibility (state : State) (produce feed : Bool) :=
  UpstreamFeedConsumer.productionConsumes (generated state produce) feed
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationConsumer
