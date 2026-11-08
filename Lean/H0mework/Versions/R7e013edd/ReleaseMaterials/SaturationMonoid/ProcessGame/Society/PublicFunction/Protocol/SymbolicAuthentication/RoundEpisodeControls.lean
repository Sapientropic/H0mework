import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RoundEpisodeSource

def funded : State := ⟨WorkerInputControls.doubleFunded,0,[]⟩
def normalControl : Controller := fun state => normal state

def silent (state : State) : Command state :=
  ⟨[],(normal state).localRule,fun _ => fun _ _ _ => none⟩
def recoveringControl : Controller := fun state => if state.archive.isEmpty then silent state else normal state

abbrev first := next funded (normal funded)
abbrev second := next first (normal first)
abbrev silentFirst := next funded (silent funded)
abbrev recovered := next silentFirst (normal silentFirst)

theorem the_first_actual_round_consumes_real_upstream_inputs :
    status funded (normal funded) = .decided true ∧
      (current first).claims () 1 2 = 6 ∧ (current first).stock 0 .energy = 1 ∧
      (current first).stock 0 .labor = 2 ∧ (current first).stock 1 .waste = 2 ∧
      (current first).stock 1 .service = 0 ∧ first.archive.length = 6 := by decide +kernel

theorem the_second_round_consumes_the_first_rounds_literal_endpoint :
    RoundEpisodeSource.run funded normalControl 2 = second ∧ status first (normal first) = .decided true ∧
      (current second).claims () 1 2 = 5 ∧ (current second).stock 0 .energy = 0 ∧
      (current second).stock 0 .labor = 1 ∧ (current second).stock 1 .waste = 1 ∧
      (current second).stock 1 .service = 0 ∧ second.archive.length = 12 := by
  refine ⟨rfl,?_⟩
  decide +kernel

theorem exhausted_upstream_resources_remain_a_real_refusal_on_the_actual_next :
    status second (normal second) = .phaseRefused ∧
      (current (next second (normal second))).claims () 1 2 = 5 ∧
      (next second (normal second)).archive.length = 17 := by decide +kernel

def archivedDecisions (records : List Archive) : List MaterialRoundConsumer.Status := records.filterMap fun record =>
  match record with
  | .communication communication => some (match communication.decision with
      | .blocked reason => .blocked reason
      | .decided value _ => .decided value)
  | _ => none

theorem absent_delivery_blocks_without_erasing_actual_payment_or_the_next_round :
    status funded (silent funded) = .blocked .missingQuorum ∧
      (current silentFirst).claims () 1 2 = 6 ∧ (current silentFirst).stock 1 .service = 1 ∧
      status silentFirst (normal silentFirst) = .decided true ∧
      (current recovered).claims () 1 2 = 5 ∧ (current recovered).stock 1 .service = 1 ∧
      archivedDecisions recovered.archive = [.blocked .missingQuorum,.decided true] := by decide +kernel

theorem the_controller_can_change_behavior_from_its_own_retained_history :
    archivedDecisions (RoundEpisodeSource.run funded recoveringControl 2).archive = [.blocked .missingQuorum,.decided true] := by decide +kernel

abbrev forged : List RecycledQuorumMaterial.Action := WorkerInputControls.tampered
abbrev corrupt := next funded (normal funded forged)
theorem a_wrong_signer_is_recorded_and_never_mints_a_decision_in_a_later_round :
    status funded (normal funded forged) = .historyRefused ∧
      status corrupt (normal corrupt) = .historyRefused ∧
      (MaterialRoundSource.before (rawSource funded forged) (funded.cut+1)).stock 0 .energy = 2 ∧
      (next corrupt (normal corrupt)).archive.length = 10 ∧
      archivedDecisions (next corrupt (normal corrupt)).archive = [] := by decide +kernel

theorem arbitrary_later_controls_consume_the_uniform_prefix_theorem (control : Controller) (n ordinal : Nat)
    (earlier : ordinal ≤ boundary funded) :
    Native.Coupling.Match funded.model.source.code funded.model.source.input (RoundEpisodeSource.run funded control n).model.source.input
      (Financial.accountAt funded.model.source.input ordinal) (Financial.accountAt (RoundEpisodeSource.run funded control n).model.source.input ordinal) :=
  RoundEpisodeConsumer.original_financial_accounts_survive_arbitrary_later_controls funded control n ordinal earlier

theorem every_actual_preparation_has_original_liability_and_next :
    RoundEpisodeConsumer.NativeConsumed (rawSource funded []) (MaterialRoundSource.depth funded.model funded.cut)
      (produce funded (normal funded)).rawDisposition ∧
    RoundEpisodeConsumer.NativeConsumed (supplied funded []) (MaterialRoundSource.depth (rawSource funded []) (funded.cut+1))
      (produce funded (normal funded)).upstreamDisposition ∧
    RoundEpisodeConsumer.NativeConsumed (MaterialRoundSource.supplied (supplied funded []) (count funded) (arrival funded []))
      (MaterialRoundSource.depth (supplied funded []) (count funded)) (produce funded (normal funded)).fuelDisposition ∧
    RoundEpisodeConsumer.NativeConsumed (residual funded []) (MaterialRoundSource.depth (supplied funded []) (count funded)+1)
      (produce funded (normal funded)).recoveryDisposition :=
  RoundEpisodeConsumer.all_four_real_preparation_occurrences_consume_their_own_ledger_and_next funded (normal funded)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeControls
