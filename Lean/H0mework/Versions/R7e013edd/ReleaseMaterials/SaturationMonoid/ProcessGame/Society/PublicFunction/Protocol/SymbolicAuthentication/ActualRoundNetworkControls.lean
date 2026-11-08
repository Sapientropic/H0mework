import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkControls
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ActualRoundNetworkSource ActualRoundNetworkConsumer

abbrev firstState := DonorRegenerationControls.ready DonorRegenerationControls.seed
abbrev secondState := DonorRegenerationControls.ready DonorRegenerationControls.first
abbrev raw (state : RoundEpisodeSource.State) := (UpstreamProductionSource.command state).raw

def network (state : RoundEpisodeSource.State) (settings : Settings := {})
    (admitted : (inspect state (raw state) settings).isSome) : Network :=
  (inspect state (raw state) settings).get admitted

def first := network firstState {} (by decide +kernel)
def second := network secondState {} (by decide +kernel)
def firstSubject := (completion first).get (by decide +kernel)
def secondSubject := (completion second).get (by decide +kernel)

theorem actual_paid_reproduction_generates_both_network_completion_results :
    status firstState (raw firstState) = .completed ∧ status secondState (raw secondState) = .completed ∧
      completion first = some firstSubject ∧ completion second = some secondSubject ∧
      firstSubject.2.priorClaim = 7 ∧ secondSubject.2.priorClaim = 6 ∧
      firstSubject.1.scope ≠ secondSubject.1.scope := by decide +kernel

theorem first_actual_round_consumes_every_compliant_history_callback
    (rivals : Nat → Opponent (code first)) (within : Within first rivals (window first)) :
    result first (finished first rivals) = .decided true firstSubject ∧ PaymentConsumed first firstSubject rivals :=
  ⟨generated_completion_covers_arbitrary_compliant_history_callbacks first firstSubject
    actual_paid_reproduction_generates_both_network_completion_results.2.2.1 rivals within,
   generated_completion_consumes_actual_payment_whole_ledger_and_next first firstSubject
    actual_paid_reproduction_generates_both_network_completion_results.2.2.1 rivals within⟩

theorem second_actual_round_consumes_every_compliant_history_callback
    (rivals : Nat → Opponent (code second)) (within : Within second rivals (window second)) :
    result second (finished second rivals) = .decided true secondSubject ∧ PaymentConsumed second secondSubject rivals :=
  ⟨generated_completion_covers_arbitrary_compliant_history_callbacks second secondSubject
    actual_paid_reproduction_generates_both_network_completion_results.2.2.2.1 rivals within,
   generated_completion_consumes_actual_payment_whole_ledger_and_next second secondSubject
    actual_paid_reproduction_generates_both_network_completion_results.2.2.2.1 rivals within⟩

abbrev latest (net : Network) : Nat → Opponent (code net) := fun _ => QueueScheduler.opponent (code net) (OriginQueue.baseline (start net))
abbrev delayed (net : Network) : Nat → Opponent (code net) := fun cut => if cut = 3 then EventStep.fixed none else latest net cut
abbrev deviation (net : Network) : Nat → Opponent (code net) := fun cut history past frame =>
  if frame.sent.isEmpty then some ⟨.activate 0,by simp [code,RoundArchive.code]⟩ else delayed net cut history past frame
abbrev silent (net : Network) : Nat → Opponent (code net) := fun _ => EventStep.fixed none

def conforms (net : Network) (rivals : Nat → Opponent (code net)) : Bool :=
  (List.range (window net)).all fun index => decide
    (intake net (actual net rivals index) (rivals (actual net rivals index).cursor.cut) ∈ choices net (actual net rivals index))
theorem conforms_iff (net : Network) (rivals : Nat → Opponent (code net)) :
    conforms net rivals = true ↔ Within net rivals (window net) := by
  simp only [conforms,Within,List.all_eq_true,List.mem_range,decide_eq_true_eq]

theorem delayed_delivery_and_rejected_impersonation_still_complete :
    Within first (delayed first) (window first) ∧ Within second (deviation second) (window second) ∧
      result first (finished first (delayed first)) = .decided true firstSubject ∧
      result second (finished second (deviation second)) = .decided true secondSubject ∧
      (material second (actual second (deviation second) 1) (deviation second 1)).call = .external (some ⟨.activate 0,by decide⟩) ∧
      StageTransport.admission (material second (actual second (deviation second) 1) (deviation second 1)) = none := by
  have one : Within first (delayed first) (window first) := (conforms_iff _ _).mp (by decide +kernel)
  have two : Within second (deviation second) (window second) := (conforms_iff _ _).mp (by decide +kernel)
  exact ⟨one,two,(first_actual_round_consumes_every_compliant_history_callback _ one).1,
    (second_actual_round_consumes_every_compliant_history_callback _ two).1,by decide +kernel⟩

def noTiming := network firstState ⟨1,0,1⟩ (by decide +kernel)
def noQuorum := network firstState ⟨1,3,2⟩ (by decide +kernel)
def noBoundedDelivery := network firstState ⟨3,7,1⟩ (by decide +kernel)
def timingWitness := (obstruction noTiming).get (by decide +kernel)
def deliveryWitness := (obstruction noBoundedDelivery).get (by decide +kernel)

theorem missing_timing_quorum_and_delivery_generate_concrete_failures :
    status firstState (raw firstState) ⟨1,0,1⟩ = .obstructed ∧
      status firstState (raw firstState) ⟨1,3,2⟩ = .obstructed ∧
      status firstState (raw firstState) ⟨3,7,1⟩ = .obstructed ∧
      completion noTiming = none ∧ completion noQuorum = none ∧ completion noBoundedDelivery = none ∧
      result noTiming timingWitness = .blocked .missingQuorum ∧
      result noBoundedDelivery deliveryWitness = .blocked .missingQuorum ∧
      obstruction noTiming = some timingWitness ∧ obstruction noBoundedDelivery = some deliveryWitness := by
  and_intros
  all_goals first | exact (Option.some_get _).symm | decide +kernel

abbrev timingSource := generated_obstruction_is_an_executable_original_source_branch noTiming timingWitness
  missing_timing_quorum_and_delivery_generate_concrete_failures.2.2.2.2.2.2.2.2.1
abbrev deliverySource := generated_obstruction_is_an_executable_original_source_branch noBoundedDelivery deliveryWitness
  missing_timing_quorum_and_delivery_generate_concrete_failures.2.2.2.2.2.2.2.2.2

abbrev timingResponsibility := failed_branch_still_consumes_its_actual_whole_ledger_and_next noTiming timingWitness
  missing_timing_quorum_and_delivery_generate_concrete_failures.2.2.2.2.2.2.2.2.1
abbrev deliveryResponsibility := failed_branch_still_consumes_its_actual_whole_ledger_and_next noBoundedDelivery deliveryWitness
  missing_timing_quorum_and_delivery_generate_concrete_failures.2.2.2.2.2.2.2.2.2

theorem silence_outside_the_default_envelope_is_blocked :
    conforms first (silent first) = false ∧
      result first (finished first (silent first)) = .blocked .missingQuorum := by decide +kernel

def staleEncoding : StageTransport.Encoding (code := code second) := fun signal =>
  if signal = 1 then some ⟨0,0,0,1,firstSubject.1.scope,true,1⟩ else none

theorem removing_the_payment_receipt_or_replaying_an_old_scope_refuses :
    StagePaymentQuorum.resolveRows (vocabulary second) (finished second (latest second)).rows.tail (scope second) = none ∧
      StagePaymentQuorum.produce (vocabulary second) (start second) (fun _ => none) (reception second)
        (finished second (latest second)).stages 0 (scope second) 1 = .blocked .missingQuorum ∧
      StagePaymentQuorum.produce (vocabulary second) (start second) staleEncoding (reception second)
        (finished second (latest second)).stages 0 (scope second) 1 = .blocked .missingQuorum := by
  and_intros <;> decide +kernel

theorem wrong_signer_and_depleted_upstream_never_become_network_completion :
    status DonorRegenerationControls.seed DonorRegenerationControls.forged = .admissionRefused ∧
      status (DonorRegenerationControls.ready DonorRegenerationControls.second)
        (raw (DonorRegenerationControls.ready DonorRegenerationControls.second)) = .admissionRefused := by
  and_intros <;> decide +kernel

abbrev firstResponsibility := (first_actual_round_consumes_every_compliant_history_callback (delayed first)
  delayed_delivery_and_rejected_impersonation_still_complete.1).2
abbrev secondResponsibility := (second_actual_round_consumes_every_compliant_history_callback (deviation second)
  delayed_delivery_and_rejected_impersonation_still_complete.2.1).2
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkControls
