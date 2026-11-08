import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ConcreteProductiveSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ConcreteProductiveConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource
open ProductiveSigningSource (total current decisions prepared producedCount increment acceptance_checks_the_actual_full_cycle)

theorem the_literal_cycle_generates_net_service_original_claims_and_a_new_actual_quorum :
 total before .service+3≤total endpoint .service ∧
 (current endpoint).claims=(current before).claims ∧
 (∃ row∈endpoint.rows.drop before.rows.length,
  ∃ item∈StageTrace.items row.actual, ∃ operator,
  item.request.operation=.produce operator ∧ row.code.law.Valid item.before item.request) ∧
 (∃ answer∈decisions contract base laws request 1 candidate,
  FreshSigningConsumer.decision contract base laws (prepared contract request candidate) request answer.1 1=.decided answer.2) := by
 have facts := acceptance_checks_the_actual_full_cycle contract base laws request .service 3 1 before candidate
  the_actual_full_cycle_has_three_net_service_units_and_a_new_quorum
 have nonempty := List.isEmpty_eq_false_iff.mp facts.2.2.2
 obtain ⟨answer,member⟩ := List.exists_mem_of_ne_nil _ nonempty
 exact ⟨facts.1,
  ProductiveSigningConsumer.accepted_claims_are_the_entire_original_financial_matrix contract base laws request .service 3 1 before candidate
   the_actual_full_cycle_has_three_net_service_units_and_a_new_quorum,
  ProductiveSigningConsumer.accepted_growth_contains_a_new_actual_valid_production_occurrence contract base laws request .service 3 1 before candidate
   the_actual_full_cycle_has_three_net_service_units_and_a_new_quorum,
  answer,member,ProductiveSigningConsumer.every_readout_is_an_actual_new_global_quorum contract base laws request 1 candidate answer member⟩

theorem the_same_literal_cycle_opens_the_actual_paid_window :
 (RenewableArchiveSource.window contract ready.actual true true).status=.opened :=
 (RenewableArchiveSource.admitted_payment_generates_the_exact_next_window contract ready.actual true true
  the_current_waste_transfer_and_provider_acceptance_buy_the_new_window).1

theorem the_same_literal_cycle_keeps_all_prior_history_and_its_own_next :
 before.actual.archive <+: endpoint.actual.archive ∧ before.actual.windows <+: endpoint.actual.windows ∧
 before.rows <+: endpoint.rows ∧
 ArchivedDeliveryConsumer.NativeContinuation endpoint.actual.model endpoint.actual.point := by
 have first := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows contract before commands
 have second := FreshSigningSource.every_paid_cycle_retains_all_original_archives_windows_and_rows contract base laws ready request
 exact ⟨first.1.trans second.1,first.2.1.trans second.2.1,first.2.2.trans second.2.2,
  JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩

-- Consume the selected source equation before instantiating the concrete search.
private theorem one_selected_step_counts
 (state : JointReceptionSource.State bound.source.code) (depth : Nat)
 (branch : SourceRepairSearch.Branch bound.source.code) (positive : (0 : ℚ)<3)
 (generated : branch∈SourceRepairSearch.cases contract depth state)
 (checked : ProductiveSigningSource.accepts contract base laws request .service 3 1 state branch=true)
 (selected : ProductiveSigningSource.produce contract base laws request .service 3 1 state depth=
  .produced branch positive generated checked) :
 producedCount contract base laws request .service 3 1 state depth 1=1 := by
 change 0+increment contract base laws request .service 3 1 state depth=1
 simp only [increment,selected,Nat.zero_add]

theorem the_computed_source_success_count_is_one :
 producedCount contract base laws request .service 3 1 before 2 1=1 := by
 obtain ⟨branch,positive,generated,checked,selected⟩ := the_original_source_producer_computes_a_positive_success
 exact one_selected_step_counts before 2 branch positive generated checked selected

private theorem inventory_run (depth count : Nat) :
 ProductiveSigningArchive.sourceRun bound contract base laws genesis parent scope true (fun _ => request) 0 0 0
  request .service 3 1 depth count=
 ProductiveSigningArchive.run bound contract base laws genesis parent scope true (fun _ => request) 0 0 0
  request .service 3 1 depth count := by
 have party : Fintype.ofList bound.source.code.parties bound.source.code.parties_cover =
  (inferInstance : Fintype Delegation.Funded.Party) := Subsingleton.elim _ _
 have instrument : Fintype.ofList bound.source.code.instruments bound.source.code.instruments_cover =
  (inferInstance : Fintype Unit) := Subsingleton.elim _ _
 unfold ProductiveSigningArchive.sourceRun
 rw [party,instrument]

theorem the_public_inventory_run_generates_a_positive_original_source_success :
 ∃ final,
 ProductiveSigningArchive.sourceRun bound contract base laws genesis parent scope true (fun _ => request) 0 0 0
  request .service 3 1 2 1=some final ∧
 total before .service+3≤total final .service ∧
 (current final).claims=(current before).claims ∧
 before.actual.archive <+: final.actual.archive ∧ before.actual.windows <+: final.actual.windows ∧
 before.rows <+: final.rows ∧
 ArchivedDeliveryConsumer.NativeContinuation final.actual.model final.actual.point := by
 rw [inventory_run]
 obtain ⟨final,actual,net,claims,history⟩ :=
  ProductiveSigningArchive.the_public_run_keeps_the_original_finances_and_counts_actual_net_production
   bound contract base laws genesis parent scope true (fun _ => request) 0 0 0 request .service 3 1 before
   the_public_entry_recognizes_the_original_slot 2 1
 rw [the_computed_source_success_count_is_one] at net
 norm_num only [Nat.cast_one,one_mul] at net
 exact ⟨final,actual,net,claims,history⟩

theorem deleting_the_original_slot_cannot_produce_the_positive_run :
 ProductiveSigningArchive.sourceRun bound contract base laws genesis parent scope true (fun _ => request) 1 0 0
  request .service 3 1 2 1=none := rfl

theorem the_literal_cycle_refuses_a_fictitious_extra_net_unit :
 ProductiveSigningSource.accepts contract base laws request .service 4 1 before candidate=false := by
 apply Bool.eq_false_iff.mpr
 intro accepted
 have net := (acceptance_checks_the_actual_full_cycle contract base laws request .service 4 1 before candidate accepted).1
 have actual := the_literal_full_cycle_has_exact_total_service_and_the_original_debt
 change total before .service+4≤total endpoint .service at net
 rw [actual.1,actual.2.2.1] at net
 norm_num at net

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ConcreteProductiveConsumer
