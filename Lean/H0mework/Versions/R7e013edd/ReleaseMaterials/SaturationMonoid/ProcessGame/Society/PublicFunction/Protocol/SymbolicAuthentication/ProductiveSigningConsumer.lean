import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveSigningSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveSigningConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage ProductiveSigningSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 [Fintype Party] [Fintype Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (laws : (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) → StageReception.Law model.source.code)
 (request : FreshSigningSource.Request (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (good : Good) (quota : ℚ) (threshold : Nat)

omit [Fintype Party] [Fintype Instrument] in
theorem every_readout_is_an_actual_new_global_quorum
 (branch : SourceRepairSearch.Branch root)
 (answer : Fin (prepared contract request branch).actual.model.source.code.sites × Bool)
 (inside : answer∈decisions contract base laws request threshold branch) :
 FreshSigningConsumer.decision contract base laws (prepared contract request branch) request answer.1 threshold=.decided answer.2 := by
 obtain ⟨recipient,_,found⟩ := List.mem_filterMap.mp inside
 cases actual : FreshSigningConsumer.decision contract base laws (prepared contract request branch) request recipient threshold with
 | blocked reason => simp only [actual] at found;contradiction
 | decided value =>
   simp only [actual,Option.some.injEq] at found
   cases found
   exact actual

omit [Fintype Party] [Fintype Instrument] in
theorem all_actual_readouts_of_a_selected_cycle_agree
 (branch : SourceRepairSearch.Branch root)
 (one two : Fin (prepared contract request branch).actual.model.source.code.sites × Bool)
 (first : one∈decisions contract base laws request threshold branch)
 (second : two∈decisions contract base laws request threshold branch) : one.2=two.2 := by
 have left := every_readout_is_an_actual_new_global_quorum contract base laws request threshold branch one first
 have right := every_readout_is_an_actual_new_global_quorum contract base laws request threshold branch two second
 rw [FreshSigningConsumer.the_new_decision_consumes_the_independent_global_receiver] at left right
 exact JointReceptionConsumer.all_generated_endpoint_decisions_agree
  (FreshSigningConsumer.vocabulary base laws (prepared contract request branch) request)
  (FreshSigningConsumer.reception base laws (prepared contract request branch) request)
  (FreshSigningConsumer.start base laws (prepared contract request branch) request)
  (FreshSigningConsumer.issued base laws (prepared contract request branch) request)
  _ _ one.1 two.1 (FreshSigningConsumer.currentScope (prepared contract request branch) request) threshold one.2 two.2 left right

theorem accepted_growth_contains_a_new_actual_valid_production_occurrence
 (before : JointReceptionSource.State root) (branch : SourceRepairSearch.Branch root)
 (checked : accepts contract base laws request good quota threshold before branch=true) :
 ∃ row∈(endpoint contract base laws request branch).rows.drop before.rows.length,
 ∃ item∈StageTrace.items row.actual, ∃ operator,
 item.request.operation=.produce operator ∧ row.code.law.Valid item.before item.request := by
 have production := (acceptance_checks_the_actual_full_cycle contract base laws request good quota threshold before branch checked).2.2.1
 obtain ⟨row,inside,produced⟩ := List.any_eq_true.mp production
 unfold productiveRow at produced
 obtain ⟨item,member,valid⟩ := List.any_eq_true.mp produced
 cases operation : item.request.operation <;> simp only [operation] at valid <;> try contradiction
 rename_i operator
 exact ⟨row,inside,item,member,operator,operation,of_decide_eq_true valid⟩

theorem accepted_claims_are_the_entire_original_financial_matrix
 (before : JointReceptionSource.State root) (branch : SourceRepairSearch.Branch root)
 (checked : accepts contract base laws request good quota threshold before branch=true) :
 (current (endpoint contract base laws request branch)).claims=(current before).claims := by
 have retained := (acceptance_checks_the_actual_full_cycle contract base laws request good quota threshold before branch checked).2.1
 funext instrument debtor creditor
 exact retained instrument debtor creditor

omit [Fintype Party] [Fintype Instrument] in
theorem a_selected_cycle_keeps_all_original_history_and_its_own_next
 (before : JointReceptionSource.State root) (depth : Nat) (branch : SourceRepairSearch.Branch root)
 (generated : branch∈SourceRepairSearch.cases contract depth before) :
 before.actual.archive <+: (endpoint contract base laws request branch).actual.archive ∧
 before.actual.windows <+: (endpoint contract base laws request branch).actual.windows ∧
 before.rows <+: (endpoint contract base laws request branch).rows ∧
 ArchivedDeliveryConsumer.NativeContinuation (endpoint contract base laws request branch).actual.model
  (endpoint contract base laws request branch).actual.point := by
 have replay := (SourceRepairSearch.every_generated_branch_replays_the_exact_original_commands contract depth before branch generated).1
 have history :=  SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows contract before branch.commands
 rw [replay] at history
 have after := FreshSigningSource.every_paid_cycle_retains_all_original_archives_windows_and_rows contract base laws branch.final request
 exact ⟨history.1.trans after.1,history.2.1.trans after.2.1,history.2.2.trans after.2.2,
  JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩

theorem actual_cycle_increment_is_paid_by_its_net_material_gain
 (before : JointReceptionSource.State root) (depth : Nat) :
 total before good+(increment contract base laws request good quota threshold before depth : ℚ)*quota≤
 total (ProductiveSigningSource.next contract base laws request good quota threshold before depth) good := by
 unfold ProductiveSigningSource.next increment
 cases selected : ProductiveSigningSource.produce contract base laws request good quota threshold before depth with
 | invalidDemand bad => simp only [Nat.cast_zero,zero_mul,add_zero,le_refl]
 | blocked positive exhausted => simp only [Nat.cast_zero,zero_mul,add_zero,le_refl]
 | produced branch positive generated checked =>
   simpa only [Nat.cast_one,one_mul] using
    (acceptance_checks_the_actual_full_cycle contract base laws request good quota threshold before branch checked).1

theorem repeated_actual_cycles_generate_cumulative_net_new_material
 (before : JointReceptionSource.State root) (depth count : Nat) :
 total before good+(producedCount contract base laws request good quota threshold before depth count : ℚ)*quota≤
 total (ProductiveSigningSource.run contract base laws request good quota threshold before depth count) good := by
 induction count with
 | zero =>
   change total before good+(0:ℚ)*quota≤total before good
   simp only [zero_mul,add_zero,le_refl]
 | succ count ih =>
   have actual := actual_cycle_increment_is_paid_by_its_net_material_gain contract base laws request good quota threshold
    (ProductiveSigningSource.run contract base laws request good quota threshold before depth count) depth
   change total before good+((producedCount contract base laws request good quota threshold before depth count+
    increment contract base laws request good quota threshold
     (ProductiveSigningSource.run contract base laws request good quota threshold before depth count) depth : Nat):ℚ)*quota≤
    total (ProductiveSigningSource.next contract base laws request good quota threshold
     (ProductiveSigningSource.run contract base laws request good quota threshold before depth count) depth) good
   rw [Nat.cast_add,add_mul]
   linarith

theorem repeated_actual_cycles_keep_every_original_financial_position
 (before : JointReceptionSource.State root) (depth count : Nat) :
 (current (ProductiveSigningSource.run contract base laws request good quota threshold before depth count)).claims=(current before).claims := by
 induction count with
 | zero => rfl
 | succ count ih =>
   change (current (ProductiveSigningSource.next contract base laws request good quota threshold
    (ProductiveSigningSource.run contract base laws request good quota threshold before depth count) depth)).claims=_
   unfold ProductiveSigningSource.next
   cases selected : ProductiveSigningSource.produce contract base laws request good quota threshold
    (ProductiveSigningSource.run contract base laws request good quota threshold before depth count) depth with
   | invalidDemand bad => exact ih
   | blocked positive exhausted => exact ih
   | produced branch positive generated checked =>
     exact (accepted_claims_are_the_entire_original_financial_matrix contract base laws request good quota threshold _ branch checked).trans ih

omit [Fintype Instrument] in
theorem a_pure_redistribution_cannot_pass_the_net_creation_gate
 (before after : JointReceptionSource.State root) (positive : 0<quota)
 (balanced : total after good=total before good) : ¬total before good+quota≤total after good := by
 rw [balanced]
 linarith

theorem unchanged_claims_do_not_supply_a_production_occurrence
 (before : JointReceptionSource.State root) (branch : SourceRepairSearch.Branch root)
 (absent : freshProduction before (endpoint contract base laws request branch)=false) :
 accepts contract base laws request good quota threshold before branch=false := by
 unfold accepts
 rw [absent]
 simp only [Bool.and_false,Bool.false_and]

theorem each_computed_step_keeps_all_original_history
 (before : JointReceptionSource.State root) (depth : Nat) :
 before.actual.archive <+: (ProductiveSigningSource.next contract base laws request good quota threshold before depth).actual.archive ∧
 before.actual.windows <+: (ProductiveSigningSource.next contract base laws request good quota threshold before depth).actual.windows ∧
 before.rows <+: (ProductiveSigningSource.next contract base laws request good quota threshold before depth).rows := by
 unfold ProductiveSigningSource.next
 cases selected : ProductiveSigningSource.produce contract base laws request good quota threshold before depth with
 | invalidDemand bad => exact ⟨List.prefix_refl _,List.prefix_refl _,List.prefix_refl _⟩
 | blocked positive exhausted => exact ⟨List.prefix_refl _,List.prefix_refl _,List.prefix_refl _⟩
 | produced branch positive generated checked =>
   have kept := a_selected_cycle_keeps_all_original_history_and_its_own_next contract base laws request before depth branch generated
   exact ⟨kept.1,kept.2.1,kept.2.2.1⟩

theorem repeated_actual_cycles_keep_all_original_history_and_own_next
 (before : JointReceptionSource.State root) (depth count : Nat) :
 before.actual.archive <+: (ProductiveSigningSource.run contract base laws request good quota threshold before depth count).actual.archive ∧
 before.actual.windows <+: (ProductiveSigningSource.run contract base laws request good quota threshold before depth count).actual.windows ∧
 before.rows <+: (ProductiveSigningSource.run contract base laws request good quota threshold before depth count).rows ∧
 ArchivedDeliveryConsumer.NativeContinuation
  (ProductiveSigningSource.run contract base laws request good quota threshold before depth count).actual.model
  (ProductiveSigningSource.run contract base laws request good quota threshold before depth count).actual.point := by
 induction count with
 | zero => exact ⟨List.prefix_refl _,List.prefix_refl _,List.prefix_refl _,JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩
 | succ count ih =>
   have next := each_computed_step_keeps_all_original_history contract base laws request good quota threshold
    (ProductiveSigningSource.run contract base laws request good quota threshold before depth count) depth
   exact ⟨ih.1.trans next.1,ih.2.1.trans next.2.1,ih.2.2.1.trans next.2.2,
    JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] [Fintype Instrument] in
theorem balanced_transfers_preserve_the_all_party_total
 (stock : Party → ℚ) (sender recipient : Party) (amount : ℚ) :
 (∑ party : Party, (stock party+(if party=recipient then amount else 0)-(if party=sender then amount else 0)))=
 ∑ party : Party, stock party := by
 simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
 have received : (∑ party : Party, if party=recipient then amount else 0)=amount := by simp
 have sent : (∑ party : Party, if party=sender then amount else 0)=amount := by simp
 rw [received,sent]
 ring

theorem a_cycle_without_actual_received_quorum_cannot_pass
 (before : JointReceptionSource.State root) (branch : SourceRepairSearch.Branch root)
 (absent : decisions contract base laws request threshold branch=[]) :
 accepts contract base laws request good quota threshold before branch=false := by
 unfold accepts
 rw [absent]
 simp only [List.isEmpty_nil,Bool.not_true,Bool.and_false]

theorem a_cycle_that_only_redistributes_or_consumes_cannot_pass
 (before : JointReceptionSource.State root) (branch : SourceRepairSearch.Branch root)
 (positive : 0<quota)
 (noCreation : total (endpoint contract base laws request branch) good≤total before good) :
 accepts contract base laws request good quota threshold before branch=false := by
 apply Bool.eq_false_iff.mpr
 intro accepted
 have net := (acceptance_checks_the_actual_full_cycle contract base laws request good quota threshold before branch accepted).1
 linarith

theorem changing_an_original_financial_claim_cannot_pay_for_net_creation
 (before : JointReceptionSource.State root) (branch : SourceRepairSearch.Branch root)
 (changed : (current (endpoint contract base laws request branch)).claims≠(current before).claims) :
 accepts contract base laws request good quota threshold before branch=false := by
 apply Bool.eq_false_iff.mpr
 intro accepted
 exact changed (accepted_claims_are_the_entire_original_financial_matrix contract base laws request good quota threshold before branch accepted)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveSigningConsumer
