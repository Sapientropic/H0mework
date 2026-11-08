import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkDomain

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 160000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open FinancedNetworkSource FinancedNetworkDomain

abbrev finished (rivals : Nat → Opponent code) := actual rivals window

theorem every_compliant_full_history_network_completes_the_same_entire_subject
    (rivals : Nat → Opponent code) (within : Within rivals window) :
    result (finished rivals) = .decided true expected ∧
      ((finished rivals).rows.all fun row => (StageTrace.audit row).all Prod.snd) = true ∧
      (finished rivals).state.current.claims () 1 2 = 9 ∧ (finished rivals).state.current.stock 1 .service = 0 := by
  obtain ⟨node,member,same⟩ := every_compliant_actual_callback_has_a_generated_branch rivals window within
  have success := generated_success node member
  have one := generated_valid window node member
  have two := actual_valid rivals window
  have states := related_states node _ one two same
  have audits : (node.rows.all fun row => (StageTrace.audit row).all Prod.snd) =
      ((finished rivals).rows.all fun row => (StageTrace.audit row).all Prod.snd) := by
    have rows := EnvelopeObservation.communication same.2
    rw [← one.2.2,← two.2.2] at rows
    generalize node.rows = a at rows ⊢
    generalize (finished rivals).rows = b at rows ⊢
    induction rows with
    | nil => rfl
    | @cons a b _ _ head tail ih =>
      have audit : StageTrace.audit a = StageTrace.audit b := by simp only [StageTrace.audit,StageTrace.items,head.before,head.submitted]
      simp only [List.all_cons,audit,ih]
  rw [related_results node _ same,audits,states] at success
  exact success

abbrev facade (rivals : Nat → Opponent code) :=
  Feedback.Runtime.facade (finished rivals).cursor.source (finished rivals).cursor.entry rfl rfl

theorem the_entire_subject_is_consumed_by_its_actual_financial_inventory_ledger_and_next
    (rivals : Nat → Opponent code) (within : Within rivals window) :
    let final := (finished rivals).cursor
    let runtime := (facade rivals).seed.advance (EventStep.boundary final)
    (∃ row ∈ (finished rivals).rows, ∃ item,
      item ∈ (Financial.inventoryAt final.source.input
        (ProgrammeHistory.visitAt final.source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? final.source.input) ∧
      code.law.Valid item.before item.request ∧ 0 < expected.2.amount ∧
      flowAt (code.law.actualDebit item.before item.request) expected.2.debtor expected.2.unit = expected.2.amount ∧
      flowAt (code.law.actualCredit item.before item.request) expected.2.creditor expected.2.unit = expected.2.amount ∧
      (code.law.step item.before item.request).claims expected.2.instrument expected.2.debtor expected.2.creditor =
        expected.2.priorClaim-expected.2.quantity) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade rivals).process.stateAt ((facade rivals).process.successor runtime.state) := by
  have valid := actual_valid rivals window
  have done := (every_compliant_full_history_network_completes_the_same_entire_subject rivals within).1
  obtain ⟨row,inside,item,member,paid⟩ := StagePaymentQuorum.every_decision_consumes_actual_payment_effects
    vocabulary start encoding reception (finished rivals).stages 0 scope 1 true expected done
  have final := (finished rivals).cursor
  have native := StageTrace.final_financial_inventory_is_the_original_record_items start (finished rivals).stages row inside
  rw [← valid.1] at native
  have rooted := (facade rivals).readoutAt_factorizes
    ((facade rivals).seed.advance (EventStep.boundary (finished rivals).cursor)) .feedback
  refine ⟨⟨row,by rwa [valid.2.2],item,?_,paid⟩,rooted.2.2.1,rooted.2.2.2.2⟩
  rw [native]
  exact member

abbrev latest : Nat → Opponent code := fun _ => QueueScheduler.opponent code (OriginQueue.baseline start)
abbrev delayed : Nat → Opponent code := fun cut => if cut = 3 then EventStep.fixed none else latest cut
abbrev rawDeviation : Nat → Opponent code := fun cut history past frame =>
  if frame.sent.isEmpty then some ⟨.activate 0,by decide⟩ else delayed cut history past frame
abbrev silent : Nat → Opponent code := fun _ => EventStep.fixed none

def conforms (rivals : Nat → Opponent code) : Bool :=
  (List.range window).all fun index => decide
    (intake (actual rivals index) (rivals (actual rivals index).cursor.cut) ∈ choices (actual rivals index))
theorem conforms_iff (rivals : Nat → Opponent code) : conforms rivals = true ↔ Within rivals window := by
  simp only [conforms,Within,List.all_eq_true,List.mem_range,decide_eq_true_eq]

theorem real_delay_and_rejected_raw_impersonation_coexist_with_the_paid_decision :
    Within delayed window ∧ Within rawDeviation window ∧
      result (finished delayed) = .decided true expected ∧ result (finished rawDeviation) = .decided true expected ∧
      (material (actual rawDeviation 1) (rawDeviation 1)).call = .external (some ⟨.activate 0,by decide⟩) ∧
      StageTransport.admission (material (actual rawDeviation 1) (rawDeviation 1)) = none := by
  have one : Within delayed window := (conforms_iff delayed).mp (by decide +kernel)
  have two : Within rawDeviation window := (conforms_iff rawDeviation).mp (by decide +kernel)
  exact ⟨one,two,(every_compliant_full_history_network_completes_the_same_entire_subject delayed one).1,
    (every_compliant_full_history_network_completes_the_same_entire_subject rawDeviation two).1,by decide +kernel⟩

theorem absent_delivery_or_the_original_timing_stays_blocked :
    ¬ Within silent window ∧ result (finished silent) = .blocked .missingQuorum ∧
      StagePaymentQuorum.produce vocabulary start encoding
        ⟨fun _ _ => scope,1⟩
        (finished delayed).stages 0 scope 1 = .blocked .missingQuorum := by
  refine ⟨?_,by decide +kernel⟩
  intro within
  have accepts := (conforms_iff silent).mpr within
  have refused : conforms silent = false := by decide +kernel
  rw [refused] at accepts
  contradiction

theorem deleting_the_original_payment_row_does_not_recover_a_subject :
    StagePaymentQuorum.resolveRows vocabulary (finished latest).rows.tail scope = none := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkConsumer
