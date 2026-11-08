import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ActualRoundNetworkSource
variable (net : Network)

theorem generated_domain_is_nonempty (count : Nat) : ∃ node, node ∈ generate net count := by
  have nonempty (node : Node net) : choices net node ≠ [] := by
    unfold choices
    split
    · simp
    · split
      · simp
      · split <;> simp
  induction count with
  | zero => exact ⟨initial net,List.mem_singleton_self _⟩
  | succ count ih =>
    obtain ⟨node,member⟩ := ih
    obtain ⟨move,allowed⟩ := List.exists_mem_of_ne_nil (choices net node) (nonempty node)
    exact ⟨step net node (EventStep.fixed move),
      List.mem_flatMap.mpr ⟨node,member,List.mem_map.mpr ⟨move,allowed,rfl⟩⟩⟩

abbrev Related (left right : (Node net)) := EnvelopeObservation.Compatible (start net) left.stages right.stages

theorem related_states (left right : (Node net)) (one : (Valid net) left) (two : (Valid net) right) (same : (Related net) left right) :
    left.state = right.state := by
  have states : EventStep.seed left.cursor = EventStep.seed right.cursor := by
    rw [one.1,two.1]
    exact same.1.state
  exact one.2.1.trans (states.trans two.2.1.symm)

theorem related_choices (left right : (Node net)) (one : (Valid net) left) (two : (Valid net) right) (same : (Related net) left right) :
    (choices net) left = (choices net) right := by
  rw [(choices_are_the_original_source_envelope net) left one,(choices_are_the_original_source_envelope net) right two]
  exact EnvelopeObservation.choices_equal (start net) _ _ same (allowance net)

def chosen (left right : (Node net)) (rival : Opponent (code net)) : Move (code net) :=
  CausalLocalDomain.chosen (EventHistory.execute (start net) left.stages) (EventHistory.execute (start net) right.stages) rival

theorem chosen_is_actual (left right : (Node net)) (two : (Valid net) right) (same : (Related net) left right) (rival : Opponent (code net)) :
    (chosen net) left right rival = (intake net) right rival := by
  unfold chosen intake
  rw [EnvelopeObservation.chosen_is_the_actual_intake (start net) _ _ same,← two.1]

theorem compact_step (left right : (Node net)) (same : (Related net) left right) (rival : Opponent (code net)) :
    (Related net) ((step net) left (EventStep.fixed ((chosen net) left right rival))) ((step net) right rival) :=
  EnvelopeObservation.compact_extension (start net) _ _ same (protocol net) rival

-- The callback may change its behaviour after observing its entire actual history.
theorem every_compliant_actual_callback_has_a_generated_branch
    (rivals : Nat → Opponent (code net)) (count : Nat) (within : (Within net) rivals count) :
    ∃ node ∈ (generate net) count, (Related net) node ((actual net) rivals count) := by
  induction count with
  | zero => exact ⟨(initial net),List.mem_singleton_self _,EventStep.matches_self _,EnvelopeObservation.reflexive _⟩
  | succ count ih =>
    obtain ⟨node,member,same⟩ := ih (fun index bounded => within index (by omega))
    have one := (generated_valid net) count node member
    have two := (actual_valid net) rivals count
    let rival := rivals ((actual net) rivals count).cursor.cut
    let move := (chosen net) node ((actual net) rivals count) rival
    have allowed : move ∈ (choices net) node := by
      dsimp only [move]
      rw [(related_choices net) node _ one two same,(chosen_is_actual net) node _ two same]
      exact within count (by omega)
    exact ⟨(step net) node (EventStep.fixed move),
      List.mem_flatMap.mpr ⟨node,member,List.mem_map.mpr ⟨move,allowed,rfl⟩⟩,
      (compact_step net) node _ same rival⟩

theorem related_subjects (left right : (Node net)) (same : (Related net) left right) :
    StagePaymentQuorum.resolve (vocabulary net) (start net) left.stages (scope net) =
      StagePaymentQuorum.resolve (vocabulary net) (start net) right.stages (scope net) :=
  StagePaymentQuorum.resolve_equal (vocabulary net) (EnvelopeObservation.communication same.2) (scope net)

theorem related_results (left right : (Node net)) (same : (Related net) left right) : (result net) left = (result net) right := by
  have counts := QuorumObservation.count_equal (start net) _ _ same.2
  have receivers := CommunicationObservation.run_equal (vocabulary net) (encoding net) (start net) (start net) _ _
    (EnvelopeObservation.communication same.2) (reception net) 0 right.stages.length
  unfold result StagePaymentQuorum.produce
  rw [(related_subjects net) left right same]
  split <;> try rfl
  split <;> try rfl
  unfold StagePaymentQuorum.received
  rw [counts,receivers]


abbrev finished (net : Network) (rivals : Nat → Opponent (code net)) := actual net rivals (window net)

theorem every_compliant_callback_completes
    (subject : Subject net) (all : ∀ node ∈ generate net (window net), result net node = .decided true subject)
    (rivals : Nat → Opponent (code net)) (within : Within net rivals (window net)) :
    result net (finished net rivals) = .decided true subject := by
  obtain ⟨node,member,same⟩ := every_compliant_actual_callback_has_a_generated_branch net rivals (window net) within
  have done := all node member
  rw [related_results net node _ same] at done
  exact done

abbrev facade (rivals : Nat → Opponent (code net)) :=
  Feedback.Runtime.facade ((finished net) rivals).cursor.source ((finished net) rivals).cursor.entry rfl rfl

def PaymentConsumed (subject : Subject net) (rivals : Nat → Opponent (code net)) : Prop :=
    let final := ((finished net) rivals).cursor
    let runtime := ((facade net) rivals).seed.advance (EventStep.boundary final)
    (∃ row ∈ ((finished net) rivals).rows, ∃ item,
      item ∈ (Financial.inventoryAt final.source.input
        (ProgrammeHistory.visitAt final.source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? final.source.input) ∧
      (code net).law.Valid item.before item.request ∧ 0 < subject.2.amount ∧
      flowAt ((code net).law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
      flowAt ((code net).law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
      ((code net).law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor =
        subject.2.priorClaim-subject.2.quantity) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = ((facade net) rivals).process.stateAt (((facade net) rivals).process.successor runtime.state)

private theorem consume_actual_payment
    (subject : Subject net) (all : ∀ node ∈ generate net (window net), result net node = .decided true subject)
    (rivals : Nat → Opponent (code net)) (within : Within net rivals (window net)) :
    PaymentConsumed net subject rivals := by
  have valid := (actual_valid net) rivals (window net)
  have done := every_compliant_callback_completes net subject all rivals within
  obtain ⟨row,inside,item,member,paid⟩ := StagePaymentQuorum.every_decision_consumes_actual_payment_effects
    (vocabulary net) (start net) (encoding net) (reception net) ((finished net) rivals).stages 0 (scope net) net.settings.threshold true subject done
  have final := ((finished net) rivals).cursor
  have native := StageTrace.final_financial_inventory_is_the_original_record_items (start net) ((finished net) rivals).stages row inside
  rw [← valid.1] at native
  have rooted := ((facade net) rivals).readoutAt_factorizes
    (((facade net) rivals).seed.advance (EventStep.boundary ((finished net) rivals).cursor)) .feedback
  refine ⟨⟨row,by rwa [valid.2.2],item,?_,paid⟩,rooted.2.2.1,rooted.2.2.2.2⟩
  rw [native]
  exact member


def completion : Option (Subject net) :=
  match assess net with
  | .completed subject _ _ => some subject
  | _ => none

private theorem completion_has_generated_checks (subject : Subject net)
    (made : completion net = some subject) :
    ∀ node ∈ generate net (window net), result net node = .decided true subject := by
  unfold completion at made
  cases verdict : assess net with
  | unresolved missing => simp only [verdict] at made;contradiction
  | completed original origin all =>
    simp only [verdict] at made
    cases Option.some.inj made
    exact all
  | obstructed original origin node member failed => simp only [verdict] at made;contradiction

theorem generated_completion_covers_arbitrary_compliant_history_callbacks
    (subject : Subject net) (made : completion net = some subject)
    (rivals : Nat → Opponent (code net)) (within : Within net rivals (window net)) :
    result net (finished net rivals) = .decided true subject :=
  every_compliant_callback_completes net subject (completion_has_generated_checks net subject made) rivals within

theorem generated_completion_consumes_actual_payment_whole_ledger_and_next
    (subject : Subject net) (made : completion net = some subject)
    (rivals : Nat → Opponent (code net)) (within : Within net rivals (window net)) :
    PaymentConsumed net subject rivals :=
  consume_actual_payment net subject (completion_has_generated_checks net subject made) rivals within

abbrev obstruction : Option (Node net) :=
  match assess net with
  | .obstructed _ _ node _ _ => some node
  | _ => none

theorem generated_obstruction_is_an_executable_original_source_branch
    (node : Node net) (made : obstruction net = some node) :
    Valid net node ∧ ∃ subject, expected net = some subject ∧ result net node ≠ .decided true subject := by
  unfold obstruction at made
  cases verdict : assess net with
  | unresolved missing => simp only [verdict] at made;contradiction
  | completed subject origin all => simp only [verdict] at made;contradiction
  | obstructed subject origin bad member failed =>
    simp only [verdict] at made
    cases Option.some.inj made
    exact ⟨generated_valid net (window net) node member,subject,origin,failed⟩

abbrev branchFacade (node : Node net) := Feedback.Runtime.facade node.cursor.source node.cursor.entry rfl rfl

theorem failed_branch_still_consumes_its_actual_whole_ledger_and_next
    (node : Node net) (made : obstruction net = some node) :
    let runtime := (branchFacade net node).seed.advance (EventStep.boundary node.cursor)
    Valid net node ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (branchFacade net node).process.stateAt ((branchFacade net node).process.successor runtime.state) := by
  have rooted := (branchFacade net node).readoutAt_factorizes
    ((branchFacade net node).seed.advance (EventStep.boundary node.cursor)) .feedback
  exact ⟨(generated_obstruction_is_an_executable_original_source_branch net node made).1,rooted.2.2.1,rooted.2.2.2.2⟩

theorem the_network_installs_only_its_actual_input_at_the_admitted_round :
    (start net).source = {net.entry.bound.source with feedback? := some (input net), feedbackOverrides := []} ∧
      (start net).source.history = net.entry.bound.source.history ∧
      EventStep.seed (start net) = (emitter net).feedbackState (input net) 0 := ⟨rfl,rfl,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkConsumer
