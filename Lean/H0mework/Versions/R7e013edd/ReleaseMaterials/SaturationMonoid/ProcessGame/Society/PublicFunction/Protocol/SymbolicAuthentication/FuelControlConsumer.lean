import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlEvidence

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 160000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open FuelControlSource FuelControlDomain

abbrev Subject := StagePaymentQuorum.Subject (code := code)
def sameOriginalPayment (payment : Payment) : Prop :=
  match Settlement.issuedAt code.law initial.state.current [MaterialRoundSource.payment] 0 with
  | none => False
  | some original => payment = {original with epoch := payment.epoch}
instance (payment : Payment) : Decidable (sameOriginalPayment payment) := by
  unfold sameOriginalPayment
  split <;> infer_instance

def Complete (node : Node) : Prop := ∃ subject : Subject,
  originSubject node = some subject ∧ result node = .decided true subject ∧ sameOriginalPayment subject.2 ∧
    (subject.1.cut = 0 ∨ subject.1.cut = 2) ∧ subject.1.scope = subject.2.scope ∧
    (node.rows.all fun row => (StageTrace.audit row).all Prod.snd) = true ∧
    node.state.current.claims () 1 2 = 6 ∧ node.state.current.stock 1 .service = 0

def completeCheck (node : Node) : Bool := match originSubject node with
  | none => false
  | some subject => decide (result node = .decided true subject ∧ sameOriginalPayment subject.2 ∧
      (subject.1.cut = 0 ∨ subject.1.cut = 2) ∧ subject.1.scope = subject.2.scope ∧
      (node.rows.all fun row => (StageTrace.audit row).all Prod.snd) = true ∧
      node.state.current.claims () 1 2 = 6 ∧ node.state.current.stock 1 .service = 0)


theorem checked_is_complete (node : Node) (passed : completeCheck node = true) : Complete node := by
  unfold completeCheck at passed
  split at passed <;> try contradiction
  rename_i subject made
  exact ⟨subject,made,of_decide_eq_true passed⟩

theorem original_subject_retains_its_exact_first_payment_row (node : Node) (subject : Subject)
    (made : originSubject node = some subject) :
    ∃ row ∈ node.rows, originRow node = some row ∧ paymentAt row = some subject.2 ∧
      StageBudget.issued (vocabulary subject.2.scope) row 0 = some subject.1 := by
  unfold originSubject at made
  cases first : originRow node with
  | none => simp [first] at made
  | some row =>
    simp only [first,Option.bind_some] at made
    cases paid : paymentAt row with
    | none => simp [paid] at made
    | some payment =>
      simp only [paid,Option.bind_some] at made
      obtain ⟨item,_,position,_⟩ := Settlement.issued_has_actual_paid_origin code.law row.before.current row.submitted 0 payment paid
      have original := StagePaymentQuorum.at_has_both_original_origins (vocabulary payment.scope) row payment.scope subject made
      have sameAt : paymentAt row = some subject.2 := by simpa only [paymentAt,Settlement.StatementData.scope,position] using original.2.1
      have equal : payment = subject.2 := Option.some.inj (paid.symm.trans sameAt)
      have signature : StageBudget.issued (vocabulary subject.2.scope) row 0 = some subject.1 := by
        rw [← equal]
        simpa only [Settlement.StatementData.scope,position] using original.1
      exact ⟨row,List.mem_of_find?_eq_some first,rfl,sameAt,signature⟩

theorem related_checks (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    completeCheck left = completeCheck right := by
  have states := related_states left right one two same
  have audits : (left.rows.all fun row => (StageTrace.audit row).all Prod.snd) =
      (right.rows.all fun row => (StageTrace.audit row).all Prod.snd) := by
    have rows := related_rows left right one two same
    generalize left.rows = a at rows ⊢
    generalize right.rows = b at rows ⊢
    induction rows with
    | nil => rfl
    | @cons a b _ _ head tail ih =>
      have audit : StageTrace.audit a = StageTrace.audit b := by simp only [StageTrace.audit,StageTrace.items,head.before,head.submitted]
      simp only [List.all_cons,audit,ih]
  unfold completeCheck
  rw [related_original_subjects left right one two same,
    related_results left right one two same,audits,states]


def Blocked (node : Node) : Prop := result node = .blocked .missingSourceSubject ∨ result node = .blocked .missingQuorum
instance (node : Node) : Decidable (Blocked node) := inferInstanceAs (Decidable (_ ∨ _))
def Disposed (node : Node) : Prop := Complete node ∨ Blocked node
def check (node : Node) : Bool := (completeCheck node || decide (Blocked node)) &&
  (!released node || completeCheck node)
def checkAll : Nat → Node → Bool :=
  Nat.rec check fun _ recur node => (controls node).all fun requested =>
    (choices node).all fun move => recur (step node requested (EventStep.fixed move))

theorem the_entire_open_control_domain_generates_disposition_and_opportunity_completion :
    checkAll window initial = true := by decide +kernel

theorem generated_prefix_keeps_its_remaining_check
    (count remaining : Nat) (node : Node) (member : node ∈ generate count)
    (passed : checkAll (count+remaining) initial = true) : checkAll remaining node = true := by
  induction count generalizing remaining node with
  | zero => cases List.mem_singleton.mp member;simpa only [Nat.zero_add] using passed
  | succ count ih =>
    obtain ⟨before,inside,next⟩ := List.mem_flatMap.mp member
    obtain ⟨requested,selected,rest⟩ := List.mem_flatMap.mp next
    obtain ⟨move,allowed,rfl⟩ := List.mem_map.mp rest
    have previous := ih (remaining+1) before inside (by simpa only [Nat.add_assoc,Nat.add_comm 1] using passed)
    exact List.all_eq_true.mp (List.all_eq_true.mp previous requested selected) move allowed


theorem checked_is_disposed (node : Node) (passed : check node = true) :
    Disposed node ∧ (released node = true → Complete node) := by
  have both := Bool.and_eq_true_iff.mp passed
  constructor
  · rcases Bool.or_eq_true_iff.mp both.1 with done | blocked
    · exact Or.inl (checked_is_complete node done)
    · exact Or.inr (of_decide_eq_true blocked)
  · intro free
    have ready := both.2
    rw [free,Bool.not_true,Bool.false_or] at ready
    exact checked_is_complete node ready

abbrev finished (control : Controller) (rivals : Nat → Opponent code) := actual control rivals window

theorem every_actual_controller_generates_disposition_and_opportunity_completion
    (control : Controller) (rivals : Nat → Opponent code) (within : Within control rivals window) :
    Disposed (finished control rivals) ∧ (released (finished control rivals) = true → Complete (finished control rivals)) := by
  obtain ⟨node,member,same⟩ := every_actual_joint_controller_has_a_generated_source_branch control rivals window within
  have one := generated_valid window node member
  have two := actual_valid control rivals window
  have passed : check node = true := generated_prefix_keeps_its_remaining_check window 0 node member
    (by simpa only [Nat.add_zero] using the_entire_open_control_domain_generates_disposition_and_opportunity_completion)
  have moved : check node = check (finished control rivals) := by
    unfold check Blocked
    have outcomes : result node = result (finished control rivals) := related_results node _ one two same
    simp only [related_checks node _ one two same,outcomes,released,same.2]
    rfl
  rw [moved] at passed
  exact checked_is_disposed _ passed

theorem every_actual_released_opportunity_completes_the_paid_subject
    (control : Controller) (rivals : Nat → Opponent code) (within : Within control rivals window)
    (free : released (finished control rivals) = true) : Complete (finished control rivals) :=
  (every_actual_controller_generates_disposition_and_opportunity_completion control rivals within).2 free

abbrev facade (control : Controller) (rivals : Nat → Opponent code) :=
  Feedback.Runtime.facade (finished control rivals).cursor.source (finished control rivals).cursor.entry rfl rfl

theorem joint_completion_consumes_the_first_actual_payment_inventory_whole_ledger_and_next
    (control : Controller) (rivals : Nat → Opponent code) (within : Within control rivals window)
    (free : released (finished control rivals) = true) :
    let node := finished control rivals
    let final := node.cursor
    let runtime := (facade control rivals).seed.advance (EventStep.boundary final)
    (∃ subject : Subject, result node = .decided true subject ∧ ∃ row ∈ node.rows,
      originRow node = some row ∧ ∃ item,
      item ∈ (Financial.inventoryAt final.source.input
        (ProgrammeHistory.visitAt final.source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? final.source.input) ∧
      code.law.Valid item.before item.request ∧ 0 < subject.2.amount ∧
      flowAt (code.law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
      flowAt (code.law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
      (code.law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor =
        subject.2.priorClaim-subject.2.quantity) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade control rivals).process.stateAt ((facade control rivals).process.successor runtime.state) := by
  obtain ⟨subject,origin,done,_⟩ := every_actual_released_opportunity_completes_the_paid_subject control rivals within free
  obtain ⟨row,inside,first,paid,_⟩ := original_subject_retains_its_exact_first_payment_row _ subject origin
  obtain ⟨item,located,valid,positive,_,debit,credit,claims⟩ := Settlement.issued_payment_has_actual_material_and_claim_effects
    code.law row.before.current row.submitted 0 subject.2 paid
  have history := actual_valid control rivals window
  have native := StageTrace.final_financial_inventory_is_the_original_record_items start (finished control rivals).stages row
    (by rwa [← history.2.2])
  rw [← history.1] at native
  have rooted := (facade control rivals).readoutAt_factorizes
    ((facade control rivals).seed.advance (EventStep.boundary (finished control rivals).cursor)) .feedback
  refine ⟨⟨subject,done,row,inside,first,item,?_,valid,positive,debit,credit,claims⟩,rooted.2.2.1,rooted.2.2.2.2⟩
  rw [native]
  exact List.mem_of_getElem? located

theorem every_actual_attempt_retains_the_native_inventory_whole_ledger_and_next
    (control : Controller) (rivals : Nat → Opponent code) :
    let node := finished control rivals
    let runtime := (facade control rivals).seed.advance (EventStep.boundary node.cursor)
    (∀ row ∈ node.rows,
      (Financial.inventoryAt node.cursor.source.input
        (ProgrammeHistory.visitAt node.cursor.source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? node.cursor.source.input) = StageTrace.items row) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade control rivals).process.stateAt ((facade control rivals).process.successor runtime.state) := by
  have valid := actual_valid control rivals window
  have rooted := (facade control rivals).readoutAt_factorizes
    ((facade control rivals).seed.advance (EventStep.boundary (finished control rivals).cursor)) .feedback
  refine ⟨?_,rooted.2.2.1,rooted.2.2.2.2⟩
  intro row inside
  rw [valid.2.2] at inside
  rw [valid.1]
  exact StageTrace.final_financial_inventory_is_the_original_record_items start _ row inside


end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlConsumer
