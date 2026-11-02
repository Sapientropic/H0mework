import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.Transcript

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable {fuel : ℚ} {inputs : List (List Action)}

def branchInputs (cut : Cut fuel inputs) (word : List Action) :=
  OutstandingSource.History.executedWords (source fuel) inputs cut.depth ++ [word]

theorem branchInputs_length (cut : Cut fuel inputs) (word : List Action) :
    (branchInputs cut word).length = cut.depth + 1 := by
  simp [branchInputs, OutstandingSource.History.executedWords_length]

def afterInput (cut : Cut fuel inputs) (word : List Action) := start fuel (branchInputs cut word)

theorem afterInput_is_the_interpreted_original_cut (cut : Cut fuel inputs) (word : List Action) :
    (afterInput cut word).past = cut.past.append word := by
  change OutstandingSource.History.replay (source fuel) (branchInputs cut word) = _
  unfold branchInputs OutstandingSource.History.replay
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [show (OutstandingSource.History.executedWords (source fuel) inputs cut.depth).foldl
      OutstandingSource.ExecutionPrefix.append ((source fuel).canonicalPrefix 2) =
      trailAt fuel inputs (cut.depth + 2) from
    OutstandingSource.History.executed_words_replay_the_actual_cut (source fuel) inputs cut.depth]
  rw [← cut.actual]

theorem branch_preserves_the_common_actual_prefix (cut : Cut fuel inputs) (word : List Action)
    (visit : Nat) (inside : visit ≤ cut.depth + 2) :
    trailAt fuel (branchInputs cut word) visit = trailAt fuel inputs visit :=
  OutstandingSource.History.executed_words_preserve_their_actual_prefix _ _ _ _ visit inside

theorem branch_current_is_the_original_cut (cut : Cut fuel inputs) (word : List Action) :
    currentAt fuel (branchInputs cut word) (cut.depth + 2) = cut.past.frame.raw := by
  have own : currentAt fuel (branchInputs cut word) (cut.depth + 2) =
      (trailAt fuel (branchInputs cut word) (cut.depth + 2)).frame.raw :=
    (OutstandingSource.History.actual_frame (source fuel) (branchInputs cut word) _).1
  exact own.trans (congrArg (fun past => past.frame.raw)
    ((branch_preserves_the_common_actual_prefix cut word _ (Nat.le_refl _)).trans cut.actual.symm))

theorem new_input_is_actually_emitted (cut : Cut fuel inputs) (word : List Action) :
    (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).submitted = word := by
  have emitted := OutstandingSource.History.scheduled_input_is_actual (source fuel)
    (branchInputs cut word) cut.depth (by rw [branchInputs_length]; omega)
  have inside : cut.depth < (branchInputs cut word).length := by rw [branchInputs_length]; omega
  have last : (branchInputs cut word)[cut.depth]'inside = word := by
    simp [branchInputs, List.getElem_append_right,
      OutstandingSource.History.executedWords_length]
  exact emitted.trans last

theorem new_input_uses_the_original_cut (cut : Cut fuel inputs) (word : List Action) :
    (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).before = cut.past.frame.raw :=
  branch_current_is_the_original_cut cut word

theorem legal_future_word_is_accepted_at_its_own_actual_cut (cut : Cut fuel inputs) (word : List Action)
    (legal : ∀ item ∈ law.rawItems cut.past.frame.raw word, law.Valid item.before item.request) :
    ∀ item ∈ law.rawItems
      (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).before
      (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).submitted,
      law.Valid item.before item.request := by
  rw [new_input_is_actually_emitted, new_input_uses_the_original_cut]
  exact legal

theorem future_input_keeps_each_original_service_archive (cut : Cut fuel inputs) (word : List Action)
    (index : (source fuel).Slot) (paid : Nat) (recorded : cut.past.frame.payments index = some paid) :
    (afterInput cut word).past.frame.payments index = some paid := by
  rw [afterInput_is_the_interpreted_original_cut]
  exact cut.past.append_keeps_archive word index paid recorded

noncomputable section

def continueAfterInput (cut : Cut fuel inputs) (word : List Action) (rounds : Nat) :
    FiniteContinuation rounds (afterInput cut word) := generate _ rounds

theorem future_input_claims_are_the_actual_effect (cut : Cut fuel inputs) (word : List Action) :
    (afterInput cut word).past.frame.raw.claims = (law.next cut.past.frame.raw word).claims := by
  rw [afterInput_is_the_interpreted_original_cut]
  rfl

theorem original_current_and_word_at_each_birth (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1)) :
    Runtime.mandateCurrentAt fuel (branchInputs cut word) birth.val = Runtime.mandateCurrentAt fuel inputs birth.val ∧
    Runtime.mandateWordAt fuel (branchInputs cut word) birth.val = Runtime.mandateWordAt fuel inputs birth.val := by
  constructor
  · change currentAt fuel (branchInputs cut word) (birth.val + 1) = currentAt fuel inputs (birth.val + 1)
    exact ((OutstandingSource.History.actual_frame (source fuel) (branchInputs cut word) _).1.trans
      (congrArg (fun past => past.frame.raw)
        (branch_preserves_the_common_actual_prefix cut word _ (by omega)))).trans
      (OutstandingSource.History.actual_frame (source fuel) inputs _).1.symm
  · change (actualExecution fuel (branchInputs cut word) birth.val).submitted = (actualExecution fuel inputs birth.val).submitted
    have prefixes := branch_preserves_the_common_actual_prefix cut word (birth.val + 2) (by omega)
    change (OutstandingSource.ExecutionPrefix.append _ _) = (OutstandingSource.ExecutionPrefix.append _ _) at prefixes
    exact (OutstandingSource.History.actual_word _ _ _).trans
      ((OutstandingSource.ExecutionPrefix.extend.inj prefixes).2.trans
        (OutstandingSource.History.actual_word _ _ _).symm)

private def reindexGrant {first second : Current} {oldWord newWord : List Action}
    (sameCurrent : second = first) (sameWord : newWord = oldWord)
    (grant : Grant base scope first oldWord) : Grant base scope second newWord := by
  cases sameCurrent
  cases sameWord
  exact grant

private theorem reindexGrant_event {first second : Current} {oldWord newWord : List Action}
    (sameCurrent : second = first) (sameWord : newWord = oldWord)
    (grant : Grant base scope first oldWord) :
    (reindexGrant sameCurrent sameWord grant).electionEvent = grant.electionEvent := by
  cases sameCurrent
  cases sameWord
  rfl

private theorem reindexGrant_index {first second : Current} {oldWord newWord : List Action}
    (sameCurrent : second = first) (sameWord : newWord = oldWord)
    (grant : Grant base scope first oldWord) :
    (reindexGrant sameCurrent sameWord grant).acceptance.item.val.index = grant.acceptance.item.val.index := by
  cases sameCurrent
  cases sameWord
  rfl

private theorem reindexGrant_actual {first second : Current} {oldWord newWord : List Action}
    (sameCurrent : second = first) (sameWord : newWord = oldWord)
    (grant : Grant base scope first oldWord) (actual : grant ∈ grantsAt base scope first oldWord) :
    reindexGrant sameCurrent sameWord grant ∈ grantsAt base scope second newWord := by
  cases sameCurrent
  cases sameWord
  exact actual

def transportOriginalGrant (cut : Cut fuel inputs) (word : List Action) (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :
    Grant base scope (Runtime.mandateCurrentAt fuel (branchInputs cut word) birth.val)
      (Runtime.mandateWordAt fuel (branchInputs cut word) birth.val) :=
  reindexGrant (original_current_and_word_at_each_birth cut word birth).1
    (original_current_and_word_at_each_birth cut word birth).2 grant

theorem transported_grant_has_the_same_original_event (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :
    (transportOriginalGrant cut word birth grant).electionEvent = grant.electionEvent :=
  reindexGrant_event _ _ grant

theorem transported_grant_keeps_original_acceptance_index (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :
    (transportOriginalGrant cut word birth grant).acceptance.item.val.index = grant.acceptance.item.val.index :=
  reindexGrant_index _ _ grant

theorem transported_grant_is_actually_present (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val))
    (actual : grant ∈ grantsAt base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :
    transportOriginalGrant cut word birth grant ∈ grantsAt base scope
      (Runtime.mandateCurrentAt fuel (branchInputs cut word) birth.val)
      (Runtime.mandateWordAt fuel (branchInputs cut word) birth.val) :=
  reindexGrant_actual _ _ grant actual


theorem transported_grant_has_the_same_native_admission (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :
    (admitGrant base scope _ _ (transportOriginalGrant cut word birth grant)).native.target =
      (admitGrant base scope _ _ grant).native.target := by
  change (Election.mandateAdmissionEdge Grant.lineageCompiler
    (transportOriginalGrant cut word birth grant).electionEvent).target =
    (Election.mandateAdmissionEdge Grant.lineageCompiler grant.electionEvent).target
  rw [transported_grant_has_the_same_original_event]

theorem common_cut_has_the_same_native_service_status (cut : Cut fuel inputs) (word : List Action)
    (index : (source fuel).Slot) :
    ((OutstandingSource.History.NativeService.historyAt (source fuel) (branchInputs cut word)
      index (cut.depth + 1)).state.LiveAt 0 ↔
      (OutstandingSource.History.NativeService.historyAt (source fuel) inputs index
        (cut.depth + 1)).state.LiveAt 0) ∧
    ((OutstandingSource.History.NativeService.historyAt (source fuel) (branchInputs cut word)
      index (cut.depth + 1)).state.TerminalAt 0 ↔
      (OutstandingSource.History.NativeService.historyAt (source fuel) inputs index
        (cut.depth + 1)).state.TerminalAt 0) := by
  simp only [OutstandingSource.History.NativeService.native_live_iff_unpaid,
    OutstandingSource.History.NativeService.native_terminal_iff_recorded,
    OutstandingSource.History.NativeService.frameAt]
  have same := congrArg (fun past => past.frame.payments)
    (branch_preserves_the_common_actual_prefix cut word (cut.depth + 2) (Nat.le_refl _))
  constructor <;> rw [show cut.depth + 1 + 1 = cut.depth + 2 by omega] <;> rw [same]

theorem common_cut_has_the_same_full_financial_matrix (cut : Cut fuel inputs) (word : List Action) :
    Financial.BalanceConservation.ledgerClaims (input fuel (branchInputs cut word))
      (Runtime.account fuel (branchInputs cut word) (cut.depth + 2)).current =
    Financial.BalanceConservation.ledgerClaims (input fuel inputs)
      (Runtime.account fuel inputs (cut.depth + 2)).current := by
  rw [Financial.BalanceConservation.generated_prefix_claims _ (zero_financial_genesis _ _) _,
    Financial.BalanceConservation.generated_prefix_claims _ (zero_financial_genesis _ _) _]
  have same : currentAt fuel (branchInputs cut word) (cut.depth + 2) = currentAt fuel inputs (cut.depth + 2) :=
    ((OutstandingSource.History.actual_frame (source fuel) (branchInputs cut word) _).1.trans
      (congrArg (fun past => past.frame.raw)
        (branch_preserves_the_common_actual_prefix cut word _ (Nat.le_refl _)))).trans
      (OutstandingSource.History.actual_frame (source fuel) inputs _).1.symm
  exact congrArg (fun current => current.claims) same

structure FutureInput (cut : Cut fuel inputs) (word : List Action) where
  private mk ::
  accepted : ∀ item ∈ law.rawItems cut.past.frame.raw word, law.Valid item.before item.request
  future : FiniteContinuation 1 (afterInput cut word)
  generated : future = generate (afterInput cut word) 1
  actual_word : (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).submitted = word
  actual_before : (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).before = cut.past.frame.raw
  original_row : ProgrammeLedger.transferReceiptOf (input fuel (branchInputs cut word))
    (OutstandingSource.History.taskWrite (source fuel) (branchInputs cut word) (cut.depth + 1)).2 =
    some (OutstandingSource.History.writtenReceipt (source fuel) (branchInputs cut word) (cut.depth + 1))

def acceptFutureInput (cut : Cut fuel inputs) (word : List Action)
    (accepted : ∀ item ∈ law.rawItems cut.past.frame.raw word, law.Valid item.before item.request) :
    FutureInput cut word :=
  ⟨accepted, generate (afterInput cut word) 1, rfl, new_input_is_actually_emitted cut word,
    new_input_uses_the_original_cut cut word,
    OutstandingSource.History.receipt_is_in_own_original_write _ _ _⟩

def FutureInput.oldMandate (cut : Cut fuel inputs) {word : List Action} (_branch : FutureInput cut word)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :=
  Runtime.traceGrant fuel inputs birth.val cut.depth grant

def FutureInput.newMandate (cut : Cut fuel inputs) {word : List Action} (_branch : FutureInput cut word)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :=
  Runtime.traceGrant fuel (branchInputs cut word) birth.val (afterInput cut word).depth
    (transportOriginalGrant cut word birth grant)

theorem FutureInput.original_grant_is_in_the_new_records (cut : Cut fuel inputs) {word : List Action}
    (branch : FutureInput cut word) (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val))
    (actual : grant ∈ grantsAt base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) :
    (⟨⟨birth.val, by change birth.val < (branchInputs cut word).length + 1; rw [branchInputs_length]; omega⟩,
      branch.newMandate cut birth grant⟩ : Sigma fun born : Fin ((afterInput cut word).depth + 1) =>
        Runtime.TracedGrant fuel (branchInputs cut word) born.val (afterInput cut word).depth) ∈
      Runtime.recordsAt fuel (branchInputs cut word) (afterInput cut word).depth :=
  Runtime.every_original_grant_is_retained _ _ _ _ _ (transported_grant_is_actually_present cut word birth grant actual)



theorem future_input_paid_slot_is_native_terminal (cut : Cut fuel inputs) (word : List Action)
    (index : (source fuel).Slot) (paid : Nat) (recorded : cut.past.frame.payments index = some paid) :
    (afterInput cut word).past.frame.payments index = some paid ∧
    (OutstandingSource.History.NativeService.historyAt (source fuel) (branchInputs cut word) index
      ((afterInput cut word).depth + 1)).state.TerminalAt 0 := by
  have preserved := future_input_keeps_each_original_service_archive cut word index paid recorded
  refine ⟨preserved, (OutstandingSource.History.NativeService.native_terminal_iff_recorded _ _ _ _).mpr ?_⟩
  change ∃ paid, (trailAt fuel (branchInputs cut word) ((afterInput cut word).depth + 1 + 1)).frame.payments index = some paid
  rw [show (afterInput cut word).depth + 1 + 1 = (afterInput cut word).depth + 2 by omega,
    ← (afterInput cut word).actual]
  exact ⟨paid, preserved⟩

theorem future_input_unpaid_slot_has_exact_native_disposition (cut : Cut fuel inputs) (word : List Action)
    (index : (source fuel).Slot) (unpaid : cut.past.frame.payments index = none) :
    ((OutstandingSource.History.NativeService.historyAt (source fuel) (branchInputs cut word) index
      ((afterInput cut word).depth + 1)).state.LiveAt 0 ↔
      ¬ (source fuel).SlotPaid cut.past.frame.raw word index) ∧
    ((OutstandingSource.History.NativeService.historyAt (source fuel) (branchInputs cut word) index
      ((afterInput cut word).depth + 1)).state.TerminalAt 0 ↔
      (source fuel).SlotPaid cut.past.frame.raw word index) := by
  simp only [OutstandingSource.History.NativeService.native_live_iff_unpaid,
    OutstandingSource.History.NativeService.native_terminal_iff_recorded,
    OutstandingSource.History.NativeService.frameAt]
  constructor
  · change (trailAt fuel (branchInputs cut word) ((afterInput cut word).depth + 2)).frame.payments index = none ↔ _
    rw [← (afterInput cut word).actual, afterInput_is_the_interpreted_original_cut]
    exact cut.past.unpaid_append_iff word index unpaid
  · change (∃ paid, (trailAt fuel (branchInputs cut word) ((afterInput cut word).depth + 2)).frame.payments index = some paid) ↔ _
    rw [← (afterInput cut word).actual, afterInput_is_the_interpreted_original_cut]
    change (∃ paid, (source fuel).update cut.past.frame.payments cut.past.frame.raw word cut.past.length index = some paid) ↔ _
    simp only [OutstandingSource.update, unpaid]
    by_cases paid : (source fuel).SlotPaid cut.past.frame.raw word index
    · simp [paid]
    · simp [paid]

theorem future_input_post_matrix_is_its_own_actual_claims (cut : Cut fuel inputs) (word : List Action) :
    Financial.BalanceConservation.ledgerClaims (input fuel (branchInputs cut word))
      (Runtime.account fuel (branchInputs cut word) ((afterInput cut word).depth + 2)).current =
      (afterInput cut word).past.frame.raw.claims := by
  rw [Financial.BalanceConservation.generated_prefix_claims _ (zero_financial_genesis _ _) _]
  exact congrArg (fun current => current.claims) (afterInput cut word).actual_current.symm

structure RefusedFutureInput (cut : Cut fuel inputs) (word : List Action) where
  private mk ::
  item : {item // item ∈ law.rawItems cut.past.frame.raw word}
  refused : ¬ law.Valid item.val.before item.val.request
  future : FiniteContinuation 1 (afterInput cut word)
  generated : future = generate (afterInput cut word) 1

inductive FutureAttempt (cut : Cut fuel inputs) (word : List Action) where
  | private accepted (branch : FutureInput cut word)
  | private refused (evidence : RefusedFutureInput cut word)

def attemptFutureInput (cut : Cut fuel inputs) (word : List Action) : FutureAttempt cut word :=
  match found : (law.rawItems cut.past.frame.raw word).find?
      (fun item => decide (¬ law.Valid item.before item.request)) with
  | some item => .refused ⟨⟨item, List.mem_of_find?_eq_some found⟩,
      of_decide_eq_true (List.find?_some
        (p := fun (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit) =>
          decide (¬ law.Valid item.before item.request)) found), generate (afterInput cut word) 1, rfl⟩
  | none => .accepted (acceptFutureInput cut word (by
      intro item member
      have checked := List.find?_eq_none.mp found item member
      by_contra invalid
      exact checked (by simp only [decide_eq_true_eq]; exact invalid)))

def FutureAttempt.isAccepted {cut : Cut fuel inputs} {word : List Action} : FutureAttempt cut word → Bool
  | .accepted _ => true
  | .refused _ => false


theorem FutureAttempt.acceptance_iff_valid {cut : Cut fuel inputs} {word : List Action}
    (attempt : FutureAttempt cut word) :
    attempt.isAccepted = true ↔ ∀ item ∈ law.rawItems cut.past.frame.raw word, law.Valid item.before item.request := by
  rcases attempt with ⟨branch⟩ | ⟨evidence⟩
  · exact ⟨fun _ => branch.accepted, fun _ => rfl⟩
  · constructor
    · intro impossible; cases impossible
    · intro valid
      exact False.elim (evidence.refused (valid evidence.item.val evidence.item.property))

def FutureAttempt.future {cut : Cut fuel inputs} {word : List Action} :
    FutureAttempt cut word → FiniteContinuation 1 (afterInput cut word)
  | .accepted branch => branch.future
  | .refused evidence => evidence.future

theorem RefusedFutureInput.is_an_actual_refused_item {cut : Cut fuel inputs} {word : List Action}
    (evidence : RefusedFutureInput cut word) :
    evidence.item.val ∈ law.rawItems
      (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).before
      (actualExecution fuel (branchInputs cut word) (cut.depth + 1)).submitted ∧
      ¬ law.Valid evidence.item.val.before evidence.item.val.request := by
  rw [new_input_is_actually_emitted, new_input_uses_the_original_cut]
  exact ⟨evidence.item.property, evidence.refused⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure
