import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Consumers
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.PublicPast.Fold

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Payment

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Functions.Revision.InitialAdmissionAt origin}

def consumeItems (items : List (Epoch.Finance.ActualItem input depth count))
    (account : (Epoch.Finance.process input depth count).GeneratedState) :=
  items.foldl (fun before item => (Epoch.Finance.consume input depth count item before).next input depth count) account

def NonFinancial (operation : Operation Party Good Technology Instrument) : Prop :=
  match operation with
  | .issue .. | .assign .. | .settle .. => False
  | _ => True

def NonFinancialInput (raw : Compile.RawInput Party Good Port Technology Instrument) : Prop :=
  match raw with
  | .primitive request => NonFinancial request.operation
  | .execute word => ∀ request ∈ word, NonFinancial request.operation
  | .advance => False
  | _ => True

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem a_nonfinancial_public_opcode_contains_only_its_original_nonfinancial_requests
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (raw : Compile.RawInput Party Good Port Technology Instrument) (nonfinancial : NonFinancialInput raw)
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : Physical.Public.wordAt before raw = some word) :
    ∀ request ∈ word, NonFinancial request.operation := by
  cases raw with
  | primitive request =>
      have same : [request.resign request.signer] = word := Option.some.inj selected
      subst word
      intro action member
      obtain rfl := List.mem_singleton.mp member
      exact nonfinancial
  | execute requests =>
      have same : requests.map (fun request => request.resign request.signer) = word := Option.some.inj selected
      subst word
      intro action member
      obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
      exact nonfinancial original originalMember
  | advance => exact nonfinancial.elim
  | migrate target => cases selected
  | code programme => cases selected
  | review phase => cases selected
  | stopReview => cases selected

theorem the_nonfinancial_public_execution_keeps_its_original_request_kinds
    (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
    (cursor : Physical.Cursor Party Good Port Technology Instrument)
    (nonfinancial : NonFinancialInput cursor.incoming) :
    ∀ item ∈ (Physical.Public.execution input depth count prefixLimit renewalLimit oldPast cursor).items,
      NonFinancial item.request.operation := by
  unfold Physical.Public.execution
  cases produced : Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast cursor with
  | accepted word selected checked =>
      have kinds := a_nonfinancial_public_opcode_contains_only_its_original_nonfinancial_requests
        _ cursor.incoming nonfinancial word selected
      intro item member
      apply kinds item.request
      rw [← (Physical.Public.interpreter input).inventory_requests_exact _ 0 word]
      exact List.mem_map.mpr ⟨item,member,rfl⟩
  | refused word selected item listed failed => exact fun _ member => (List.not_mem_nil member).elim
  | metadata selected => exact fun _ member => (List.not_mem_nil member).elim

theorem the_original_nonfinancial_item_keeps_the_native_account
    (item : Epoch.Finance.ActualItem input depth count)
    (before : (Epoch.Finance.process input depth count).GeneratedState)
    (nonfinancial : NonFinancial (item.instruction input depth count).request.operation) :
    (Epoch.Finance.consume input depth count item before).next input depth count = before := by
  unfold Epoch.Finance.consume
  split
  · rfl
  · split
    · rename_i claim returned
      have operation := claim.operation
      rw [Epoch.Finance.readNewClaim_origin input depth count item claim returned] at operation
      rw [operation] at nonfinancial
      exact nonfinancial.elim
    · split
      · rename_i movement returned
        rw [movement.operation] at nonfinancial
        cases kind : movement.kind <;> simp only [kind,NonFinancial] at nonfinancial
      · rfl

theorem the_original_nonfinancial_inventory_keeps_the_native_account
    (items : List (Epoch.Finance.ActualItem input depth count))
    (before : (Epoch.Finance.process input depth count).GeneratedState)
    (nonfinancial : ∀ item ∈ items, NonFinancial (item.instruction input depth count).request.operation) :
    consumeItems items before = before := by
  induction items generalizing before with
  | nil => rfl
  | cons item tail inherited =>
      change consumeItems tail ((Epoch.Finance.consume input depth count item before).next input depth count) = before
      rw [the_original_nonfinancial_item_keeps_the_native_account item before
        (nonfinancial item List.mem_cons_self)]
      exact inherited before (fun item original => nonfinancial item (List.mem_cons_of_mem _ original))

def remainingAccount (frame : Macro.Public.Runtime.Frame origin admission) :=
  consumeItems ((Macro.Public.Accounting.items input depth count prefixLimit renewalLimit
    origin.germ.snapshot.past frame.start).drop frame.actual.actual.position) frame.account

theorem the_actual_head_uses_the_original_native_consumer
    (frame : Macro.Public.Runtime.Frame origin admission)
    (item : Epoch.Finance.ActualItem input depth count)
    (head : Macro.Public.Accounting.item? input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past frame.start frame.actual.actual = some item) :
    frame.next.start = frame.start ∧
      frame.next.actual.actual.position = frame.actual.actual.position + 1 ∧
      frame.next.account = (Epoch.Finance.consume input depth count item frame.account).next input depth count := by
  have work : frame.HasWork := Or.inr (by rw [head]; rfl)
  have selected : frame.next = frame.internalNext work := by
    rw [Macro.Public.Runtime.Frame.next,dif_pos work]
  unfold Macro.Public.Runtime.Frame.internalNext at selected
  split at selected
  · rename_i registered parsed
    rw [selected]
    refine ⟨rfl,rfl,?_⟩
    exact (Macro.Public.Accounting.the_macro_hold_does_not_erase_a_new_issue_write input depth count
      prefixLimit renewalLimit origin.germ.snapshot.past frame.start registered).symm.trans
        (Macro.Public.Accounting.every_actual_head_has_its_literal_source_account input depth count
          prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual frame.paid item head)
  · rename_i parsed
    rw [selected]
    refine ⟨rfl,?_,?_⟩
    · change (Macro.Public.Accounting.nativeNext input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.start frame.actual.actual).position = _
      rw [Macro.Public.Accounting.nativeNext,dif_pos frame.paid,head]
      exact (Macro.Public.Accounting.Current.after_item_reads_the_source_generated_native_account
        frame.actual.actual frame.paid item).2.1
    · exact Macro.Public.Accounting.every_actual_head_has_its_literal_source_account input depth count
        prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual frame.paid item head

theorem the_actual_drain_is_the_same_original_consumer_fold
    (frame : Macro.Public.Runtime.Frame origin admission) :
    frame.drained.account = remainingAccount frame := by
  let items := Macro.Public.Accounting.items input depth count prefixLimit renewalLimit
    origin.germ.snapshot.past frame.start
  by_cases work : frame.HasWork
  · cases head : Macro.Public.Accounting.item? input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.start frame.actual.actual with
    | none =>
        change frame.actual.actual.bodyPaid = false ∨ _ at work
        simp [frame.paid,head] at work
    | some item =>
        have updated := the_actual_head_uses_the_original_native_consumer frame item head
        have present : items[frame.actual.actual.position]? = some item := by
          simpa only [Macro.Public.Accounting.item?,frame.paid,if_true] using head
        obtain ⟨within,original⟩ := List.getElem?_eq_some_iff.mp present
        have tail : items.drop frame.actual.actual.position =
            item :: items.drop (frame.actual.actual.position + 1) := by
          rw [List.drop_eq_getElem_cons within,original]
        have remaining : remainingAccount frame.next = remainingAccount frame := by
          have sameItems := congrArg (fun start => Macro.Public.Accounting.items input depth count
            prefixLimit renewalLimit origin.germ.snapshot.past start) updated.1
          have sameTail := congrArg₂ (fun position source => List.drop position source) updated.2.1 sameItems
          have sameAccount := congrArg₂ (fun source account => consumeItems source account) sameTail updated.2.2
          exact sameAccount.trans (by
            change consumeItems (items.drop (frame.actual.actual.position + 1))
                ((Epoch.Finance.consume input depth count item frame.account).next input depth count) =
              consumeItems (items.drop frame.actual.actual.position) frame.account
            rw [tail]
            rfl)
        have first : frame.drained.account = frame.next.drained.account := by
          unfold Macro.Public.Runtime.Frame.drained
          rw [Macro.Public.Runtime.Frame.drain,dif_pos work]
          simp only [Macro.Public.Runtime.Frame.visits,Function.iterate_succ_apply]
        exact first.trans ((the_actual_drain_is_the_same_original_consumer_fold frame.next).trans remaining)
  · have noHead : Macro.Public.Accounting.item? input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.start frame.actual.actual = none := by
      cases found : Macro.Public.Accounting.item? input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past frame.start frame.actual.actual with
      | none => rfl
      | some item => exact (work (Or.inr (by rw [found]; rfl))).elim
    have absent : items[frame.actual.actual.position]? = none := by
      simpa only [Macro.Public.Accounting.item?,frame.paid,if_true] using noHead
    have empty : items.drop frame.actual.actual.position = [] :=
      List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp absent)
    have first : frame.drained.account = frame.account := by
      unfold Macro.Public.Runtime.Frame.drained
      rw [Macro.Public.Runtime.Frame.drain,dif_neg work]
      rfl
    refine first.trans ?_
    change frame.account = consumeItems (items.drop frame.actual.actual.position) frame.account
    rw [empty]
    rfl
termination_by frame.sourceMass
decreasing_by exact frame.every_internal_next_strictly_lowers_the_actual_source work

theorem the_actual_nonfinancial_body_keeps_its_entire_original_account
    (frame : Macro.Public.Runtime.Frame origin admission)
    (nonfinancial : NonFinancialInput frame.start.incoming) :
    frame.drained.account = frame.account := by
  have kinds := the_nonfinancial_public_execution_keeps_its_original_request_kinds
    (input := input) (depth := depth) (count := count) (prefixLimit := prefixLimit)
    (renewalLimit := renewalLimit) origin.germ.snapshot.past frame.start nonfinancial
  rw [the_actual_drain_is_the_same_original_consumer_fold]
  apply the_original_nonfinancial_inventory_keeps_the_native_account
  intro item member
  have original := List.mem_of_mem_drop member
  have actual : item.instruction input depth count ∈
      (Physical.Public.execution input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start).items := by
    rw [← Macro.Public.Accounting.actual_items_are_the_same_public_execution
      input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start]
    exact List.mem_map.mpr ⟨item,original,rfl⟩
  exact kinds _ actual

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Payment
