import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Events

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

theorem the_single_original_execution_has_its_single_original_native_item
    (cursor : Physical.Cursor Party Good Port Technology Instrument)
    (first : ExecutionItem Party Good Port Technology Instrument)
    (body : (Physical.Public.execution input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past cursor).items = [first]) :
    ∃ item, Macro.Public.Accounting.items input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past cursor = [item] ∧ item.instruction input depth count = first ∧
      item.interpreter input depth count = Physical.Public.interpreter input := by
  have mapped := Macro.Public.Accounting.actual_items_are_the_same_public_execution
    input depth count prefixLimit renewalLimit origin.germ.snapshot.past cursor
  rw [body] at mapped
  cases inventory : Macro.Public.Accounting.items input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past cursor with
  | nil => rw [inventory] at mapped; cases mapped
  | cons item tail =>
      rw [inventory,List.map_cons] at mapped
      have empty : tail = [] := List.map_eq_nil_iff.mp (List.cons.inj mapped).2
      subst tail
      refine ⟨item,rfl,(List.cons.inj mapped).1,?_⟩
      have member : item ∈ Macro.Public.Accounting.items input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past cursor := by rw [inventory]; exact List.mem_cons_self
      unfold Macro.Public.Accounting.items Epoch.Finance.inventory at member
      obtain ⟨position,rfl⟩ := List.mem_ofFn.mp member
      rfl

theorem a_signed_source_issue_generates_the_original_claim_and_native_admission
    (prior : List (Compile.RawInput Party Good Port Technology Instrument))
    (before : (Epoch.Finance.process input depth count).GeneratedState)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ) (purpose : Port)
    (nonnegative : 0 ≤ quantity) :
    ∃ claim : Epoch.Finance.NewClaim input depth count,
      claim.instrument = instrument ∧ claim.debtor = debtor ∧ claim.holder = holder ∧ claim.quantity = quantity ∧
      Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit origin.germ.snapshot.past prior
        [.primitive ⟨debtor,[],purpose,[],.issue instrument debtor holder quantity⟩] before =
          before.step (Epoch.Finance.process input depth count) (.admit (.inr claim)) := by
  let cursor := Physical.Prefix.cursor prior
  let request : Request Party Good Port Technology Instrument :=
    ⟨debtor,[],purpose,[],.issue instrument debtor holder quantity⟩
  let raw := (Physical.Public.stateAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past cursor.past).raw
  have valid : (Physical.Public.interpreter input).Valid raw (request.resign request.signer) :=
    the_signed_public_issue_is_valid (input := input) raw instrument debtor holder quantity purpose nonnegative
  have body := the_original_valid_public_primitive_has_its_singleton_inventory
    (input := input) (origin := origin) cursor request valid
  obtain ⟨item,inventory,instruction,interpreter⟩ :=
    the_single_original_execution_has_its_single_original_native_item
      (origin := origin) (Physical.receive cursor (.primitive request)) _ body
  have operation : (item.instruction input depth count).request.operation =
      .issue instrument debtor holder quantity := by rw [instruction]; rfl
  have accepted : (item.interpreter input depth count).Valid
      (item.instruction input depth count).before (item.instruction input depth count).request := by
    rw [interpreter,instruction]
    exact valid
  have found := the_original_actual_issue_generates_its_native_claim input depth count item
    instrument debtor holder quantity operation accepted
  let claim := (Epoch.Finance.readNewClaim input depth count item).get found
  have returned : Epoch.Finance.readNewClaim input depth count item = some claim := (Option.some_get found).symm
  have original := Epoch.Finance.readNewClaim_origin input depth count item claim returned
  have declared := claim.operation
  rw [original,operation] at declared
  have coordinates := Operation.issue.inj declared
  refine ⟨claim,coordinates.1.symm,coordinates.2.1.symm,coordinates.2.2.1.symm,coordinates.2.2.2.symm,?_⟩
  have lower : Payment.consumeItems (Macro.Public.Accounting.items input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past (Physical.receive cursor (.primitive request))) before =
        before.step (Epoch.Finance.process input depth count) (.admit (.inr claim)) := by
    rw [inventory]
    change (Epoch.Finance.consume input depth count item before).next input depth count = _
    unfold Epoch.Finance.consume
    rw [dif_neg (not_not_intro accepted)]
    split
    · rename_i actual parsed
      cases Option.some.inj (parsed.symm.trans returned)
      rfl
    · rename_i missing
      cases missing.symm.trans returned
  exact (the_inventory_fold_is_the_original_financial_visit _ _ before).symm.trans lower

theorem the_nonfinancial_source_prefix_preserves_the_original_native_state
    (prior word : List (Compile.RawInput Party Good Port Technology Instrument))
    (before : (Epoch.Finance.process input depth count).GeneratedState)
    (nonfinancial : ∀ raw ∈ word, Payment.NonFinancialInput raw) :
    Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past prior word before = before := by
  induction word generalizing prior before with
  | nil => rfl
  | cons raw word inherited =>
      have first := the_nonfinancial_public_event_keeps_the_same_original_account
        (input := input) (depth := depth) (count := count) (prefixLimit := prefixLimit) (renewalLimit := renewalLimit)
        origin.germ.snapshot.past (Epoch.Interface.ActualOccurrence.eventCursor prior raw) before
        (nonfinancial raw List.mem_cons_self)
      change Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit origin.germ.snapshot.past
        (prior ++ [raw]) word _ = before
      exact (congrArg (fun account : (Epoch.Finance.process input depth count).GeneratedState =>
        Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit origin.germ.snapshot.past
          (prior ++ [raw]) word account) first).trans
        (inherited _ before (fun raw original => nonfinancial raw (List.mem_cons_of_mem _ original)))

theorem an_accepted_original_primitive_has_its_original_native_consumption
    (prior : List (Compile.RawInput Party Good Port Technology Instrument))
    (before : (Epoch.Finance.process input depth count).GeneratedState)
    (request : Request Party Good Port Technology Instrument)
    (accepted : (Physical.Public.resultAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past
      (Epoch.Interface.ActualOccurrence.eventCursor prior (.primitive request))).isAccepted = true) :
    ∃ item : Epoch.Finance.ActualItem input depth count,
      (item.instruction input depth count).request.operation = request.operation ∧
      (item.interpreter input depth count).Valid
        (item.instruction input depth count).before (item.instruction input depth count).request ∧
      Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit origin.germ.snapshot.past prior
        [.primitive request] before = (Epoch.Finance.consume input depth count item before).next input depth count := by
  let cursor := Epoch.Interface.ActualOccurrence.eventCursor prior (.primitive request)
  cases produced : Physical.Public.resultAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past cursor with
  | accepted word selected checked =>
      have same : [request.resign request.signer] = word := Option.some.inj selected
      subst word
      have body : (Physical.Public.execution input depth count prefixLimit renewalLimit origin.germ.snapshot.past cursor).items =
          [⟨0,(Physical.Public.stateAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past cursor.past).raw,
            request.resign request.signer⟩] := by
        unfold Physical.Public.execution
        rw [produced]
        rfl
      obtain ⟨item,inventory,instruction,interpreter⟩ :=
        the_single_original_execution_has_its_single_original_native_item (origin := origin) cursor _ body
      refine ⟨item,?_,?_,?_⟩
      · rw [instruction]
        rfl
      · rw [interpreter,instruction]
        exact checked _ (by simp only [RawLaw.rawItems,RawLaw.execute,List.mem_singleton])
      · exact (the_inventory_fold_is_the_original_financial_visit _ _ before).symm.trans (by
          change Payment.consumeItems (Macro.Public.Accounting.items input depth count prefixLimit renewalLimit
            origin.germ.snapshot.past cursor) before = _
          rw [inventory]
          rfl)
  | refused word selected item listed failed =>
      change (Physical.Public.resultAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past cursor).isAccepted = true at accepted
      rw [produced] at accepted
      cases accepted
  | metadata selected =>
      change (Physical.Public.resultAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past cursor).isAccepted = true at accepted
      rw [produced] at accepted
      cases accepted

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Events
