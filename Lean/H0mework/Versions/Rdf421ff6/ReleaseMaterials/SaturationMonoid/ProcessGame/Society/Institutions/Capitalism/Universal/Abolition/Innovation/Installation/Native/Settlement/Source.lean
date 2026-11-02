import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement

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

theorem the_inventory_fold_is_the_original_financial_visit
    (tag : Epoch.Interface.Tag input depth count) (visit : Epoch.Interface.Visit input depth count tag)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    Payment.consumeItems (Epoch.Finance.inventory input depth count tag visit) before =
      Epoch.Finance.consumeVisit input depth count tag visit before := by
  unfold Epoch.Finance.consumeVisit
  generalize Epoch.Finance.inventory input depth count tag visit = items
  induction items generalizing before with
  | nil => rfl
  | cons item tail inherited =>
      exact inherited ((Epoch.Finance.consume input depth count item before).next input depth count)

theorem the_new_original_body_consumes_its_own_financial_inventory
    (frame : Macro.Public.Runtime.Frame origin admission) (complete : ¬ frame.HasWork) :
    frame.next.drained.account = Epoch.Finance.consumeVisit input depth count
      (Macro.Public.Accounting.tag input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.next.start)
      (Macro.Public.Accounting.visit input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.next.start)
      frame.account := by
  have sameAccount : frame.next.account = frame.account := by
    rw [Macro.Public.Runtime.Frame.next,dif_neg complete]
    rfl
  have position := the_new_raw_reentry_starts_at_its_original_first_head frame complete
  let items := Macro.Public.Accounting.items input depth count prefixLimit renewalLimit
    origin.germ.snapshot.past frame.next.start
  have tail : items.drop frame.next.actual.actual.position = items :=
    (congrArg (fun position => items.drop position) position).trans List.drop_zero
  exact (Payment.the_actual_drain_is_the_same_original_consumer_fold frame.next).trans
    ((congrArg₂ (fun source account => Payment.consumeItems source account) tail sameAccount).trans
      (the_inventory_fold_is_the_original_financial_visit _ _ frame.account))

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem the_same_actual_cursor_is_its_original_public_event
    (cursor : Physical.Cursor Party Good Port Technology Instrument) :
    Epoch.Interface.ActualOccurrence.eventCursor cursor.past cursor.incoming = cursor := by
  cases cursor
  unfold Epoch.Interface.ActualOccurrence.eventCursor Physical.receive
  rw [Physical.Prefix.past_readback]

private theorem the_actual_drain_keeps_its_original_snapshot
    (frame : Macro.Public.Runtime.Frame origin admission) : frame.drained.snapshot = frame.snapshot := by
  by_cases work : frame.HasWork
  · have sameStart : frame.next.start = frame.start := by
      rw [Macro.Public.Runtime.Frame.next,dif_pos work]
      unfold Macro.Public.Runtime.Frame.internalNext
      split <;> rfl
    have sameSnapshot := frame.next.snapshot_is_the_literal_after.trans
      ((congrArg Physical.next sameStart).trans frame.snapshot_is_the_literal_after.symm)
    have first : frame.drained.snapshot = frame.next.drained.snapshot := by
      unfold Macro.Public.Runtime.Frame.drained
      rw [Macro.Public.Runtime.Frame.drain,dif_pos work]
      simp only [Macro.Public.Runtime.Frame.visits,Function.iterate_succ_apply]
    exact first.trans ((the_actual_drain_keeps_its_original_snapshot frame.next).trans sameSnapshot)
  · unfold Macro.Public.Runtime.Frame.drained
    rw [Macro.Public.Runtime.Frame.drain,dif_neg work]
    rfl
termination_by frame.sourceMass
decreasing_by exact frame.every_internal_next_strictly_lowers_the_actual_source work

theorem a_real_public_step_has_its_same_original_prefix_and_account
    (frame : Macro.Public.Runtime.Frame origin admission) (complete : ¬ frame.HasWork) :
    frame.next.drained.snapshot.past = frame.snapshot.past ++ [frame.next.start.incoming] ∧
      frame.next.drained.account = Epoch.Finance.consumeVisit input depth count
        (Epoch.Interface.Actors.PublicPast.eventTag input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past frame.snapshot.past frame.next.start.incoming)
        (Epoch.Interface.Actors.PublicPast.eventVisit input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past frame.snapshot.past frame.next.start.incoming) frame.account := by
  have prior : frame.next.start.past = frame.snapshot.past := by
    rw [Macro.Public.Runtime.Frame.next,dif_neg complete]
    rfl
  have cursor : Epoch.Interface.ActualOccurrence.eventCursor frame.snapshot.past frame.next.start.incoming =
      frame.next.start :=
    (congrArg (fun past => Epoch.Interface.ActualOccurrence.eventCursor past frame.next.start.incoming) prior.symm).trans
      (the_same_actual_cursor_is_its_original_public_event frame.next.start)
  constructor
  · exact (congrArg Physical.Cursor.past
      (the_actual_drain_keeps_its_original_snapshot frame.next)).trans
        ((congrArg Physical.Cursor.past frame.next.snapshot_is_the_literal_after).trans
          (congrArg (fun past => past ++ [frame.next.start.incoming]) prior))
  · exact (the_new_original_body_consumes_its_own_financial_inventory frame complete).trans
      (congrArg (fun start : Physical.Cursor Party Good Port Technology Instrument =>
        Epoch.Finance.consumeVisit input depth count
          (Macro.Public.Accounting.tag input depth count prefixLimit renewalLimit origin.germ.snapshot.past start)
          (Macro.Public.Accounting.visit input depth count prefixLimit renewalLimit origin.germ.snapshot.past start)
          frame.account) cursor).symm

theorem the_original_public_fold_splits_at_its_actual_source_cut
    (oldPast prior left right : List (Compile.RawInput Party Good Port Technology Instrument))
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit oldPast prior (left ++ right) before =
      Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit oldPast (prior ++ left) right
        (Epoch.Finance.PublicPast.foldFrom input depth count prefixLimit renewalLimit oldPast prior left before) := by
  induction left generalizing prior before with
  | nil => simp only [List.nil_append,List.append_nil,Epoch.Finance.PublicPast.foldFrom]
  | cons raw left inherited =>
      simp only [List.cons_append,Epoch.Finance.PublicPast.foldFrom,inherited,List.append_assoc,List.nil_append]

theorem the_original_public_account_appends_its_same_event
    (oldPast past : List (Compile.RawInput Party Good Port Technology Instrument))
    (raw : Compile.RawInput Party Good Port Technology Instrument)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    Epoch.Finance.PublicPast.account input depth count prefixLimit renewalLimit oldPast (past ++ [raw]) before =
      Epoch.Finance.consumeVisit input depth count
        (Epoch.Interface.Actors.PublicPast.eventTag input depth count prefixLimit renewalLimit oldPast past raw)
        (Epoch.Interface.Actors.PublicPast.eventVisit input depth count prefixLimit renewalLimit oldPast past raw)
        (Epoch.Finance.PublicPast.account input depth count prefixLimit renewalLimit oldPast past before) := by
  exact the_original_public_fold_splits_at_its_actual_source_cut oldPast [] past [raw] before

theorem the_nonfinancial_public_event_keeps_the_same_original_account
    (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
    (cursor : Physical.Cursor Party Good Port Technology Instrument)
    (before : (Epoch.Finance.process input depth count).GeneratedState)
    (nonfinancial : Payment.NonFinancialInput cursor.incoming) :
    Epoch.Finance.consumeVisit input depth count
      (Macro.Public.Accounting.tag input depth count prefixLimit renewalLimit oldPast cursor)
      (Macro.Public.Accounting.visit input depth count prefixLimit renewalLimit oldPast cursor) before = before := by
  refine (the_inventory_fold_is_the_original_financial_visit _ _ before).symm.trans ?_
  apply Payment.the_original_nonfinancial_inventory_keeps_the_native_account
  have kinds := Payment.the_nonfinancial_public_execution_keeps_its_original_request_kinds
    (input := input) (depth := depth) (count := count) (prefixLimit := prefixLimit)
    (renewalLimit := renewalLimit) oldPast cursor nonfinancial
  intro item member
  have original : item.instruction input depth count ∈
      (Physical.Public.execution input depth count prefixLimit renewalLimit oldPast cursor).items := by
    rw [← Macro.Public.Accounting.actual_items_are_the_same_public_execution
      input depth count prefixLimit renewalLimit oldPast cursor]
    exact List.mem_map.mpr ⟨item,member,rfl⟩
  exact kinds _ original

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement
