import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Uniform
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

open Capitalism.Universal.Source.Program (RawLaw)
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open OriginalSource (Current Write Policy currentAt writeAt NoActualDamage)
open Runtime.OriginalProgramme (input people orderedMenus)

noncomputable section

private abbrev paidOrigin := Settlement.settledCut.raw
private abbrev trueFirst := orderedMenus true
private abbrev paidCurrent :=
  Runtime.currentAt Settlement.settled input paidOrigin people trueFirst
private abbrev paidWrite :=
  Runtime.writeAt Settlement.settled input paidOrigin people trueFirst
private abbrev paidAttempt :=
  Runtime.eventAt Settlement.settled input paidOrigin people trueFirst

/-- The original first three whole writes lead to the settled current.
The first new service lets the other original person go first. -/
def safeOrderReplay : Trace Current Write where
  current := fun visit => if visit < 3 then commonExternalReplay.current visit else paidCurrent (visit - 3)
  effect := fun visit => if visit < 3 then commonExternalReplay.effect visit else some (paidWrite (visit - 3))

theorem safe_order_reads_each_actual_tail_current (n : Nat) :
    safeOrderReplay.current (3 + n) = paidCurrent n := by
  change (if 3 + n < 3 then commonExternalReplay.current (3 + n) else paidCurrent (3 + n - 3)) = _
  rw [if_neg (by omega : ¬ 3 + n < 3), show 3 + n - 3 = n by omega]

theorem safe_order_writes_each_actual_tail_service (n : Nat) :
    safeOrderReplay.effect (3 + n) = some (paidWrite n) := by
  change (if 3 + n < 3 then commonExternalReplay.effect (3 + n) else some (paidWrite (3 + n - 3))) = _
  rw [if_neg (by omega : ¬ 3 + n < 3), show 3 + n - 3 = n by omega]

private theorem reads_common_opening (visit : Nat) (early : visit ≤ 3) :
    safeOrderReplay.current visit = commonExternalReplay.current visit := by
  by_cases before : visit < 3
  · exact if_pos before
  · have endOfOpening : visit = 3 := by omega
    subst visit
    rfl

private theorem writes_common_opening (visit : Nat) (early : visit < 3) :
    safeOrderReplay.effect visit = commonExternalReplay.effect visit :=
  if_pos early

private theorem safe_order_width (visit : Nat) : safeOrderReplay.width visit = 1 := by
  unfold Trace.width
  by_cases early : visit < 3
  · rw [writes_common_opening visit early]
    rfl
  · let n := visit - 3
    have tail : visit = 3 + n := by omega
    rw [tail, safe_order_writes_each_actual_tail_service]

theorem safe_order_ordinal (visit : Nat) : safeOrderReplay.ordinal visit = visit := by
  induction visit with
  | zero => rfl
  | succ visit prior => rw [Trace.ordinal, prior, safe_order_width]

theorem safe_order_keeps_the_same_opening (policy : Policy) :
    safeOrderReplay.current 0 = currentAt policy 0 ∧
      ∀ visit < 3, safeOrderReplay.Check (currentAt policy) (writeAt policy) visit := by
  have opening := the_same_actual_external_replay_bypasses_every_protected_policy policy
  refine ⟨(reads_common_opening 0 (by omega)).trans opening.1, ?_⟩
  intro visit early
  have commonOrdinal (n : Nat) : commonExternalReplay.ordinal n = n := replay_ordinal _ n
  simpa only [Trace.Check, writes_common_opening visit early, reads_common_opening visit (by omega),
    reads_common_opening (visit + 1) (by omega), safe_order_ordinal, commonOrdinal] using opening.2.1 visit early

private theorem funded : TerminalPeace.Supply.Stocked paidOrigin :=
  Completion.the_original_payment_releases_the_living_reserve

private def signers (items : List Original.Item) : List Bool :=
  items.map fun item => item.request.signer

private theorem true_first_inventory :
    signers (paidWrite 0).2 = [true, true, false, false] := by
  change signers (paidAttempt 0).items = _
  have items := Runtime.OriginalProgramme.the_ordered_renewal_keeps_its_exact_written_items
    Settlement.settled true funded 0
  change (paidAttempt 0).items = _ at items
  rw [items]
  rfl

private theorem false_first_inventory :
    signers Completion.peace.val.items = [false, false, true, true] := by
  let before := Installation.originalNative Completion.anchor
  change signers (Renewal.readAction before Renewal.service).execution.items = _
  have items := (TerminalPeace.Supply.the_native_renewal_pays_both_original_bearers before funded).2.1
  change (Renewal.readAction before Renewal.service).execution.items = _ at items
  rw [items, RawLaw.rawItems, TerminalPeace.Supply.the_renewal_inventory_is_exact before.raw funded]
  rfl

theorem the_safe_external_write_has_different_original_item_order (policy : Policy) :
    ∃ written, safeOrderReplay.effect 3 = some written ∧
      written.2.map (fun item => item.request.signer) = [true, true, false, false] ∧
      (writeAt policy 3).2.map (fun item => item.request.signer) = [false, false, true, true] := by
  refine ⟨paidWrite 0, safe_order_writes_each_actual_tail_service 0, true_first_inventory, ?_⟩
  exact false_first_inventory

theorem the_first_safe_external_mismatch_is_the_actual_item_order (policy : Policy) :
    ¬ safeOrderReplay.Check (currentAt policy) (writeAt policy) 3 := by
  obtain ⟨written, emitted, trueOrder, falseOrder⟩ :=
    the_safe_external_write_has_different_original_item_order policy
  intro checked
  unfold Trace.Check at checked
  rw [emitted, safe_order_ordinal] at checked
  have same := congrArg (fun write : Write => write.2.map fun item => item.request.signer) checked.1
  rw [trueOrder, falseOrder] at same
  contradiction

theorem the_safe_external_replay_cannot_factor_through_the_fixed_order (policy : Policy) :
    ¬ ∃ factor, safeOrderReplay.Factors (currentAt policy) (writeAt policy) factor := by
  rintro ⟨_, factor⟩
  exact the_first_safe_external_mismatch_is_the_actual_item_order policy
    ((safeOrderReplay.checks_of_factor _ _ factor).2 3)

theorem the_safe_order_and_the_fixed_order_generate_the_same_paid_raw :
    (paidAttempt 0).after.raw = Completion.peace.val.native.raw := by
  have paid := Runtime.OriginalProgramme.the_ordered_renewal_keeps_its_exact_successor
    Settlement.settled true funded 0
  change (paidAttempt 0).after.raw =
    { paidOrigin with clock := paidOrigin.clock + 1, round := paidOrigin.round + 1 } at paid
  refine paid.trans ((congrArg (fun raw : Original.Raw =>
    { raw with clock := raw.clock + 1, round := raw.round + 1 }) Settlement.settled_raw).trans ?_)
  rw [Completion.the_first_peace_write_reads_the_paid_current]
  apply Capitalism.Universal.Source.Program.RawCurrent.ext
  · rfl
  · rfl
  · rfl
  · decide +kernel
  · decide +kernel

theorem the_two_ordered_programmes_keep_the_same_raw_at_each_visit (n : Nat) :
    (paidAttempt n).before.raw =
      (Runtime.eventAt Settlement.settled input paidOrigin people (orderedMenus false) n).before.raw := by
  induction n with
  | zero => rfl
  | succ n same =>
    change (paidAttempt n).after.raw =
      (Runtime.eventAt Settlement.settled input paidOrigin people (orderedMenus false) n).after.raw
    have trueNext := Runtime.OriginalProgramme.the_ordered_renewal_keeps_its_exact_successor
      Settlement.settled true funded n
    have falseNext := Runtime.OriginalProgramme.the_ordered_renewal_keeps_its_exact_successor
      Settlement.settled false funded n
    exact trueNext.trans ((congrArg (fun raw : Original.Raw =>
      { raw with clock := raw.clock + 1, round := raw.round + 1 }) same).trans falseNext.symm)

theorem the_safe_external_order_has_cofinal_paid_time :
    ∀ start bound, ∃ visit ≥ start, bound < (safeOrderReplay.current visit).2 := by
  intro start bound
  obtain ⟨n, later, beyond⟩ := Runtime.OriginalProgramme.the_ordered_source_hours_are_cofinal
    Settlement.settled true funded start bound
  refine ⟨3 + n, by omega, ?_⟩
  rw [safe_order_reads_each_actual_tail_current]
  exact beyond

theorem every_safe_order_tail_pays_and_keeps_each_independent_exit (n : Nat) :
    Runtime.ReadyAt Settlement.settled input paidOrigin people trueFirst n :=
  Runtime.OriginalProgramme.every_ordered_due_visit_and_personal_exit_are_generated
    Settlement.settled true funded n

theorem every_safe_order_tail_retains_the_original_cleared_row (n : Nat) :
    (Runtime.run Settlement.settled input paidOrigin people trueFirst n).state.stack.balances =
      [(Original.occurrence, Settlement.clearedBalance)] :=
  (Runtime.every_actual_visit_keeps_the_original_rows Settlement.settled input paidOrigin people trueFirst n).trans
    Settlement.settled_balances

theorem every_safe_order_tail_has_no_new_damage (n : Nat) :
    NoActualDamage (safeOrderReplay.effect (3 + n)) := by
  rw [safe_order_writes_each_actual_tail_service]
  let attempt := paidAttempt n
  change ∀ item ∈ attempt.items, ∀ key,
    Reparation.loss TerminalPeace.Supply.physical Original.community item key = 0
  obtain ⟨_, paid, items, _⟩ := attempt.accepted_effect (every_safe_order_tail_pays_and_keeps_each_independent_exit n).1
  intro item listed key
  have own := paid.own item (items ▸ listed)
  let physical : Supply.OwnItem TerminalPeace.Supply.physical people item :=
    ⟨own.operation, own.member, own.noConsent, PublicFunction.valid_physical
      TerminalPeace.Supply.revisedLaw item.before item.request own.valid⟩
  exact physical.opens_no_coercive_loss Original.community key

theorem the_safe_external_replay_never_opens_new_damage (visit : Nat) :
    NoActualDamage (safeOrderReplay.effect visit) := by
  by_cases early : visit < 3
  · rw [writes_common_opening visit early]
    have opening : visit = 0 ∨ visit = 1 ∨ visit = 2 := by omega
    rcases opening with rfl | rfl | rfl
    · change ∀ item ∈ Boundary.Actual.items Original.cut ExposureGuard.stop, _
      rw [ExposureGuard.the_open_original_recourse_dispatches_a_material_free_stop _ Original.review]
      intro item listed
      exact (List.not_mem_nil listed).elim
    · change ∀ item ∈ Boundary.Actual.items Settlement.physicalCut Settlement.payerInput, _
      rw [Settlement.actual_payment_items, Settlement.protected_stock]
      intro item listed key
      rw [List.mem_singleton.mp listed]
      rcases key with ⟨payer, holder, good⟩
      cases payer <;> cases holder <;> cases good <;> decide +kernel
    · change ∀ item ∈ Boundary.Actual.items
        (endAt Original.seed (Settlement.protectedPast ++ [Settlement.payerInput])) none, _
      rw [Settlement.the_return_native_step_has_no_material_item]
      intro item listed
      exact (List.not_mem_nil listed).elim
  · have tail : visit = 3 + (visit - 3) := by omega
    rw [tail]
    exact every_safe_order_tail_has_no_new_damage _

#print axioms the_safe_external_write_has_different_original_item_order
#print axioms the_safe_external_replay_cannot_factor_through_the_fixed_order
#print axioms the_safe_order_and_the_fixed_order_generate_the_same_paid_raw
#print axioms the_two_ordered_programmes_keep_the_same_raw_at_each_visit
#print axioms the_safe_external_order_has_cofinal_paid_time
#print axioms every_safe_order_tail_pays_and_keeps_each_independent_exit
#print axioms every_safe_order_tail_retains_the_original_cleared_row
#print axioms the_safe_external_replay_never_opens_new_damage

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel
