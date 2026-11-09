import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.NamedSlot
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Attached
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.OriginalSlot
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Composition

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

open ResponsibilityLifecycle
open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

private theorem single_trace {before after : C} {command : R} (trace : Trace before [command] after) :
    Ready before ∧ ReviewAvailable before ∧ command.consents = [] ∧
      (Physical.Public.interpreter before.native.input).Valid before.raw command ∧ after = afterNative before command := by
  cases trace with
  | cons _ _ _ _ ready review consents valid tail =>
    cases tail
    exact ⟨ready, review, consents, valid, rfl⟩

private abbrev prepayment := front ++ [levy]
private abbrev before := Conflict.Root.terminal source prepayment
private abbrev after := Conflict.Root.terminal source conflict

set_option maxHeartbeats 1500000 in
theorem the_paid_conflict_reaches_the_named_old_principal :
    Conflict.Root.SameOldSlot source conflict position 1 6 := by
  have actual : Trace source (prepayment ++ [settle]) after := by
    have word : prepayment ++ [settle] = conflict := by simp only [prepayment, conflict, List.append_assoc, List.singleton_append]
    rw [word]
    exact conflictPaid.trace
  have tail := Conflict.Root.trace_after_prefix source after prepayment [settle] actual
  obtain ⟨ready, review, consent, valid, actualEnd⟩ := single_trace tail
  have prior := Conflict.Root.trace_before_prefix source after prepayment [settle] actual
  have kept := (the_paid_body_keeps_the_native_account before settle ready).trans
    (Conflict.Root.nonfinancial_trace_keeps_the_entire_native_book prior (by decide +kernel))
  let body := afterBody before settle
  obtain ⟨item, identity, interpreter, consumed⟩ :=
    the_paid_primitive_has_one_literal_native_consumer before settle ready review consent valid
  have operation : (item.instruction _ _ _).request.operation = .settle () true false 6 :=
    congrArg (fun (entry : ExecutionItem Bool Bool Bool Unit Unit) => entry.request.operation) identity
  have admitted : (item.interpreter _ _ _).Valid (item.instruction _ _ _).before (item.instruction _ _ _).request := by
    rw [interpreter, identity]
    exact valid
  obtain ⟨sameInput, sameDepth, sameCount⟩ := Quantities.Execution.the_actual_script_keeps_the_original_reader_indices
    source (Quantities.Execution.primitiveScript prepayment)
  have parameter := (queued before settle).advance_parameters
  have input := parameter.1.trans sameInput
  have depth := parameter.2.1.trans sameDepth
  have count := parameter.2.2.1.trans sameCount
  have read := read_native_same (nativeAccount source) (nativeAccount body) input depth count kept
    (fun input depth count account => account.current.slots[1]?.map (fun row =>
      let claim := Epoch.Finance.slotClaim input depth count row
      (claim.instrument _ _ _, claim.debtor _ _ _)))
  have address : (slotAt body 1).map (slotAddress body) = some ((), true) :=
    read.trans the_original_index_read.1
  have originalPrincipal : principalAt body 1 false = 6 :=
    (read_native_same (nativeAccount source) (nativeAccount body) input depth count kept
      (fun input depth count account => Allocation.balanceAt input depth count account 1 false)).trans
      the_original_index_read.2.1
  have originalPriority : priorityBefore body position 1 = 0 :=
    (read_native_same (nativeAccount source) (nativeAccount body) input depth count kept
      (fun input depth count account => Allocation.prefixCapacity input depth count account
        0 1 position.instrument position.debtor position.creditor)).trans the_original_index_read.2.2
  obtain ⟨slot, present, oldAddress⟩ := Option.map_eq_some_iff.mp address
  have named : NamesOpenSlot source position 1 := by
    refine ⟨the_original_index_read.1, ?_⟩
    change 0 < principalAt source 1 false
    rw [the_original_index_read.2.1]
    norm_num
  cases slot with
  | terminal archive =>
    simp [principalAt, present, Epoch.Finance.slotBalance] at originalPrincipal
  | live obligation =>
    have coordinates : obligation.content.instrument _ _ _ = () ∧ obligation.content.debtor _ _ _ = true :=
      ⟨congrArg Prod.fst oldAddress, congrArg Prod.snd oldAddress⟩
    let paid := (Epoch.Finance.consume _ _ _ item (nativeAccount body)).next _ _ _
    have consumption := (nativeAccount_heq_of_eq actualEnd).trans consumed
    obtain ⟨finalInput, finalDepth, finalCount⟩ := Quantities.Execution.the_actual_script_keeps_the_original_reader_indices
      source (Quantities.Execution.primitiveScript conflict)
    have params : after.native.input = body.native.input ∧ after.native.depth = body.native.depth ∧
        after.native.count = body.native.count :=
      ⟨finalInput.trans input.symm, finalDepth.trans depth.symm, finalCount.trans count.symm⟩
    have balance : principalAt after 1 false = Allocation.balanceAt _ _ _ paid 1 false :=
      read_native_same paid (nativeAccount after) params.1 params.2.1 params.2.2 consumption
        (fun input depth count account => Allocation.balanceAt input depth count account 1 false)
    have transferred := Allocation.the_literal_native_payment_reduces_the_named_old_slot_by_its_exact_share
      _ _ _ item () true false 6 operation admitted (nativeAccount body) 1 obligation present coordinates
    have paidAmount : principalAt after 1 false = 0 := by
      rw [balance, transferred]
      change principalAt body 1 false - min (principalAt body 1 false) (max 0 (6 - priorityBefore body position 1)) = _
      rw [originalPrincipal, originalPriority]
      norm_num
    have archive := Epoch.Finance.InstructionResult.original_claims_retained _ _ _
      (Epoch.Finance.consume _ _ _ item (nativeAccount body))
    have nextAddress := read_native_same paid (nativeAccount after) params.1 params.2.1 params.2.2 consumption
      (fun input depth count account => account.current.slots[1]?.map (fun row =>
        let claim := Epoch.Finance.slotClaim input depth count row
        (claim.instrument _ _ _, claim.debtor _ _ _)))
    refine ⟨named, ?_, ?_⟩
    · change (slotAt after 1).map (slotAddress after) = _ at nextAddress
      change (slotAt after 1).map (slotAddress after) = _
      rw [nextAddress]
      rw [← List.getElem?_map]
      have addresses := archive.map (fun claim =>
        (claim.instrument _ _ _, claim.debtor _ _ _))
      simp only [List.map_map, Function.comp_def] at addresses
      obtain ⟨extra, extended⟩ := addresses
      have fits := (List.getElem?_eq_some_iff.mp present).1
      rw [← extended, List.getElem?_append_left (by simpa only [List.length_map] using fits),
        List.getElem?_map]
      exact address
    · change principalAt source 1 false - principalAt after 1 false = 6
      rw [the_original_index_read.2.1, paidAmount, sub_zero]

#print axioms the_paid_conflict_reaches_the_named_old_principal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving
