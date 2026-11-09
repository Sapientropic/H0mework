import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Priority
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Consumers.Payment

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

open ResponsibilityLifecycle
open PublicFunction.Repayment
open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

noncomputable section

def position : Position Bool Unit := ⟨(), true, false⟩

private theorem the_original_base_keeps_its_old_retired_slot :
    ∃ archive, (nativeAccount Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual.base).current.slots =
      [.terminal archive] := by
  open Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact in
  open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Consumers in
  obtain ⟨archive, slots, _, _⟩ := actual_retirement_keeps_the_original_address_and_archive
  refine ⟨archive, ?_⟩
  change (Evolving.Epoch.Transition.nativeNext Evolving.Epoch.Consumers.current
    Evolving.Epoch.Consumers.original_complete).actual.actual.account.current.slots = _
  rw [(Evolving.Epoch.Transition.body_is_not_replayed_or_financially_reset
    Evolving.Epoch.Consumers.current Evolving.Epoch.Consumers.original_complete).1]
  change Evolving.Epoch.Consumers.original.actual.actual.account.current.slots = _
  have account := Evolving.Source.initial_reads_the_completed_original_financial_account
    seed grossClaim the_source_generates_its_own_sufficient_plan Evolving.Epoch.Consumers.reader
  exact (congrArg (fun state => state.current.slots) account).trans slots

private theorem there_is_one_old_closed_row_before_issuance :
    (nativeAccount Original.source).current.slots.length = 1 ∧ priorityBefore Original.source position 1 = 0 := by
  open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual in
  have kept := a_paid_transfer_keeps_the_literal_native_debt_account base Evolving.Epoch.Consumers.repair
    base_ready base_review rfl the_original_food_repair_is_actually_payable true false [(true,1)] rfl
  open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual in
  obtain ⟨sameInput, depth, count⟩ := Quantities.Execution.the_actual_script_keeps_the_original_reader_indices
    base (Quantities.Execution.primitiveScript [Evolving.Epoch.Consumers.repair])
  obtain ⟨archive, archived⟩ := the_original_base_keeps_its_old_retired_slot
  open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual in
  have lengths := read_native_same (nativeAccount base) (nativeAccount Original.source) sameInput depth count kept
    (fun _ _ _ account => account.current.slots.length)
  open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual in
  have priorities := read_native_same (nativeAccount base) (nativeAccount Original.source) sameInput depth count kept
    (fun input depth count account => Allocation.prefixCapacity input depth count account
      0 1 position.instrument position.debtor position.creditor)
  refine ⟨lengths.trans (by rw [archived]; rfl), ?_⟩
  unfold priorityBefore
  rw [priorities, Allocation.prefixCapacity, archived]
  simp only [List.drop_zero, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, slotClaims_terminal, add_zero]

private theorem issueValid : (Physical.Public.interpreter Original.source.native.input).Valid Original.source.raw issue := by
  rw [Original.source_input_is_the_original_registered_input, Original.the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

set_option maxHeartbeats 1500000 in
theorem the_original_index_read :
    (slotAt source 1).map (slotAddress source) = some ((), true) ∧
      principalAt source 1 false = 6 ∧ priorityBefore source position 1 = 0 := by
  let body := afterBody Original.source issue
  obtain ⟨item, identity, interpreter, paid⟩ := the_paid_primitive_has_one_literal_native_consumer
    Original.source issue Original.source_ready Original.source_review rfl issueValid
  have operation : (item.instruction _ _ _).request.operation = .issue () true false 6 :=
    congrArg (fun (entry : ExecutionItem Bool Bool Bool Unit Unit) => entry.request.operation) identity
  have valid : (item.interpreter _ _ _).Valid (item.instruction _ _ _).before (item.instruction _ _ _).request := by
    rw [interpreter, identity]
    exact issueValid
  obtain ⟨claim, read, instrument, debtor, holder, quantity⟩ :
      ∃ claim, Epoch.Finance.readNewClaim _ _ _ item = some claim ∧
        claim.instrument = () ∧ claim.debtor = true ∧ claim.holder = false ∧ claim.quantity = 6 := by
    unfold Epoch.Finance.readNewClaim
    split
    · rename_i observed
      cases operation.symm.trans observed
      rw [dif_pos valid]
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    · rename_i notIssue
      exact (notIssue () true false 6 operation).elim
  let original := nativeAccount body
  let updated := (Epoch.Finance.consume _ _ _ item original).next _ _ _
  let slot := ObligationSlot.live (Epoch.Finance.admission _ _ _ (.inr claim)).toObligation
  have appended : updated.current.slots = original.current.slots ++ [slot] := by
    unfold updated Epoch.Finance.consume
    rw [dif_neg (not_not_intro valid)]
    split
    · rename_i other observed
      cases Option.some.inj (observed.symm.trans read)
      rfl
    · rename_i absent
      cases absent.symm.trans read
  have oldParams := (queued Original.source issue).advance_parameters
  have newParams := body.advance_parameters
  have book := the_paid_body_keeps_the_native_account Original.source issue Original.source_ready
  have one : original.current.slots.length = 1 :=
    (read_native_same (nativeAccount Original.source) original oldParams.1 oldParams.2.1 oldParams.2.2.1
      book (fun _ _ _ account => account.current.slots.length)).trans
      there_is_one_old_closed_row_before_issuance.1
  have found : updated.current.slots[1]? = some slot := by
    rw [← one, appended, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have address := read_native_same updated (nativeAccount source) newParams.1 newParams.2.1 newParams.2.2.1
      paid (fun input depth count account => account.current.slots[1]?.map (fun row =>
        let claim := Epoch.Finance.slotClaim input depth count row
        (claim.instrument _ _ _, claim.debtor _ _ _)))
    change (slotAt source 1).map (slotAddress source) = _ at address
    rw [address, found]
    change some (claim.instrument, claim.debtor) = some ((), true)
    rw [instrument, debtor]
  · have balance : principalAt source 1 false = Allocation.balanceAt
      body.native.input body.native.depth body.native.count updated 1 false :=
      read_native_same updated (nativeAccount source) newParams.1 newParams.2.1 newParams.2.2.1
        paid (fun input depth count account => Allocation.balanceAt input depth count account 1 false)
    rw [balance, Allocation.balanceAt, found]
    change Epoch.Finance.claimInitial _ _ _ (.inr claim) false = _
    rw [Epoch.Finance.new_initial_balance_is_the_same_single, holder, quantity, Finsupp.single_eq_same]
  · have current := read_native_same updated (nativeAccount source) newParams.1 newParams.2.1 newParams.2.2.1
      paid (fun input depth count account => Allocation.prefixCapacity input depth count account
        0 1 position.instrument position.debtor position.creditor)
    have originalPriority := read_native_same (nativeAccount Original.source) original oldParams.1 oldParams.2.1
      oldParams.2.2.1 book (fun input depth count account => Allocation.prefixCapacity
        input depth count account 0 1 position.instrument position.debtor position.creditor)
    unfold priorityBefore
    rw [current]
    refine Eq.trans ?_ (originalPriority.trans there_is_one_old_closed_row_before_issuance.2)
    unfold Allocation.prefixCapacity
    simp only [List.drop_zero, appended, List.take_left' one]
    rw [← one, List.take_length]

#print axioms the_original_index_read

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving
