import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Financial

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement

noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev FinanceSources :=
  SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Finance.sources

def sharePosition (obligation : AdmittedObligation (Financial.Family.vocabulary FinanceSources)) (creditor : Bool) :=
  (⟨obligation.content.2.instrument, obligation.content.2.debtor, creditor⟩ :
    Repayment.Position Bool Unit)

theorem positive_share_is_a_selected_debt_position
    (index : Fin inventory.finance.current.slots.length)
    (obligation : AdmittedObligation (Financial.Family.vocabulary FinanceSources)) (creditor : Bool)
    (present : inventory.finance.current.slots.get index = .live obligation)
    (positive : 0 < Financial.BalanceConservation.shareAt
      (FinanceSources obligation.content.1) obligation.residual creditor) :
    sharePosition obligation creditor ∈ Handoff.debtPositions (current epoch inventory.inputs) := by
  have slotMember : .live obligation ∈ inventory.finance.current.slots :=
    present ▸ List.get_mem inventory.finance.current.slots index
  let quantity := Financial.Family.slotClaims FinanceSources (.live obligation)
    obligation.content.2.instrument obligation.content.2.debtor creditor
  have quantity_exact : quantity = Financial.BalanceConservation.shareAt
      (FinanceSources obligation.content.1) obligation.residual creditor := by
    change (if (Financial.Family.slotClaim FinanceSources (.live obligation)).2.instrument =
        obligation.content.2.instrument ∧
        (Financial.Family.slotClaim FinanceSources (.live obligation)).2.debtor =
          obligation.content.2.debtor then
      Financial.Family.slotBalance FinanceSources (.live obligation) creditor else 0) = _
    rw [if_pos (show
      (Financial.Family.slotClaim FinanceSources (.live obligation)).2.instrument = obligation.content.2.instrument ∧
        (Financial.Family.slotClaim FinanceSources (.live obligation)).2.debtor = obligation.content.2.debtor from ⟨rfl,rfl⟩)]
    rfl
  have quantity_positive : 0 < quantity := quantity_exact ▸ positive
  have quantity_member : quantity ∈ inventory.finance.current.slots.map (fun slot =>
      Financial.Family.slotClaims FinanceSources slot obligation.content.2.instrument
        obligation.content.2.debtor creditor) := by
    apply List.mem_map.mpr
    exact ⟨.live obligation, slotMember, by simp [quantity]⟩
  have each_nonnegative : ∀ value ∈ inventory.finance.current.slots.map (fun slot =>
      Financial.Family.slotClaims FinanceSources slot obligation.content.2.instrument
        obligation.content.2.debtor creditor), 0 ≤ value := by
    intro value member
    rcases List.mem_map.mp member with ⟨slot, slotMember, sameValue⟩
    subst value
    unfold Financial.Family.slotClaims
    by_cases coordinates :
          (Financial.Family.slotClaim FinanceSources slot).2.instrument = obligation.content.2.instrument ∧
          (Financial.Family.slotClaim FinanceSources slot).2.debtor = obligation.content.2.debtor
    · rw [if_pos coordinates]
      cases slot with
      | live old =>
        have sound := Financial.Family.generated_sound FinanceSources inventory.finance (.live old) slotMember
        exact sound.2 creditor
      | terminal _ => simp [Financial.Family.slotBalance]
    · rw [if_neg coordinates]
  have ledgerPositive : 0 < Financial.Family.ledgerClaims FinanceSources
      inventory.finance.current obligation.content.2.instrument obligation.content.2.debtor creditor := by
    unfold Financial.Family.ledgerClaims
    exact lt_of_lt_of_le quantity_positive
      (List.single_le_sum each_nonnegative quantity quantity_member)
  have currentPositive : 0 < Repayment.balance (sharePosition obligation creditor) (current epoch inventory.inputs) := by
    change 0 < (current epoch inventory.inputs).claims obligation.content.2.instrument
      obligation.content.2.debtor creditor
    rw [← inventory.matrix]
    exact ledgerPositive
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true currentPositive⟩
  rcases sharePosition obligation creditor with ⟨instrument, debtor, holder⟩
  cases instrument
  cases debtor <;> cases holder <;> simp [Settlement.addresses]

theorem every_positive_current_address_has_its_own_live_slot
    (position : Repayment.Position Bool Unit)
    (positive : 0 < Repayment.balance position (current epoch inventory.inputs)) :
    ∃ (index : Fin inventory.finance.current.slots.length)
      (obligation : AdmittedObligation (Financial.Family.vocabulary FinanceSources)),
      inventory.finance.current.slots.get index = .live obligation ∧
      sharePosition obligation position.creditor = position ∧
      0 < Financial.BalanceConservation.shareAt (FinanceSources obligation.content.1)
        obligation.residual position.creditor := by
  have ledgerPositive : 0 < Financial.Family.ledgerClaims FinanceSources inventory.finance.current
      position.instrument position.debtor position.creditor := by
    rw [inventory.matrix]; exact positive
  have someSlot : ∃ slot ∈ inventory.finance.current.slots,
      0 < Financial.Family.slotClaims FinanceSources slot position.instrument position.debtor position.creditor := by
    by_contra absent
    have nonpos : Financial.Family.ledgerClaims FinanceSources inventory.finance.current
        position.instrument position.debtor position.creditor ≤ 0 := by
      have sumNonpos (values : List ℚ) (nonpos : ∀ value ∈ values, value ≤ 0) : values.sum ≤ 0 := by
        induction values with
        | nil => exact le_refl 0
        | cons first rest ih =>
          exact add_nonpos (nonpos first (List.mem_cons_self))
            (ih (fun value member => nonpos value (List.mem_cons_of_mem first member)))
      apply sumNonpos
      intro value member
      obtain ⟨slot,inside,rfl⟩ := List.mem_map.mp member
      apply le_of_not_gt
      intro pos
      exact absent ⟨slot,inside,pos⟩
    exact (not_le_of_gt ledgerPositive) nonpos
  obtain ⟨slot,member,pos⟩ := someSlot
  obtain ⟨index,inside,present⟩ := List.mem_iff_getElem.mp member
  cases slot with
  | terminal archive => simp [Financial.Family.slotClaims,Financial.Family.slotBalance] at pos
  | live obligation =>
    have coordinates : obligation.content.2.instrument = position.instrument ∧
        obligation.content.2.debtor = position.debtor := by
      unfold Financial.Family.slotClaims at pos
      split at pos
      · exact ‹_ ∧ _›
      · exact (lt_irrefl 0 pos).elim
    refine ⟨⟨index,inside⟩,obligation,present,?_,?_⟩
    · cases position with
      | mk code debtor holder =>
        dsimp only at coordinates
        rcases coordinates with ⟨rfl,rfl⟩
        rfl
    · simpa [Financial.Family.slotClaims,Financial.Family.slotClaim,Financial.Family.slotObligation,
        Financial.Family.slotBalance,Financial.BalanceConservation.shareAt,coordinates.1,coordinates.2] using pos

structure LocatedIndex (positions : List (Repayment.Position Bool Unit))
    (position : Repayment.Position Bool Unit) where
  index : Fin positions.length
  exact : positions[index] = position

def locateIndex : (positions : List (Repayment.Position Bool Unit)) →
    (position : Repayment.Position Bool Unit) → position ∈ positions →
    LocatedIndex positions position
  | [], _, member => False.elim (List.not_mem_nil member)
  | first :: rest, position, member => by
      by_cases same : position = first
      · subst position
        exact ⟨0, by simp⟩
      · have tailMember : position ∈ rest := by
          rcases List.mem_cons.mp member with head | tail
          · exact (same head).elim
          · exact tail
        obtain ⟨index, exact⟩ := locateIndex rest position tailMember
        exact ⟨index.succ, by simpa using exact⟩

def locateDebtPosition
    (position : Repayment.Position Bool Unit)
    (member : position ∈ Handoff.debtPositions (current epoch inventory.inputs)) :
    Repayment.Portfolio.Slice (Mandate.law base epoch.scope)
      (Handoff.debtPositions (current epoch inventory.inputs)) (current epoch inventory.inputs) position := by
  let located := locateIndex (Handoff.debtPositions (current epoch inventory.inputs)) position member
  exact located.exact ▸ Repayment.Portfolio.locate (Mandate.law base epoch.scope)
    (Handoff.debtPositions (current epoch inventory.inputs)) (current epoch inventory.inputs) located.index

def every_positive_share_gets_its_own_actual_repayment_slice
    (index : Fin inventory.finance.current.slots.length)
    (obligation : AdmittedObligation (Financial.Family.vocabulary FinanceSources)) (creditor : Bool)
    (present : inventory.finance.current.slots.get index = .live obligation)
    (positive : 0 < Financial.BalanceConservation.shareAt
      (FinanceSources obligation.content.1) obligation.residual creditor) :
    Repayment.Portfolio.Slice (Mandate.law base epoch.scope)
      (Handoff.debtPositions (current epoch inventory.inputs)) (current epoch inventory.inputs)
      (sharePosition obligation creditor) :=
  locateDebtPosition inventory (sharePosition obligation creditor)
    (positive_share_is_a_selected_debt_position inventory index obligation creditor present positive)


private theorem repair_preserves_other_claims
    (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (before : Current) (position : Repayment.Position Bool Unit)
    (code : Unit) (debtor creditor : Bool)
    (other : (code, debtor, creditor) ≠
      (position.instrument, position.debtor, position.creditor)) :
    (law.execute before 0 (Repayment.Portfolio.Repair.word law position before)).final.claims
      code debtor creditor = before.claims code debtor creditor := by
  unfold Repayment.Portfolio.Repair.word
  cases Repayment.respond law position before
  next clear => rfl
  next ready =>
    exact Repayment.other_positions_are_preserved law position before ready code debtor creditor other
  next positive failed =>
    rw [law.execute_append]
    dsimp only
    have paymentSame (state : Current) :
        (law.step state (Repayment.payment law position before)).claims code debtor creditor =
          state.claims code debtor creditor := by
      unfold RawLaw.step
      split
      · change state.claims code debtor creditor -
          (if (code, debtor, creditor) =
            (position.instrument, position.debtor, position.creditor) then
              Repayment.quantity law position before else 0) = _
        rw [if_neg other, sub_zero]
      · rfl
    have productionSame (state : Current) :
        (law.step state (Repayment.production law position before)).claims code debtor creditor =
          state.claims code debtor creditor := by
      unfold RawLaw.step
      split <;> rfl
    have priorEffect :
        (law.execute before 0 (Repayment.candidate law position before)).final.claims
            code debtor creditor = before.claims code debtor creditor := by
      unfold Repayment.candidate Repayment.preparation
      split <;> simp only [List.nil_append, List.cons_append, RawLaw.execute,
        paymentSame, productionSame]
    rw [← priorEffect]
    generalize (law.execute before 0 (Repayment.candidate law position before)).final = after
    generalize Repayment.Portfolio.Repair.orders law position before = orders
    have preserve : ∀ (state : Current) (index : Nat),
        ((law.execute state index (orders.map Repayment.Portfolio.Repair.Order.request)).final).claims
            code debtor creditor = state.claims code debtor creditor := by
      intro state index
      induction orders generalizing state index with
      | nil => rfl
      | cons order tail ih =>
        rw [List.map_cons, RawLaw.execute, ih]
        unfold RawLaw.step
        split <;> rfl
    exact preserve _ _

private theorem portfolio_locate_before_preserves_own_claim
    (law : RawLaw Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (positions : List (Repayment.Position Bool Unit)) (current : Current)
    (index : Fin positions.length) (nodup : positions.Nodup) :
    (Repayment.Portfolio.locate law positions current index).before.claims
        positions[index].instrument positions[index].debtor positions[index].creditor =
      current.claims positions[index].instrument positions[index].debtor positions[index].creditor := by
  induction positions generalizing current with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
    refine Fin.cases ?_ (fun smaller => ?_) index
    · rfl
    · let selected := rest[smaller]
      have selected_mem : selected ∈ rest := List.get_mem rest smaller
      have selected_ne : (selected.instrument, selected.debtor, selected.creditor) ≠
          (first.instrument, first.debtor, first.creditor) := by
        intro same
        have equal : selected = first := by
          unfold selected at same ⊢
          cases first
          cases hsel : rest[smaller]
          simp_all
        rw [equal] at selected_mem
        exact (List.nodup_cons.mp nodup).1 selected_mem
      let next := (law.execute current 0 (Repayment.Portfolio.Repair.word law first current)).final
      have recursive := ih next smaller (List.nodup_cons.mp nodup).2
      change (Repayment.Portfolio.locate law rest next smaller).before.claims
          selected.instrument selected.debtor selected.creditor = _
      rw [recursive]
      exact repair_preserves_other_claims law current first selected.instrument selected.debtor
        selected.creditor selected_ne

theorem located_debt_slice_keeps_its_own_balance
    (position : Repayment.Position Bool Unit)
    (member : position ∈ Handoff.debtPositions (current epoch inventory.inputs)) :
    (locateDebtPosition inventory position member).before.claims
        position.instrument position.debtor position.creditor =
      (current epoch inventory.inputs).claims position.instrument position.debtor position.creditor := by
  let positions := Handoff.debtPositions (current epoch inventory.inputs)
  have nodup : positions.Nodup := by
    dsimp [positions, Handoff.debtPositions]
    apply List.Nodup.filter
    simp [Settlement.addresses]
  let located := locateIndex positions position member
  have preserved := portfolio_locate_before_preserves_own_claim
    (Mandate.law base epoch.scope) positions (current epoch inventory.inputs) located.index nodup
  have transportBefore {a b : Repayment.Position Bool Unit} (same : a = b)
      (slice : Repayment.Portfolio.Slice (Mandate.law base epoch.scope) positions
        (current epoch inventory.inputs) a) : (same ▸ slice).before = slice.before := by
    cases same
    rfl
  change (located.exact ▸ Repayment.Portfolio.locate (Mandate.law base epoch.scope)
    positions (current epoch inventory.inputs) located.index).before.claims
      position.instrument position.debtor position.creditor = _
  rw [transportBefore located.exact]
  simpa only [located.exact] using preserved

def ownSlice (intent : Intent)
    (index : Fin (staged inventory intent).finance.current.slots.length)
    (obligation : AdmittedObligation (Financial.Family.vocabulary FinanceSources)) (creditor : Bool)
    (present : (staged inventory intent).finance.current.slots.get index = .live obligation)
    (positive : 0 < Financial.BalanceConservation.shareAt
      (FinanceSources obligation.content.1) obligation.residual creditor) :=
  every_positive_share_gets_its_own_actual_repayment_slice (staged inventory intent)
    index obligation creditor present positive

theorem ownSlice_positive (intent : Intent)
    (index : Fin (staged inventory intent).finance.current.slots.length)
    (obligation : AdmittedObligation (Financial.Family.vocabulary FinanceSources)) (creditor : Bool)
    (present : (staged inventory intent).finance.current.slots.get index = .live obligation)
    (positive : 0 < Financial.BalanceConservation.shareAt
      (FinanceSources obligation.content.1) obligation.residual creditor) :
    0 < Repayment.balance (sharePosition obligation creditor)
      (ownSlice inventory intent index obligation creditor present positive).before := by
  have selected := positive_share_is_a_selected_debt_position (staged inventory intent)
    index obligation creditor present positive
  change 0 < (locateDebtPosition (staged inventory intent) (sharePosition obligation creditor) selected).before.claims
    (sharePosition obligation creditor).instrument (sharePosition obligation creditor).debtor
      (sharePosition obligation creditor).creditor
  rw [located_debt_slice_keeps_its_own_balance]
  exact of_decide_eq_true (List.mem_filter.mp selected).2

theorem ready_payment_is_in_the_actual_source_history (intent : Intent)
    (index : Fin (staged inventory intent).finance.current.slots.length)
    (obligation : AdmittedObligation (Financial.Family.vocabulary FinanceSources)) (creditor : Bool)
    (present : (staged inventory intent).finance.current.slots.get index = .live obligation)
    (positive : 0 < Financial.BalanceConservation.shareAt
      (FinanceSources obligation.content.1) obligation.residual creditor)
    (ready : Repayment.Ready (Mandate.law base epoch.scope) (sharePosition obligation creditor)
      (ownSlice inventory intent index obligation creditor present positive).before) :
    ∃ item ∈ (Mandate.law base epoch.scope).rawItems (repaymentExecution inventory intent).before
        (repaymentExecution inventory intent).submitted,
      item.before = Repayment.readyCurrent (Mandate.law base epoch.scope) (sharePosition obligation creditor)
        (ownSlice inventory intent index obligation creditor present positive).before ∧
      item.request = Repayment.payment (Mandate.law base epoch.scope) (sharePosition obligation creditor)
        (ownSlice inventory intent index obligation creditor present positive).before ∧
      (Mandate.law base epoch.scope).Valid item.before item.request := by
  rw [(actual_repayment_word_and_cut inventory intent).1,(actual_repayment_word_and_cut inventory intent).2]
  exact (ownSlice inventory intent index obligation creditor present positive).ready_payment_is_in_the_whole_trace _ ready


theorem positive_slice_payment_is_an_actual_item (intent : Intent)
    (position : Repayment.Position Bool Unit)
    (slice : Repayment.Portfolio.Slice (Mandate.law base epoch.scope)
      (Handoff.debtPositions (current epoch (staged inventory intent).inputs))
      (current epoch (staged inventory intent).inputs) position)
    (positive : 0 < Repayment.balance position slice.before) :
    ∃ item ∈ (Mandate.law base epoch.scope).rawItems (repaymentExecution inventory intent).before
        (repaymentExecution inventory intent).submitted,
      item.before = Repayment.readyCurrent (Mandate.law base epoch.scope) position slice.before ∧
      item.request = Repayment.payment (Mandate.law base epoch.scope) position slice.before := by
  let law := Mandate.law base epoch.scope
  let item := (⟨(Repayment.preparation law position slice.before).length,
    Repayment.readyCurrent law position slice.before, Repayment.payment law position slice.before⟩ :
      ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
  have inCandidate : item ∈ law.rawItems slice.before (Repayment.candidate law position slice.before) := by
    by_cases cash : 0 < slice.before.stock position.debtor (law.settlementUnit position.instrument) <;>
      simp [item,Repayment.candidate,Repayment.preparation,Repayment.readyCurrent,cash,RawLaw.rawItems,RawLaw.execute]
  have inRepair : item ∈ law.rawItems slice.before (Repayment.Portfolio.Repair.word law position slice.before) := by
    by_cases ready : Repayment.Ready law position slice.before
    · rw [Repayment.Portfolio.Repair.paid_word_is_the_original_candidate law position slice.before positive ready]
      exact inCandidate
    · rw [Repayment.Portfolio.Repair.blocked_word_contains_the_candidate law position slice.before positive ready]
      unfold RawLaw.rawItems
      rw [law.execute_append]
      exact List.mem_append_left _ inCandidate
  rw [(actual_repayment_word_and_cut inventory intent).1,(actual_repayment_word_and_cut inventory intent).2]
  exact ⟨_,slice.item_is_in_the_whole_trace law item inRepair,rfl,rfl⟩

theorem positive_slice_has_a_typed_obstruction (intent : Intent)
    (position : Repayment.Position Bool Unit)
    (slice : Repayment.Portfolio.Slice (Mandate.law base epoch.scope)
      (Handoff.debtPositions (current epoch (staged inventory intent).inputs))
      (current epoch (staged inventory intent).inputs) position)
    (positive : 0 < Repayment.balance position slice.before)
    (failed : ¬ Repayment.Ready (Mandate.law base epoch.scope) position slice.before) :
    Repayment.quantity (Mandate.law base epoch.scope) position slice.before ≤ 0 ∨
      ∃ item ∈ (Mandate.law base epoch.scope).rawItems (repaymentExecution inventory intent).before
          (repaymentExecution inventory intent).submitted,
        ¬ (Mandate.law base epoch.scope).Valid item.before item.request := by
  by_cases quantityPositive : 0 < Repayment.quantity (Mandate.law base epoch.scope) position slice.before
  · right
    have refusal : ∃ item ∈ (Mandate.law base epoch.scope).rawItems slice.before
        (Repayment.candidate (Mandate.law base epoch.scope) position slice.before),
        ¬ (Mandate.law base epoch.scope).Valid item.before item.request := by
      by_contra absent
      apply failed
      refine ⟨quantityPositive,?_⟩
      intro item member
      by_contra refused
      exact absent ⟨item,member,refused⟩
    obtain ⟨item,member,refused⟩ := refusal
    have inRepair : item ∈ (Mandate.law base epoch.scope).rawItems slice.before
        (Repayment.Portfolio.Repair.word (Mandate.law base epoch.scope) position slice.before) := by
      rw [Repayment.Portfolio.Repair.blocked_word_contains_the_candidate _ _ _ positive failed]
      unfold RawLaw.rawItems
      rw [(Mandate.law base epoch.scope).execute_append]
      exact List.mem_append_left _ member
    rw [(actual_repayment_word_and_cut inventory intent).1,(actual_repayment_word_and_cut inventory intent).2]
    exact ⟨_,slice.item_is_in_the_whole_trace _ item inRepair,refused⟩
  · exact Or.inl (le_of_not_gt quantityPositive)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Financial
