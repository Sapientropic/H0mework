import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Incidence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- A repair credit is the victim's own admitted receipt of the original
material from the original debtor. An ordinary posting or a third party's
gift can still occur without discharging this address. -/
def receiptCredit (law : Law) (item : Item) (key : Key Party Good) : ℚ :=
  if item.request.signer = key.1 ∧ law.Valid item.before item.request then
    match item.request.operation with
    | .transfer payer payee _ =>
        if payer = key.2.1 ∧ payee = key.1 then
          max 0 (flowAt (law.actualCredit item.before item.request) key.1 key.2.2)
        else 0
    | _ => 0
  else 0

omit [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community] in
theorem receipt_nonnegative (law : Law) (item : Item) (key : Key Party Good) :
    0 ≤ receiptCredit law item key := by
  unfold receiptCredit
  split
  · split <;> try exact le_rfl
    split
    · exact le_max_left _ _
    · exact le_rfl
  · exact le_rfl

omit [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community] in
theorem positive_receipt_has_the_original_signature_and_delivery
    (law : Law) (item : Item) (key : Key Party Good) (positive : 0 < receiptCredit law item key) :
    item.request.signer = key.1 ∧ law.Valid item.before item.request ∧
      ∃ goods, item.request.operation = .transfer key.2.1 key.1 goods ∧
        flowAt (law.actualCredit item.before item.request) key.1 key.2.2 = receiptCredit law item key := by
  by_cases signed : item.request.signer = key.1 ∧ law.Valid item.before item.request
  · cases form : item.request.operation <;> simp only [receiptCredit, if_pos signed, form] at positive
    case transfer payer payee goods =>
      by_cases exactAddress : payer = key.2.1 ∧ payee = key.1
      · rw [if_pos exactAddress, lt_max_iff] at positive
        have incoming := positive.resolve_left (lt_irrefl 0)
        exact ⟨signed.1, signed.2, goods, by rw [← exactAddress.1, ← exactAddress.2],
          by simp only [receiptCredit, if_pos signed, form, if_pos exactAddress, max_eq_right incoming.le]⟩
      · simp [exactAddress] at positive
    all_goals exact (lt_irrefl 0 positive).elim
  · simp [receiptCredit, signed] at positive

/-- The paid attack stays the literal prefix of every later disposition.
These are suffix positions of the original word, not a second receipt book. -/
def continuationItems (source : C) (attack tail : Word) : List Item :=
  (occurred source (attack ++ tail)).drop attack.length

theorem continuation_requests (source : C) (attack tail : Word) :
    (continuationItems source attack tail).map ExecutionItem.request = tail := by
  change (((source.native.input.law.execute source.raw 0 (attack ++ tail)).items.drop attack.length).map
    ExecutionItem.request) = tail
  rw [List.map_drop, RawLaw.inventory_requests_exact]
  simp

def received (source : C) (attack tail : Word) (key : Key Party Good) : ℚ :=
  ((continuationItems source attack tail).map (fun item => receiptCredit source.native.input.law item key)).sum

theorem received_nonnegative (source : C) (attack tail : Word) (key : Key Party Good) :
    0 ≤ received source attack tail key := by
  unfold received
  apply List.sum_nonneg
  rintro payment present
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
  exact receipt_nonnegative _ _ _

def remaining (source : C) (attack tail : Word) (community : Party → Community) (key : Key Party Good) : ℚ :=
  max 0 (gross source attack community key - received source attack tail key)

theorem remaining_append_le (source : C) (attack front back : Word) (community : Party → Community)
    (key : Key Party Good) :
    remaining source attack (front ++ back) community key ≤ remaining source attack front community key := by
  let law := source.native.input.law
  have prefixItems : occurred source (attack ++ front) <+: occurred source (attack ++ (front ++ back)) := by
    rw [← List.append_assoc]
    change (law.execute source.raw 0 (attack ++ front)).items <+:
      (law.execute source.raw 0 ((attack ++ front) ++ back)).items
    rw [law.execute_append source.raw 0 (attack ++ front) back]
    exact ⟨_, rfl⟩
  have follows := prefixItems.drop attack.length
  change continuationItems source attack front <+: continuationItems source attack (front ++ back) at follows
  obtain ⟨extra, original⟩ := follows
  have more : received source attack front key ≤ received source attack (front ++ back) key := by
    unfold received
    rw [← original, List.map_append, List.sum_append]
    apply le_add_of_nonneg_right
    apply List.sum_nonneg
    rintro quantity listed
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp listed
    exact receipt_nonnegative _ _ _
  exact max_le_max le_rfl (sub_le_sub_left more _)

theorem initial_remaining_is_the_original_amount
    {source : C} {attack : Word} {community : Party → Community} {key : Key Party Good}
    (claim : ClaimAt source attack community key) :
    remaining source attack [] community key = gross source attack community key := by
  have none : continuationItems source attack [] = [] :=
    List.map_eq_nil_iff.mp (continuation_requests source attack [])
  rw [remaining, received, none, List.map_nil, List.sum_nil, sub_zero, max_eq_right claim.positive.le]

theorem delivered_and_remaining_balance (source : C) (attack tail : Word) (community : Party → Community)
    (key : Key Party Good) :
    remaining source attack tail community key + min (gross source attack community key)
      (received source attack tail key) = gross source attack community key := by
  unfold remaining
  rcases le_total (gross source attack community key) (received source attack tail key) with covered | short
  · rw [max_eq_left (sub_nonpos.mpr covered), min_eq_left covered, zero_add]
  · rw [max_eq_right (sub_nonneg.mpr short), min_eq_right short]
    ring

theorem discharge_iff_received (source : C) (attack tail : Word) (community : Party → Community)
    (key : Key Party Good) :
    remaining source attack tail community key = 0 ↔
      gross source attack community key ≤ received source attack tail key := by
  unfold remaining
  exact ⟨fun closed => sub_nonpos.mp (closed ▸ le_max_right _ _),
    fun paid => max_eq_left (sub_nonpos.mpr paid)⟩

theorem unilateral_carry_keeps_the_entire_original_debt {source : C} {attack : Word}
    {community : Party → Community} {key : Key Party Good} (claim : ClaimAt source attack community key)
    (tail : Word) (unilateral : ∀ request ∈ tail, community request.signer = community key.2.1) :
    remaining source attack tail community key = gross source attack community key := by
  obtain ⟨origin, _, positive⟩ := claim.has_original_loss
  have foreign := (positive_loss_is_an_actual_foreign_debit _ _ _ _ positive).1.1
  have empty : received source attack tail key = 0 := by
    unfold received
    apply List.sum_eq_zero
    rintro quantity member
    obtain ⟨item, inside, rfl⟩ := List.mem_map.mp member
    have requestIn : item.request ∈ tail := by
      rw [← continuation_requests source attack tail]
      exact List.mem_map.mpr ⟨item, inside, rfl⟩
    have notSigned : item.request.signer ≠ key.1 := by
      intro same
      exact foreign ((congrArg community same).symm.trans (unilateral item.request requestIn))
    simp [receiptCredit, notSigned]
  rw [remaining, empty, sub_zero, max_eq_right claim.positive.le]

theorem unilateral_carry_cannot_archive {source : C} {attack : Word}
    {community : Party → Community} {key : Key Party Good} (claim : ClaimAt source attack community key)
    (tail : Word) (unilateral : ∀ request ∈ tail, community request.signer = community key.2.1) :
    0 < remaining source attack tail community key := by
  rw [unilateral_carry_keeps_the_entire_original_debt claim tail unilateral]
  exact claim.positive

theorem closed_has_a_victim_receipt_in_the_original_whole_write
    {source : C} {attack tail : Word} {community : Party → Community} {key : Key Party Good}
    (claim : ClaimAt source attack community key) (paid : Root.Paid source (attack ++ tail))
    (closed : remaining source attack tail community key = 0) :
    ∃ item ∈ Quantities.Execution.inventory source (Quantities.Execution.primitiveScript (attack ++ tail)),
      item.request.signer = key.1 ∧ 0 < receiptCredit source.native.input.law item key := by
  have somePositive : ∃ item ∈ continuationItems source attack tail,
      0 < receiptCredit source.native.input.law item key := by
    by_contra absent
    have zero : received source attack tail key = 0 := by
      unfold received
      apply List.sum_eq_zero
      rintro amount present
      obtain ⟨item, member, rfl⟩ := List.mem_map.mp present
      exact le_antisymm (le_of_not_gt fun positive => absent ⟨item, member, positive⟩)
        (receipt_nonnegative _ _ _)
    exact (ne_of_gt (claim.positive.trans_le ((discharge_iff_received _ _ _ _ _).mp closed))) zero
  obtain ⟨item, member, positive⟩ := somePositive
  refine ⟨{item with index := 0}, ?_, (positive_receipt_has_the_original_signature_and_delivery _ _ _ positive).1,
    positive⟩
  rw [original_inventory paid]
  exact List.mem_map.mpr ⟨item, List.mem_of_mem_drop member, rfl⟩

inductive Decision (source : C) (attack tail : Word) (community : Party → Community) (key : Key Party Good)
  | refused (original : ClaimAt source attack community key) (issue : Root.Failure source (attack ++ tail))
  | outstanding (original : ClaimAt source attack community key) (actual : Root.Paid source (attack ++ tail))
      (unpaid : 0 < remaining source attack tail community key)
  | discharged (original : ClaimAt source attack community key) (actual : Root.Paid source (attack ++ tail))
      (zero : remaining source attack tail community key = 0)

def inspect {source : C} {attack : Word} {community : Party → Community} {key : Key Party Good}
    (claim : ClaimAt source attack community key) (tail : Word) :
    Decision source attack tail community key :=
  match Root.inspect source (attack ++ tail) with
  | .rejected issue => .refused claim issue
  | .paid actual =>
    if cleared : remaining source attack tail community key = 0 then .discharged claim actual cleared
    else .outstanding claim actual (lt_of_le_of_ne (le_max_left _ _) (Ne.symm cleared))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation
