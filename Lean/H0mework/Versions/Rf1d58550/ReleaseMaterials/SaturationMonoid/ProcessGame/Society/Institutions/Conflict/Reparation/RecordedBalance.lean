import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Discharge
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Composition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "inventory" => Quantities.Execution.inventory
local notation "endAt" => Quantities.Execution.endAt
local notation "script" => Quantities.Execution.primitiveScript

def recordedReceived (source : C) (attack : Word) (history : Script) (key : Key Party Good) : ℚ :=
  ((inventory (Root.terminal source attack) history).map
    (fun item => receiptCredit source.native.input.law item key)).sum

/-- Only deliveries from the actual original execution are counted, even
when the suffix mixes epoch inputs with native accounting steps. -/
def recordedDue (source : C) (attack : Word) (history : Script) (community : Party → Community)
    (key : Key Party Good) : ℚ :=
  max 0 (gross source attack community key - recordedReceived source attack history key)

theorem recordedDue_at_opening {source : C} {attack : Word} {community : Party → Community}
    {key : Key Party Good} (claim : ClaimAt source attack community key) :
    recordedDue source attack [] community key = gross source attack community key := by
  simp [recordedDue, recordedReceived, Quantities.Execution.inventory, max_eq_right claim.positive.le]

theorem recordedDue_zero_iff (source : C) (attack : Word) (history : Script)
    (community : Party → Community) (key : Key Party Good) :
    recordedDue source attack history community key = 0 ↔
      gross source attack community key ≤ recordedReceived source attack history key := by
  unfold recordedDue
  exact ⟨fun closed => sub_nonpos.mp (closed ▸ le_max_right _ _),
    fun paid => max_eq_left (sub_nonpos.mpr paid)⟩

theorem closing_the_recorded_balance_requires_an_actual_victim_receipt
    {source : C} {attack : Word} {community : Party → Community} {key : Key Party Good}
    (claim : ClaimAt source attack community key) (history : Script)
    (closed : recordedDue source attack history community key = 0) :
    ∃ item ∈ inventory (Root.terminal source attack) history,
      0 < receiptCredit source.native.input.law item key := by
  by_contra missing
  have zero : recordedReceived source attack history key = 0 := by
    unfold recordedReceived
    apply List.sum_eq_zero
    rintro amount listed
    obtain ⟨item, actual, rfl⟩ := List.mem_map.mp listed
    exact le_antisymm (le_of_not_gt fun positive => missing ⟨item, actual, positive⟩)
      (receipt_nonnegative _ _ _)
  have covered := (recordedDue_zero_iff source attack history community key).mp closed
  exact (not_le_of_gt claim.positive) (zero ▸ covered)

theorem recordedDue_append_le (source : C) (attack : Word) (past suffix : Script)
    (community : Party → Community) (key : Key Party Good) :
    recordedDue source attack (past ++ suffix) community key ≤ recordedDue source attack past community key := by
  unfold recordedDue recordedReceived
  rw [Quantities.Execution.inventory_append, List.map_append, List.sum_append]
  apply max_le_max le_rfl
  apply sub_le_sub_left
  apply le_add_of_nonneg_right
  apply List.sum_nonneg
  rintro credit listed
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp listed
  exact receipt_nonnegative _ _ _

theorem recordedDue_append_without_receipts (source : C) (attack : Word) (past suffix : Script)
    (community : Party → Community) (key : Key Party Good)
    (noReceipt : ∀ item ∈ inventory (endAt (Root.terminal source attack) past) suffix,
      receiptCredit source.native.input.law item key = 0) :
    recordedDue source attack (past ++ suffix) community key = recordedDue source attack past community key := by
  have zero : ((inventory (endAt (Root.terminal source attack) past) suffix).map
      (fun item => receiptCredit source.native.input.law item key)).sum = 0 := by
    apply List.sum_eq_zero
    rintro amount member
    obtain ⟨item, actual, rfl⟩ := List.mem_map.mp member
    exact noReceipt item actual
  simp only [recordedDue, recordedReceived, Quantities.Execution.inventory_append, List.map_append,
    List.sum_append, zero, add_zero]

theorem recordedDue_after_a_unilateral_suffix {source : C} {attack : Word}
    {community : Party → Community} {key : Key Party Good} (claim : ClaimAt source attack community key)
    (past suffix : Script)
    (unilateral : ∀ item ∈ inventory (endAt (Root.terminal source attack) past) suffix,
      community item.request.signer = community key.2.1) :
    recordedDue source attack (past ++ suffix) community key = recordedDue source attack past community key := by
  obtain ⟨damage, _, positive⟩ := claim.has_original_loss
  have foreign := (positive_loss_is_an_actual_foreign_debit _ _ _ _ positive).1.1
  apply recordedDue_append_without_receipts
  intro item actual
  have absent : item.request.signer ≠ key.1 := by
    intro signed
    exact foreign ((congrArg community signed).symm.trans (unilateral item actual))
  simp [receiptCredit, absent]

/-- The recorded path extends the existing raw claim compiler without
changing its value on any actual primitive history. -/
theorem recordedDue_of_paid_word {source : C} {attack tail : Word} {community : Party → Community}
    {key : Key Party Good} (claim : ClaimAt source attack community key)
    (actual : Root.Paid source (attack ++ tail)) :
    recordedDue source attack (script tail) community key = remaining source attack tail community key := by
  have original := original_inventory actual
  rw [Quantities.Execution.primitiveScript_append, Quantities.Execution.inventory_append,
    original_inventory claim.paid] at original
  change
    (occurred source attack).map (fun item => { item with index := 0 }) ++
      inventory (Root.terminal source attack) (script tail) =
        (occurred source (attack ++ tail)).map (fun item => { item with index := 0 }) at original
  have size : (occurred source attack).length = attack.length :=
    source.native.input.law.inventory_length source.raw 0 attack
  have suffix := congrArg (List.drop attack.length) original
  rw [List.drop_left' (by simpa only [List.length_map] using size), ← List.map_drop] at suffix
  unfold recordedDue recordedReceived remaining received
  rw [suffix, List.map_map]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation
