import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Balance

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Quantities.Execution (endAt)
open Reparation.Actual (Balance ReceiptAnswers)
open Occurrence.Unbounded.Nonattainment (loss born payment the_native_head_leaves_no_material)
open ExposureGuard (no_material_is_admitted)

noncomputable section

/-- The original assault's native accounting comes first. Every repayment
then has its own literal material position and its generated native head. -/
def paidPrefix (amounts : List ℚ) : Original.Word := none :: amounts.flatMap installment

abbrev fullWord : Original.Word := paidPrefix [6]

private theorem paidPrefix_snoc (amounts : List ℚ) (quantity : ℚ) :
    paidPrefix (amounts ++ [quantity]) = paidPrefix amounts ++ [payment quantity, none] := by
  simp [paidPrefix, List.flatMap_append]

private theorem full_history_snoc (amounts : List ℚ) (quantity : ℚ) :
    born ++ paidPrefix (amounts ++ [quantity]) = (born ++ paidPrefix amounts) ++ installment quantity := by
  rw [paidPrefix_snoc, List.append_assoc]

private theorem append_eligible {anchor past front tail : Original.Word}
    (first : Occurrence.EligibleFrom Original.community replies anchor past front)
    (last : Occurrence.EligibleFrom Original.community replies anchor (past ++ front) tail) :
    Occurrence.EligibleFrom Original.community replies anchor past (front ++ tail) := by
  induction front generalizing past with
  | nil => simpa only [List.append_nil, List.nil_append] using last
  | cons input front ih =>
    exact ⟨first.1, ih first.2 (by
      rwa [List.append_assoc, List.singleton_append])⟩

private theorem opening_portfolio (answers : ReceiptAnswers Original.seed) :
    (Occurrence.reached answers loss []).stack.balances = [(loss, Original.balance)] := by
  change (Occurrence.writeAfter answers (Occurrence.originState loss) []).stack.balances = _
  rw [Occurrence.writeAfter_nil_balances]
  exact Original.at_its_birth_the_whole_ledger_opens_six

private theorem reached_snoc_balances (front : Original.Word)
    (input : Reparation.Actual.Input Bool Bool Bool Unit Unit) :
    (Occurrence.reached replies loss (front ++ [input])).stack.balances =
      (Settlement.writeTick replies (Occurrence.reached replies loss front) input).stack.balances :=
  Occurrence.writeAfter_snoc_balances replies (Occurrence.originState loss) front input

/-- Each finite positive partition is executed in order on the actual
original ledger. The residual is exactly the unpaid part of its original six. -/
theorem the_installment_prefix_is_an_actual_write (amounts : List ℚ)
    (positive : ∀ q ∈ amounts, 0 < q) (within : amounts.sum ≤ 6) :
    Occurrence.Eligible replies loss (paidPrefix amounts) ∧
    (Ready (endAt Original.seed (born ++ paidPrefix amounts)) ∧
      ReviewAvailable (endAt Original.seed (born ++ paidPrefix amounts))) ∧
    (endAt Original.seed (born ++ paidPrefix amounts)).raw = Snapshot amounts.sum ∧
    ∃ balance : Balance, (Occurrence.reached replies loss (paidPrefix amounts)).stack.balances = [(loss, balance)] ∧
      balance.remaining = 6 - amounts.sum := by
  induction amounts using List.reverseRecOn with
  | nil =>
    have cut : endAt Original.seed (born ++ paidPrefix []) = Original.cut :=
      congrArg (endAt Original.seed) Original.exact_history.symm
    refine ⟨⟨⟨no_material_is_admitted _ _ _ _ the_native_head_leaves_no_material,
      Boundary.Actual.no_material_write_has_no_damage _ _ _ the_native_head_leaves_no_material⟩, trivial⟩,
      ?_, ?_, Original.balance, ?_, by simpa using Original.balance_six⟩
    · rw [cut]
      exact ⟨Original.ready, Original.review⟩
    · rw [cut, Original.cut_raw]
      norm_num [Snapshot]
    · change (Occurrence.reached replies loss ([] ++ [none])).stack.balances = _
      rw [reached_snoc_balances]
      have empty : Boundary.Actual.items (endAt Original.seed (born ++ [])) none = [] := by
        simpa only [List.append_nil] using the_native_head_leaves_no_material
      exact (a_native_accounting_input_keeps_the_entire_balance_table
        (Occurrence.reached replies loss []) replies empty).trans (opening_portfolio replies)
  | append_singleton earlier quantity ih =>
    have now : 0 < quantity := positive quantity (List.mem_append_right _ List.mem_cons_self)
    have exactSum : (earlier ++ [quantity]).sum = earlier.sum + quantity := by simp
    rw [exactSum] at within
    obtain ⟨eligible, ready, raw, old, portfolio, debt⟩ := ih
      (fun q listed => positive q (List.mem_append_left _ listed)) (by linarith only [now, within])
    let past := born ++ paidPrefix earlier
    have funded : quantity ≤ 113 - earlier.sum := by linarith only [within]
    have next := the_original_cut_after_an_installment past earlier.sum quantity raw ready.1 ready.2 now funded
    have checked := the_return_and_its_accounting_are_eligible past earlier.sum quantity raw ready.1 ready.2 now funded born
    have cap : quantity ≤ old.remaining := by rw [debt]; linarith only [within]
    have applied := the_installment_pays_the_original_row past earlier.sum quantity raw ready.1 ready.2 now funded
      (Occurrence.reached replies loss (paidPrefix earlier)) old portfolio (List.prefix_append _ _) cap
    refine ⟨?_, ?_, ?_, old.subtract quantity cap, ?_, ?_⟩
    · rw [paidPrefix_snoc]
      exact append_eligible eligible checked
    · rw [full_history_snoc]
      exact next.2
    · rw [full_history_snoc, exactSum]
      exact next.1
    · have suffixShape : paidPrefix (earlier ++ [quantity]) = (paidPrefix earlier ++ [payment quantity]) ++ [none] := by
        rw [paidPrefix_snoc, List.append_assoc]
        rfl
      have empty : Boundary.Actual.items
          (endAt Original.seed (born ++ (paidPrefix earlier ++ [payment quantity]))) none = [] := by
        simpa only [past, List.append_assoc] using
          accounting_has_no_items past earlier.sum quantity raw ready.1 ready.2 now funded
      calc
        _ = (Occurrence.reached replies loss ((paidPrefix earlier ++ [payment quantity]) ++ [none])).stack.balances :=
          congrArg (fun suffix => (Occurrence.reached replies loss suffix).stack.balances) suffixShape
        _ = (Occurrence.reached replies loss (paidPrefix earlier ++ [payment quantity])).stack.balances := by
          rw [reached_snoc_balances]
          exact a_native_accounting_input_keeps_the_entire_balance_table
            (Occurrence.reached replies loss (paidPrefix earlier ++ [payment quantity])) replies empty
        _ = _ := (reached_snoc_balances (paidPrefix earlier) (payment quantity)).trans applied
    · change old.remaining - quantity = _
      rw [debt, exactSum]
      ring

/-- Every positive rational partition of six clears the entire original
reparation portfolio at an actual ready and reviewable native successor. -/
theorem every_full_partition_clears_the_whole_account (amounts : List ℚ)
    (positive : ∀ q ∈ amounts, 0 < q) (full : amounts.sum = 6) :
    Occurrence.Eligible replies loss (paidPrefix amounts) ∧
    (Ready (endAt Original.seed (born ++ paidPrefix amounts)) ∧
      ReviewAvailable (endAt Original.seed (born ++ paidPrefix amounts))) ∧
    (endAt Original.seed (born ++ paidPrefix amounts)).raw = Original.snapshot 117 107 ∧
    ∀ row ∈ (Occurrence.reached replies loss (paidPrefix amounts)).stack.balances, row.2.remaining = 0 := by
  obtain ⟨eligible, ready, raw, balance, portfolio, exactDebt⟩ :=
    the_installment_prefix_is_an_actual_write amounts positive full.le
  refine ⟨eligible, ready, ?_, ?_⟩
  · rw [raw, full]
    norm_num [Snapshot]
  · intro row listed
    rw [portfolio] at listed
    rw [List.mem_singleton.mp listed]
    simp [exactDebt, full]

private theorem single_transfer :
    Occurrence.Eligible replies loss fullWord ∧
    (Ready (endAt Original.seed (born ++ fullWord)) ∧ ReviewAvailable (endAt Original.seed (born ++ fullWord))) ∧
    (endAt Original.seed (born ++ fullWord)).raw = Original.snapshot 117 107 ∧
    (∀ row ∈ (Occurrence.reached replies loss fullWord).stack.balances, row.2.remaining = 0) :=
  every_full_partition_clears_the_whole_account [6] (by simp) (by simp)

theorem fullWord_is_eligible : Occurrence.Eligible replies loss fullWord := single_transfer.1

theorem fullWord_is_ready :
    Ready (endAt Original.seed (born ++ fullWord)) ∧ ReviewAvailable (endAt Original.seed (born ++ fullWord)) :=
  single_transfer.2.1

theorem fullWord_raw : (endAt Original.seed (born ++ fullWord)).raw = Original.snapshot 117 107 :=
  single_transfer.2.2.1

theorem fullWord_clears_the_whole_account :
    ∀ row ∈ (Occurrence.reached replies loss fullWord).stack.balances, row.2.remaining = 0 := single_transfer.2.2.2

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment
