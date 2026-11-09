import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Batch
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Repeated.Funding
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalService

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.OriginalBatch

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_input)
open Conflict.Consumers.Evolving (R compact sourceInput)
open Reparation.Actual (Balance originalLosses)
open Reparation.Actual.Allocation (Position originalItem)
open OriginalPayment (replies Snapshot)
open OriginalPayment.Repeated (indexedLoss birth accounted fundingPrefix fundedPast fundedState fundedCut
  funding_is_actual_at_every_count actual_accounted_cut the_funded_cut_keeps_the_exact_total_due)

noncomputable section

private abbrev claim : Reparation.Key Bool Bool := (false, true, false)

private theorem each_original_key_is_the_levy_key (n : Nat) (key : Reparation.Key Bool Bool)
    (listed : key ∈ originalKeys (indexedLoss n)) : key = claim := by
  have actual := eligible_prefix_has_the_original_keys (indexedLoss n) replies (fundingPrefix 0)
    (funding_is_actual_at_every_count n 0).1
  rw [← actual] at listed
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp listed)
  exact ((the_funded_cut_keeps_the_exact_total_due n 0).1 row present).1

private theorem lawful_original_delivery (past : Original.Word) (quantity : ℚ)
    (positive : 0 < quantity) (funded : quantity ≤ (endAt Original.seed past).raw.stock true false)
    (policy : (endAt Original.seed past).native.input.law.operationAllowed (endAt Original.seed past).raw
      (paymentRequest false claim quantity) = true)
    (port : (endAt Original.seed past).native.input.law.allowed (endAt Original.seed past).raw.technology
      ((endAt Original.seed past).native.input.law.stockPort (endAt Original.seed past).raw.technology true false) true = true) :
    (endAt Original.seed past).native.input.law.Valid (endAt Original.seed past).raw
      (paymentRequest false claim quantity) := by
  unfold RawLaw.Valid
  refine ⟨⟨trivial, policy⟩, ?_, trivial, ?_, ?_, ?_⟩
  · intro gate listed
    change gate ∈ [(endAt Original.seed past).native.input.law.stockPort (endAt Original.seed past).raw.technology true false]
      at listed
    rw [List.mem_singleton.mp listed]
    exact Or.inl port
  · intro entry listed
    change entry ∈ [((true, false), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    exact positive.le
  · intro entry listed
    change entry ∈ [((false, false), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    exact positive.le
  · intro entry listed
    change entry ∈ [((true, false), quantity)] at listed
    rw [List.mem_singleton.mp listed]
    change flowAt (locate true [(false, quantity)]) true false ≤ _
    rw [singleton_delivery_flow, if_pos rfl]
    exact funded

/-- Both original people answer on the actual native item for the computed
quantity. The channel inherits the compact source's existing authority. -/
def originalChannels (n : Nat) : IndependentReceiptChannels (indexedLoss n) replies := by
  refine ⟨fun _ => false, ?_⟩
  intro front key _ ready named
  rw [each_original_key_is_the_levy_key n key named]
  let amount := dueFor claim (prefixRows (indexedLoss n) replies front)
  let past := birth n ++ front
  dsimp only
  intro positive enough
  have source : (endAt Original.seed past).native.input = compact := (endAt_input _ _).trans sourceInput
  have policy : (endAt Original.seed past).native.input.law.operationAllowed (endAt Original.seed past).raw
      (paymentRequest false claim amount) = true := by
    rw [source]
    rfl
  have port : (endAt Original.seed past).native.input.law.allowed (endAt Original.seed past).raw.technology
      ((endAt Original.seed past).native.input.law.stockPort (endAt Original.seed past).raw.technology true false) true = true := by
    rw [source]
    rfl
  have legal := lawful_original_delivery past amount positive enough policy port
  have items := the_delivery_writes_one_original_item ready.1 ready.2 legal
  have personal (site : Position Original.seed past (payment false claim amount)) (person : Bool) :
      replies past (payment false claim amount) site person = true := by
    have present : originalItem Original.seed past (payment false claim amount) site ∈
        Boundary.Actual.items (endAt Original.seed past) (payment false claim amount) := List.getElem_mem _
    rw [items] at present
    unfold replies
    rw [List.mem_singleton.mp present]
    simpa [paymentRequest, positive]
  exact ⟨by decide, policy, port, fun site => personal site true, fun site => personal site false⟩

/-- Keep exactly the original stock at the accounted cut available to its
bearers. The next production lots finance the restitution budget. -/
def originalReserve (n : Nat) : Bool → Bool → ℚ := (endAt Original.seed (accounted n)).raw.stock

private theorem reserve_nonnegative (n : Nat) (person good : Bool) : 0 ≤ originalReserve n person good := by
  unfold originalReserve
  rw [(actual_accounted_cut n).1]
  cases person <;> cases good <;> norm_num [Snapshot, Original.snapshot]

private theorem cell_due_exact (n count : Nat) (cell : MaterialCell Bool Bool) :
    cellDue (fundedState n count).stack.balances cell = if cell = (true, false) then 6 * ((n : ℚ) + 1) else 0 := by
  let rows := (fundedState n count).stack.balances
  have actual := the_funded_cut_keeps_the_exact_total_due n count
  have atKey (row : Reparation.Actual.Occurrence Original.seed Original.community × Balance)
      (listed : row ∈ rows) : row.1.key = claim := (actual.1 row listed).1
  by_cases same : cell = (true, false)
  · subst cell
    rw [if_pos rfl, ← actual.2]
    unfold cellDue Settlement.outstanding
    apply congrArg List.sum
    apply List.map_congr_left
    intro row listed
    rw [atKey row listed]
    rfl
  · rw [if_neg same]
    unfold cellDue
    have zero : (rows.map fun row => if payerCell row.1.key = cell then row.2.remaining else 0) =
        rows.map (fun _ => 0) := by
      apply List.map_congr_left
      intro row listed
      rw [atKey row listed, if_neg (Ne.symm same)]
    rw [zero]
    simp

private def periodGain (cell : MaterialCell Bool Bool) : ℚ :=
  if cell = (true, false) then 18 else 0

def originalFundingCycles (n : Nat) : Nat :=
  fundingCycles (fundedState n 0).stack.balances (fun _ => 0) periodGain

/-- The source-calculated count is exactly the first sufficient actual
production cut when the original reserve is protected. -/
theorem the_actual_funding_cut_is_sufficient_iff (n count : Nat) :
    CoversPortfolio (indexedLoss n) replies (originalReserve n) (fundingPrefix count) ↔
      originalFundingCycles n ≤ count := by
  have gain_nonnegative (cell : MaterialCell Bool Bool) : 0 ≤ periodGain cell := by
    unfold periodGain
    split <;> norm_num
  have grows (cell : MaterialCell Bool Bool) :
      0 < cellDue (fundedState n 0).stack.balances cell → 0 < periodGain cell := by
    rw [cell_due_exact]
    by_cases owing : cell = (true, false) <;> simp [periodGain, owing]
  rw [originalFundingCycles, fundingCycles_le_iff_funds _ _ _ (fun _ => le_rfl) gain_nonnegative grows]
  have stock (person good : Bool) : (fundedCut n count).raw.stock person good =
      originalReserve n person good + (count : ℚ) * periodGain (person, good) := by
    rw [(funding_is_actual_at_every_count n count).2.1, originalReserve, (actual_accounted_cut n).1]
    cases person <;> cases good <;> norm_num [periodGain, Snapshot, Original.snapshot]
    ring
  constructor
  · intro covered cell
    rcases cell with ⟨person, good⟩
    have actual := covered person good
    change originalReserve n person good + cellDue (fundedState n count).stack.balances (person, good) ≤
      (fundedCut n count).raw.stock person good at actual
    rw [stock, add_le_add_iff_left, cell_due_exact] at actual
    simpa only [zero_add, cell_due_exact] using actual
  · intro funded person good
    have exactCell := funded (person, good)
    rw [cell_due_exact, zero_add] at exactCell
    change originalReserve n person good + cellDue (fundedState n count).stack.balances (person, good) ≤
      (fundedCut n count).raw.stock person good
    rw [stock, add_le_add_iff_left, cell_due_exact]
    exact exactCell

/-- The generic batch generates the settlement suffix from the actual
funded history of arbitrary finite repeated assaults. -/
def originalFundedBatch (n : Nat) :
    ClearedPrefix (indexedLoss n) replies (originalReserve n) (fundingPrefix (originalFundingCycles n)) :=
  let funded := funding_is_actual_at_every_count n (originalFundingCycles n)
  clearFundedPortfolio (indexedLoss n) replies (originalChannels n) (originalReserve n) (reserve_nonnegative n)
    (fundingPrefix (originalFundingCycles n)) funded.1 funded.2.2.1
    ((the_actual_funding_cut_is_sufficient_iff n _).mpr le_rfl)

theorem the_generated_batch_keeps_the_complete_origin_inventory (n : Nat) :
    let settled := originalFundedBatch n
    (prefixRows (indexedLoss n) replies settled.word).map Prod.fst =
      originalLosses Original.seed Original.community (birth n) := by
  dsimp only
  rw [Occurrence.reached_origins]
  exact Occurrence.eligible_preserves_the_literal_original_loss_inventory Original.community replies (birth n) (birth n)
    _ (originalFundedBatch n).eligible

private theorem original_stock_survives_the_batch (n : Nat) :
    TerminalPeace.Supply.Stocked (prefixRaw (indexedLoss n) (originalFundedBatch n).word) := by
  intro person
  have material : 18 ≤ originalReserve n person false := by
    unfold originalReserve
    rw [(actual_accounted_cut n).1]
    cases person <;> norm_num [Snapshot, Original.snapshot]
  exact ⟨material.trans ((originalFundedBatch n).reserved person false),
    (reserve_nonnegative n person true).trans ((originalFundedBatch n).reserved person true)⟩

/-- The generated batch supplies a live candidate to the common optimizer.
Both reports name the very same paid realization of a whole-zero portfolio. -/
theorem the_native_batch_attains_the_shared_whole_terminal (n : Nat) :
    let occurrence := indexedLoss n
    let batch := originalFundedBatch n
    let offers := OriginalService.menuAt (birth n ++ batch.word) (fun _ => true)
    ∃ word run minimum shortest all fewest,
      source_generated_terminal_peace occurrence replies (fun _ => True) offers .wholePortfolio =
        .attained word run minimum shortest ∧
      compileWhole occurrence replies (fun _ => True) offers = .paid word run all fewest ∧
      word.length ≤ batch.word.length := by
  let occurrence := indexedLoss n
  let batch := originalFundedBatch n
  let offers := OriginalService.menuAt (birth n ++ batch.word) (fun _ => true)
  let choice := OriginalService.choiceAt (birth n ++ batch.word) (fun _ => true)
  have approved := (OriginalService.approval_reads_both_independent_replies occurrence batch.word _).mpr (fun _ => rfl)
  obtain ⟨pilot, starts, live⟩ := OriginalService.the_original_carriers_fund_the_pilot occurrence batch.word
    (fun _ => true) _ (original_stock_survives_the_batch n) batch.ready approved
  have viable : ViableEntry occurrence replies (fun _ => True) batch.word offers :=
    ⟨⟨Or.inr trivial, batch.eligible⟩, batch.ready, choice, approved, pilot, starts, live⟩
  obtain ⟨word, run, minimum, shortest, all, fewest, attained, paid⟩ :=
    both_portfolio_reports_select_the_same_whole_terminal occurrence replies (fun _ => True) offers
      ⟨batch.word, viable, batch.cleared⟩
  exact ⟨word, run, minimum, shortest, all, fewest, attained, paid, fewest batch.word viable batch.cleared⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.OriginalBatch
