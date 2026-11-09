import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Posting.Allocation
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Guard
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Write

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation Reparation.Actual
open Reparation.Actual.Allocation (Position itemPositions)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {past : Reparation.Actual.Script Party Good Port Technology Instrument}

local notation "Proposal" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "ClaimKey" => Key Party Good

/-- Each actual ledger origin carries its literal birth prefix on the
recorded history. A later position needs no supplied age witness. -/
theorem every_actual_origin_birth_is_a_prefix (history : Reparation.Actual.Script Party Good Port Technology Instrument)
    (origin : Reparation.Actual.Occurrence seed community) (listed : origin ∈ originalLosses seed community history) :
    (Occurrence.history origin).IsPrefix history := by
  induction history using List.reverseRecOn with
  | nil =>
    rw [originalLosses, List.reverseRecOn_nil] at listed
    exact (List.not_mem_nil listed).elim
  | append_singleton prior input earlier =>
    rw [losses_snoc] at listed
    rcases List.mem_append.mp listed with old | now
    · exact (earlier old).trans (List.prefix_append _ _)
    · unfold openings at now
      obtain ⟨damage, _, rfl⟩ := List.mem_map.mp now
      exact List.prefix_rfl

theorem reached_rows_have_their_actual_birth_prefix (answers : ReceiptAnswers seed)
    (anchor : Reparation.Actual.Occurrence seed community) (suffix : Reparation.Actual.Script Party Good Port Technology Instrument)
    (row : Reparation.Actual.Occurrence seed community × Balance)
    (listed : row ∈ (Occurrence.reached answers anchor suffix).stack.balances) :
    (Occurrence.history row.1).IsPrefix (Occurrence.history anchor ++ suffix) := by
  have current := List.mem_map_of_mem (f := Prod.fst) listed
  rw [Occurrence.reached_origins] at current
  exact every_actual_origin_birth_is_a_prefix _ row.1 current

private theorem posted_rows_of_a_safe_input (state : State seed community past) (input : Proposal)
    (safe : Boundary.Actual.damages (endAt seed past) input community = []) :
    (posted state input).stack.balances = state.stack.balances := by
  have noOpening : openings seed community past input = [] := by
    unfold openings
    rw [safe]
    rfl
  rw [posted_balances, noOpening, List.map_nil, List.append_nil]

private theorem actual_position_rows (answers : ReceiptAnswers seed) (state : State seed community past)
    (input : Proposal) (site : Position seed past input) (positions : itemPositions past input = [site]) :
    (Settlement.writeTick answers state input).stack.balances =
      (Settlement.atPosition answers past input site (posted state input)).after.balances := by
  rw [Settlement.writeTick_balances, positions, Settlement.writePositions, Settlement.writePositions,
    Settlement.writePosition_balances]

private theorem no_other_offer_of_the_same_good (answers : ReceiptAnswers seed) (input : Proposal)
    (site : Position seed past input) (key : ClaimKey) (receipt : JointReceipt seed key)
    (issued : Settlement.jointOffer answers past input site key = some receipt)
    (other : ClaimKey) (sameGood : other.2.2 = key.2.2) (different : other ≠ key) :
    Settlement.jointOffer answers past input site other = none := by
  cases selected : Settlement.jointOffer answers past input site other with
  | none => rfl
  | some proof =>
    exact (different (Settlement.two_joint_offers_of_one_original_good_must_share_one_claim_key
      answers past input site other key proof receipt selected issued sameGood)).elim

private theorem the_original_position_demands_exactly_the_key_due (answers : ReceiptAnswers seed)
    (state : State seed community past) (input : Proposal) (site : Position seed past input)
    (key : ClaimKey) (receipt : JointReceipt seed key)
    (issued : Settlement.jointOffer answers past input site key = some receipt)
    (earlier : ∀ row ∈ state.stack.balances, row.1.key = key → (Occurrence.history row.1).IsPrefix past) :
    Settlement.demand (Settlement.jointOffer answers past input site) key.2.2 state.stack.balances =
      dueFor key state.stack.balances := by
  apply demand_eq_key_due _ key _
  · intro row listed same
    have offered : ∃ received : JointReceipt seed row.1.key,
        Settlement.jointOffer answers past input site row.1.key = some received := by
      rw [same]
      exact ⟨receipt, issued⟩
    obtain ⟨received, actual⟩ := offered
    refine ⟨received, actual, ?_⟩
    obtain ⟨_, _, _, rfl⟩ := Settlement.the_joint_offer_is_issued_at_the_exact_position _ _ _ _ _ _ actual
    exact Or.inl (earlier row listed same)
  · exact no_other_offer_of_the_same_good answers input site key receipt issued

/-- The one original position is allocated by the existing writer. Its
selected key drops by the exact amount available, and no origin is removed. -/
theorem writeTick_pays_the_original_key_exactly (answers : ReceiptAnswers seed) (state : State seed community past)
    (input : Proposal) (site : Position seed past input) (key : ClaimKey) (receipt : JointReceipt seed key)
    (positions : itemPositions past input = [site])
    (issued : Settlement.jointOffer answers past input site key = some receipt)
    (safe : Boundary.Actual.damages (endAt seed past) input community = [])
    (earlier : ∀ row ∈ state.stack.balances, row.1.key = key → (Occurrence.history row.1).IsPrefix past) :
    let after := Settlement.writeTick answers state input
    after.stack.balances.map Prod.fst = state.stack.balances.map Prod.fst ∧
      dueFor key after.stack.balances = dueFor key state.stack.balances -
        min (Settlement.limitAt past input site key.2.2) (dueFor key state.stack.balances) := by
  let postedState := posted state input
  let plan := Settlement.atPosition answers past input site postedState
  have filed : postedState.stack.balances = state.stack.balances := posted_rows_of_a_safe_input state input safe
  have wrote := actual_position_rows answers state input site positions
  change (Settlement.writeTick answers state input).stack.balances = plan.after.balances at wrote
  dsimp only
  rw [wrote]
  refine ⟨plan.move.keeps_origins.trans (congrArg (List.map Prod.fst) filed), ?_⟩
  have demand : Settlement.demand (Settlement.jointOffer answers past input site) key.2.2 postedState.stack.balances =
      dueFor key state.stack.balances := by
    rw [filed]
    exact the_original_position_demands_exactly_the_key_due answers state input site key receipt issued earlier
  have charged := plan.tight key.2.2
  change Settlement.limitAt past input site key.2.2 - (plan.left.balance key.2.2).remaining =
    min (Settlement.limitAt past input site key.2.2)
      (Settlement.demand (Settlement.jointOffer answers past input site) key.2.2 postedState.stack.balances) at charged
  rw [demand] at charged
  have debit := the_unique_key_of_a_good_consumes_its_entire_booked_debit
    (Settlement.jointOffer answers past input site) (Settlement.limitAt past input site)
    (fun k r selected => (Settlement.the_original_limit_is_the_selected_quantity answers past input site k r selected).le)
    postedState.stack (Settlement.Available.full (Settlement.limitAt_nonnegative past input site)) key
    (no_other_offer_of_the_same_good answers input site key receipt issued)
  change dueFor key plan.after.balances +
    (Settlement.limitAt past input site key.2.2 - (plan.left.balance key.2.2).remaining) =
      dueFor key postedState.stack.balances at debit
  rw [charged, filed] at debit
  linarith only [debit]

theorem writeTick_keeps_rows_without_receipt_or_delivery (answers : ReceiptAnswers seed) (state : State seed community past)
    (input : Proposal) (site : Position seed past input) (positions : itemPositions past input = [site])
    (safe : Boundary.Actual.damages (endAt seed past) input community = [])
    (read : ClaimKey → Prop) [DecidablePred read]
    (closed : ∀ key, read key → Settlement.jointOffer answers past input site key = none ∨
      Settlement.limitAt past input site key.2.2 = 0) :
    (Settlement.writeTick answers state input).stack.balances.filter (fun row => decide (read row.1.key)) =
      state.stack.balances.filter (fun row => decide (read row.1.key)) := by
  rw [actual_position_rows answers state input site positions]
  let postedState := posted state input
  have kept := allocation_keeps_every_unfunded_row
    (Settlement.jointOffer answers past input site) (Settlement.limitAt past input site)
    (fun k r issued => (Settlement.the_original_limit_is_the_selected_quantity answers past input site k r issued).le)
    postedState.stack (Settlement.Available.full (Settlement.limitAt_nonnegative past input site)) read closed
  exact kept.trans (congrArg (fun rows => rows.filter (fun row => decide (read row.1.key)))
    (posted_rows_of_a_safe_input state input safe))

theorem writeTick_clears_every_original_row_of_the_funded_key (answers : ReceiptAnswers seed)
    (state : State seed community past) (input : Proposal) (site : Position seed past input)
    (key : ClaimKey) (receipt : JointReceipt seed key) (positions : itemPositions past input = [site])
    (issued : Settlement.jointOffer answers past input site key = some receipt)
    (safe : Boundary.Actual.damages (endAt seed past) input community = [])
    (earlier : ∀ row ∈ state.stack.balances, row.1.key = key → (Occurrence.history row.1).IsPrefix past)
    (funded : dueFor key state.stack.balances ≤ Settlement.limitAt past input site key.2.2) :
    ∀ row ∈ (Settlement.writeTick answers state input).stack.balances, row.1.key = key → row.2.remaining = 0 := by
  have exactDue := (writeTick_pays_the_original_key_exactly answers state input site key receipt positions issued safe earlier).2
  rw [min_eq_right funded, sub_self] at exactDue
  exact every_original_row_is_cleared_when_its_key_has_zero_due key _ exactDue

private theorem another_key_has_no_receipt_or_no_delivery (answers : ReceiptAnswers seed) (input : Proposal)
    (site : Position seed past input) (key : ClaimKey) (receipt : JointReceipt seed key)
    (issued : Settlement.jointOffer answers past input site key = some receipt)
    (oneGood : ∀ good, good ≠ key.2.2 → Settlement.limitAt past input site good = 0)
    (other : ClaimKey) (different : other ≠ key) :
    Settlement.jointOffer answers past input site other = none ∨ Settlement.limitAt past input site other.2.2 = 0 := by
  by_cases sameGood : other.2.2 = key.2.2
  · exact Or.inl (no_other_offer_of_the_same_good answers input site key receipt issued other sameGood different)
  · exact Or.inr (oneGood other.2.2 sameGood)

/-- A single-good delivery keeps the exact balance and relative order of
every old row outside its authorized key. -/
theorem writeTick_keeps_every_other_original_row_of_a_single_good_delivery (answers : ReceiptAnswers seed)
    (state : State seed community past) (input : Proposal) (site : Position seed past input)
    (key : ClaimKey) (receipt : JointReceipt seed key) (positions : itemPositions past input = [site])
    (issued : Settlement.jointOffer answers past input site key = some receipt)
    (safe : Boundary.Actual.damages (endAt seed past) input community = [])
    (oneGood : ∀ good, good ≠ key.2.2 → Settlement.limitAt past input site good = 0) :
    (Settlement.writeTick answers state input).stack.balances.filter (fun row => decide (row.1.key ≠ key)) =
      state.stack.balances.filter (fun row => decide (row.1.key ≠ key)) :=
  writeTick_keeps_rows_without_receipt_or_delivery answers state input site positions safe (· ≠ key)
    (another_key_has_no_receipt_or_no_delivery answers input site key receipt issued oneGood)

/-- A funded single-good delivery closes its key. Every other key keeps its
exact original total, on the same ordered list of origin addresses. -/
theorem writeTick_clears_key_and_preserves_all_other_due (answers : ReceiptAnswers seed)
    (state : State seed community past) (input : Proposal) (site : Position seed past input)
    (key : ClaimKey) (receipt : JointReceipt seed key) (positions : itemPositions past input = [site])
    (issued : Settlement.jointOffer answers past input site key = some receipt)
    (safe : Boundary.Actual.damages (endAt seed past) input community = [])
    (earlier : ∀ row ∈ state.stack.balances, row.1.key = key → (Occurrence.history row.1).IsPrefix past)
    (funded : dueFor key state.stack.balances ≤ Settlement.limitAt past input site key.2.2)
    (oneGood : ∀ good, good ≠ key.2.2 → Settlement.limitAt past input site good = 0) :
    let after := Settlement.writeTick answers state input
    after.stack.balances.map Prod.fst = state.stack.balances.map Prod.fst ∧
      ∀ other, dueFor other after.stack.balances = if other = key then 0 else dueFor other state.stack.balances := by
  have exactWrite := writeTick_pays_the_original_key_exactly answers state input site key receipt positions issued safe earlier
  refine ⟨exactWrite.1, fun other => ?_⟩
  by_cases same : other = key
  · subst other
    rw [if_pos rfl, exactWrite.2, min_eq_right funded, sub_self]
  · have kept := writeTick_keeps_rows_without_receipt_or_delivery answers state input site positions safe (· = other)
      (fun read equal => another_key_has_no_receipt_or_no_delivery answers input site key receipt issued oneGood read
        (equal.symm ▸ same))
    simp only [if_neg same, dueFor_is_the_sum_of_the_original_rows_of_the_key, kept]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
