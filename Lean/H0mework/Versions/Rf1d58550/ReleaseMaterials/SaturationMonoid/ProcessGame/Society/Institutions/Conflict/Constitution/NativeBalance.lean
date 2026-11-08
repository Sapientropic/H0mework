import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ReviewDebt
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.RecordedBalance
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Defence
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Advance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "inventory" => Quantities.Execution.inventory
local notation "endAt" => Quantities.Execution.endAt
local notation "script" => Quantities.Execution.primitiveScript

/-- Read the original reparation across any actual clock-bearing continuation.
The remaining amount comes from the original inventory of that continuation. -/
abbrev nativeDue
    {source : Root.Cut Party Good Port Technology Instrument}
    {word : RawEvent Party Good Port Technology Instrument} {community : Party → Community}
    (attack : Boundary.AggressionAt source word community) (history : Script) : ℚ :=
  Reparation.recordedDue source word history community (debtAddress attack)

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem no_transfer_has_zero_credit
    (law : RawLaw Party Good Port Technology Instrument) (item : ExecutionItem Party Good Port Technology Instrument)
    (key : Reparation.Key Party Good)
    (none : ∀ debtor creditor goods, item.request.operation ≠ .transfer debtor creditor goods) :
    Reparation.receiptCredit law item key = 0 := by
  unfold Reparation.receiptCredit
  split
  · cases observed : item.request.operation
    case transfer debtor creditor goods => exact (none debtor creditor goods observed).elim
    all_goals rfl
  · rfl

/-- The aggressor's entire actual suffix, with arbitrary epoch and clock
changes, cannot consume the victim's independent receipt. -/
theorem a_unilateral_original_suffix_preserves_the_native_remainder
    {source : Root.Cut Party Good Port Technology Instrument}
    {word : RawEvent Party Good Port Technology Instrument} {community : Party → Community}
    (attack : Boundary.AggressionAt source word community) (past suffix : Script)
    (unilateral : ∀ item ∈ inventory (endAt attack.after past) suffix,
      community item.request.signer = community attack.attacker) :
    nativeDue attack (past ++ suffix) = nativeDue attack past := by
  exact Reparation.recordedDue_after_a_unilateral_suffix (claimFor attack) past suffix unilateral

variable [DecidableEq Technology]

/-- The real clock may cross many epochs. Their existing receipt inventory
stays in every original balance, and the two review payments add no delivery credit. -/
theorem a_dual_review_preserves_every_original_reparation
    {source : Root.Cut Party Good Port (State Party Technology) Instrument}
    {word tail : RawEvent Party Good Port (State Party Technology) Instrument}
    {community : Party → Community} {base : RawLaw Party Good Port Technology Instrument}
    {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
    {first second : Party} {good : Good}
    (history : List (Option (Compile.RawInput Party Good Port (State Party Technology) Instrument)))
    (review : Emergency.ReviewPaid base scope (endAt (Root.terminal source word) history) first second good tail)
    (key : Reparation.Key Party Good) :
    let cut := endAt (Root.terminal source word) history
    let reviews := Emergency.reviewWord base scope cut first second tail
    Reparation.recordedDue source word (history ++ script reviews) community key =
      Reparation.recordedDue source word history community key := by
  let cut := endAt (Root.terminal source word) history
  let reviews := Emergency.reviewWord base scope cut first second tail
  change Reparation.recordedDue source word (history ++ script reviews) community key = _
  apply Reparation.recordedDue_append_without_receipts
  intro item occurrence
  change item ∈ inventory cut (script reviews) at occurrence
  rw [Reparation.original_inventory review.whole] at occurrence
  obtain ⟨raw, listed, same⟩ := List.mem_map.mp occurrence
  have rawRequest : raw.request ∈ reviews := by
    change raw ∈ (cut.native.input.law.execute cut.raw 0 reviews).items at listed
    rw [← cut.native.input.law.inventory_requests_exact cut.raw 0 reviews]
    exact List.mem_map_of_mem listed
  rw [← same]
  exact no_transfer_has_zero_credit _ _ _ (Emergency.review_word_has_no_transfer base scope
    cut first second review.localTail raw.request rawRequest)

theorem attack_clock_history_and_dual_review_write_the_same_ledger
    {source : Root.Cut Party Good Port (State Party Technology) Instrument}
    {word tail : RawEvent Party Good Port (State Party Technology) Instrument}
    {community : Party → Community} {base : RawLaw Party Good Port Technology Instrument}
    {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
    {first second : Party} {good : Good}
    (attack : Boundary.AggressionAt source word community)
    (history : List (Option (Compile.RawInput Party Good Port (State Party Technology) Instrument)))
    (elapsed : Quantities.Settled attack.after history)
    (review : Emergency.ReviewPaid base scope (endAt attack.after history) first second good tail) :
    let cut := endAt attack.after history
    let reviews := Emergency.reviewWord base scope cut first second tail
    Quantities.Settled source (script word ++ (history ++ script reviews)) ∧
      nativeDue attack (history ++ script reviews) = nativeDue attack history ∧
      endAt source (script word ++ (history ++ script reviews)) = Root.terminal cut reviews := by
  dsimp only
  exact ⟨Quantities.Due.Production.append_settled source _ _ attack.paid.whole
      (Quantities.Due.Production.append_settled attack.after history _ elapsed review.whole.whole),
    a_dual_review_preserves_every_original_reparation (source := source) (word := word)
      (community := community) history review (debtAddress attack),
    by simp only [Quantities.Execution.endAt_append, Root.terminal, Boundary.AggressionAt.after]⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution
