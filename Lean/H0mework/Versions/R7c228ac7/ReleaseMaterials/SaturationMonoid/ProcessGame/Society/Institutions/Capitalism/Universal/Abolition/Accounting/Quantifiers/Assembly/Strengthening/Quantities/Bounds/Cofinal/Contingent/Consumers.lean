import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent.Slices
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Expiry
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window.Consumers

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent.Consumers

open Abolition.Root Abolition.Root.Registered Execution
open Recovery.Robust.Recurring (run)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers
  (lifeSource firstPaidPeriod the_original_full_period_pays_life_and_finishes_its_native_work)
open Clock.Window.Consumers (closesAtStart a_real_material_period_can_commit_after_its_original_service_cutoff)

noncomputable section

local notation "C" => Evolving.Epoch.Current (Party := Bool) (Good := Bool) (Port := Bool)
  (Technology := Unit) (Instrument := Unit)
local notation "Script" => List (Option (Compile.RawInput Bool Bool Bool Unit Unit))

def exposure (_stage : Nat) (current : C) (commit : Bool) : Script :=
  if commit then periodAndAccounting current Innovation.Contribution.Pricing.Consumers.Actual.lifeWord else []

def observe (_stage : Nat) (_current : C) : Unit := ()

def choose (_stage : Nat) (current : C) : Bool := decide (current.raw.clock ≤ closesAtStart.deadline)

def inspect (_stage : Nat) (current : C) (word : Script) : Option (Clock.Window.Shortage current closesAtStart word) :=
  Clock.Window.inspect current closesAtStart word

private theorem the_entire_paid_period_is_late :
    ∀ receipt ∈ timedInventory lifeSource firstPaidPeriod, closesAtStart.deadline < receipt.2 := by
  intro receipt present
  obtain ⟨index, exactReceipt⟩ := List.mem_iff_get.mp present
  let ordinal : Fin (inventory lifeSource firstPaidPeriod).length :=
    ⟨index.val, by
      rw [← timedInventory_is_the_original_inventory, List.length_map]
      exact index.isLt⟩
  have same : timedAt lifeSource firstPaidPeriod ordinal = receipt := exactReceipt
  rw [← same]
  exact a_real_material_period_can_commit_after_its_original_service_cutoff.2.1 ordinal

private theorem actual_period_moves_past_the_window :
    closesAtStart.deadline < (endAt lifeSource firstPaidPeriod).raw.clock := by
  have hour := the_original_full_period_pays_life_and_finishes_its_native_work.2
  unfold elapsed at hour
  change lifeSource.raw.clock < _
  linarith

/-- The reacting input commits real production at the first original cut.
No possible later programme can move its receipts or repairs into the
closed window. The source retains the paid period and original shortage. -/
theorem an_adaptive_original_input_blocks_every_committed_policy_at_its_real_cut
    (policy : Nat → Unit → Script) :
    Settled lifeSource firstPaidPeriod ∧
      let events := emitted lifeSource exposure observe policy choose
      let branch := run exposure observe policy events
      (∃ issue, inspect 0 (stageAt lifeSource branch 0) (stageBody lifeSource branch 0) = some issue) ∧
      Failure lifeSource exposure observe inspect policy ∧
      ¬ Paid lifeSource exposure observe inspect policy := by
  let events := emitted lifeSource exposure observe policy choose
  let branch := run exposure observe policy events
  have actualFirst : stageBody lifeSource branch 0 = firstPaidPeriod ++ policy 0 () := by
    have commits : choose 0 lifeSource = true := by
      unfold choose
      exact decide_eq_true (le_refl _)
    unfold branch events stageBody run emitted exposure
    change (if choose 0 lifeSource then firstPaidPeriod else []) ++ policy 0 () = _
    rw [commits]
    rfl
  have late := Clock.Window.later_actions_cannot_backdate_an_original_missed_service lifeSource closesAtStart
    firstPaidPeriod (policy 0 ()) actual_period_moves_past_the_window the_entire_paid_period_is_late
  have fails : ¬ Clock.Window.FullyServed (stageAt lifeSource branch 0) closesAtStart (stageBody lifeSource branch 0) := by
    rw [actualFirst]
    exact late.refutes
  have issue : ∃ original, inspect 0 (stageAt lifeSource branch 0) (stageBody lifeSource branch 0) = some original := by
    cases found : inspect 0 (stageAt lifeSource branch 0) (stageBody lifeSource branch 0) with
    | none =>
      exact (fails ((Clock.Window.passes_iff_every_original_service_commits_in_time _ _ _).mp found)).elim
    | some original => exact ⟨original, rfl⟩
  have failure : Failure lifeSource exposure observe inspect policy :=
    .branch events (.requirement 0 issue) fun stage => record lifeSource (stageScript lifeSource branch stage)
  exact ⟨the_original_full_period_pays_life_and_finishes_its_native_work.1, issue, failure, failure_refutes failure⟩

private def requiredWindow (_stage : Nat) (_current : C) (word : Script) (_ : Unit) :
    Option (Slice word.length) :=
  some ⟨0, word.length, by simp⟩

private def windowInquiry (stage : Nat) (_ : Unit) (current : C) (word : Script) :=
  inspect stage current word

private def completionTime (_stage : Nat) (_ : Unit) (current : C) (word : Script) : EReal :=
  ((((endAt current word).raw.clock : ℚ) : ℝ) : EReal)

private theorem the_whole_slice_uses_the_original_window (stage : Nat) (current : C) (word : Script)
    (slice : Slice word.length) (located : requiredWindow stage current word () = some slice)
    (clear : windowInquiry stage () (slice.current current word) (slice.body word) = none) :
    inspect stage current word = none := by
  change some ⟨0, word.length, _⟩ = some slice at located
  have exactSlice := Option.some.inj located
  subst slice
  change inspect stage current ((word.drop 0).take word.length) = none at clear
  have exactBody : (word.drop 0).take word.length = word := by simp
  exact (congrArg (fun body => inspect stage current body = none) exactBody).mp clear

theorem no_amount_profile_can_hide_the_missed_original_window :
    values lifeSource exposure observe (Slices.inspectStage requiredWindow windowInquiry)
      (Slices.readStage requiredWindow id completionTime) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro profile present
  obtain ⟨policy, _, _, _, paid⟩ :=
    (Slices.the_complete_contingent_domain_uses_only_original_quantities_at_paid_cuts _ _ _ _ _ _ _ _).mp present
  let events := emitted lifeSource exposure observe policy choose
  let branch := run exposure observe policy events
  obtain ⟨slice, located, clear, _, _⟩ := (paid events 0).2.2.2 ()
  have inTime := the_whole_slice_uses_the_original_window 0 (stageAt lifeSource branch 0)
    (stageBody lifeSource branch 0) slice located clear
  obtain ⟨issue, found⟩ := (an_adaptive_original_input_blocks_every_committed_policy_at_its_real_cut policy).2.1
  change inspect 0 (stageAt lifeSource branch 0) (stageBody lifeSource branch 0) = some issue at found
  rw [inTime] at found
  cases found

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent.Consumers
