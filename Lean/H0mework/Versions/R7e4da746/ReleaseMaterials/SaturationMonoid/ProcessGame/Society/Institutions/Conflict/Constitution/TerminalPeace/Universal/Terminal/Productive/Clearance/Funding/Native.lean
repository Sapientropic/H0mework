import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Eligibility
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PaidPeriod

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Funding

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Quantities.Execution
open Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Conflict.Root.Cut Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "RawWord" => RawEvent Party Good Port Technology Instrument

variable {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

theorem eligible_append (answers : ReceiptAnswers seed) (anchor past front tail : Word)
    (first : Occurrence.EligibleFrom community answers anchor past front)
    (second : Occurrence.EligibleFrom community answers anchor (past ++ front) tail) :
    Occurrence.EligibleFrom community answers anchor past (front ++ tail) := by
  induction front generalizing past with
  | nil => simpa only [List.nil_append, List.append_nil] using second
  | cons input rest earlier =>
    refine ⟨first.1, earlier (past ++ [input]) first.2 ?_⟩
    rwa [List.append_assoc]

/-- Pure accounting visits have no material position to debit or sign. -/
theorem empty_inventory_is_eligible (answers : ReceiptAnswers seed) (anchor past word : Word)
    (empty : inventory (endAt seed past) word = []) :
    Occurrence.EligibleFrom community answers anchor past word := by
  induction word generalizing past with
  | nil => trivial
  | cons input tail earlier =>
    change inventory (endAt seed past) ([input] ++ tail) = [] at empty
    rw [inventory_append] at empty
    have parts := List.append_eq_nil_iff.mp empty
    refine ⟨⟨ExposureGuard.no_material_is_admitted _ _ _ _ parts.1,
      Boundary.Actual.no_material_write_has_no_damage _ _ _ parts.1⟩, earlier _ ?_⟩
    rw [endAt_append]
    exact parts.2

private theorem pending_keeps_control (source : C) (pending : Quantities.Pending source) :
    (next source none).control = source.control := by
  change Public.Inquiry.HasWork source.native.frame source.native.actual.actual at pending
  change source.advance.control = source.control
  unfold Evolving.Epoch.Current.advance
  rw [dif_pos pending]
  split
  · exact source.native_birth_keeps_the_same_source_phase _
  · exact source.the_unconsumed_source_phase_is_not_reset_by_ordinary_accounting

private theorem native_payments_keep_control (source : C) (count : Nat)
    (within : count ≤ remainingNative source) :
    (endAt source (nativePayments count)).control = source.control := by
  induction count generalizing source with
  | zero => rfl
  | succ count earlier =>
    have pending := (pending_iff_positive_original_positions source).mpr (by omega)
    have spent := a_native_payment_spends_one_original_position source pending
    exact (earlier (next source none) (by omega)).trans (pending_keeps_control source pending)

/-- Drain the actual native mass and preserve the installed review coordinate. -/
theorem drain_keeps_review (source : C) (review : ReviewAvailable source) :
    ReviewAvailable (endAt source (drain source)) := by
  unfold ReviewAvailable drain
  rw [native_payments_keep_control source (remainingNative source) le_rfl]
  exact review

private theorem physical_period_keeps_review (source : C) (word : RawWord)
    (ready : Ready source) (review : ReviewAvailable source) :
    ReviewAvailable (next source (some (.execute word))) := by
  let queried := query source (some (.execute word))
  have empty : ¬ Public.Inquiry.HasWork queried.native.frame queried.native.actual.actual := ready
  have control : queried.control = source.control :=
    (source.requery_keeps_control_and_complete_account _).1
  have command : queried.proposal = .execute word := rfl
  have same : (next source (some (.execute word))).control.review = source.control.review := by
    change queried.advance.control.review = _
    rw [Evolving.Epoch.Current.advance_eq_epoch queried empty,
      Evolving.Epoch.Transition.next_reads_the_written_control queried empty]
    unfold Evolving.Epoch.Current.afterControl Evolving.Epoch.Current.choice
    rw [control, command]
    unfold Evolving.Epoch.select
    split
    · simp only [Evolving.Epoch.Selection.controlAfter, Evolving.Epoch.Dispatch.compile,
        Evolving.Epoch.Dispatch.Selection.controlAfter]
      split <;> rfl
    · rename_i cursor observed
      have allowed : cursor.recourse = true := by simpa only [ReviewAvailable, observed] using review
      simp only [if_pos allowed, Evolving.Epoch.Selection.controlAfter, Evolving.Epoch.Dispatch.compile,
        Evolving.Epoch.Dispatch.Selection.controlAfter]
      split <;> rfl
  unfold ReviewAvailable
  rw [same]
  exact review

theorem period_and_accounting_is_ready (source : C) (word : RawWord)
    (ready : Ready source) (review : ReviewAvailable source) :
    Ready (endAt source (periodAndAccounting source word)) ∧
      ReviewAvailable (endAt source (periodAndAccounting source word)) :=
  ⟨(the_first_exhausted_native_cut_is_the_original_paid_drain
    (next source (some (.execute word)))).1,
    drain_keeps_review _ (physical_period_keeps_review source word ready review)⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Funding
