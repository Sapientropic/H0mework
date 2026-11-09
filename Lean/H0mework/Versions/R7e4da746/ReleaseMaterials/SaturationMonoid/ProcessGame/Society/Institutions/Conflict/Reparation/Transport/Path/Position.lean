import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Entries
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Script" => List Input
local notation "opening" => Birth.attacked claim

/-- Native accounting consumes a suffix of the original history with no new
material items. Retaining that suffix lets the same reparation phase survive
the financial first write literally. -/
structure Position (history : Script) where
  posted : Script
  accounting : Script
  history_eq : history = posted ++ accounting
  noItems : inventory (endAt opening posted) accounting = []

namespace Position

abbrev initial : Position claim [] := ⟨[], [], rfl, rfl⟩

variable {claim} {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
  (position : Position claim past)

def phase : Birth.Stage source attack :=
  match position.posted with
  | [] => Birth.opening claim
  | head :: tail => .recorded (head :: tail)

private theorem phase_empty (empty : position.posted = []) : position.phase = Birth.opening claim := by
  simp [phase, empty]

private theorem phase_nonempty (filled : position.posted ≠ []) : position.phase = .recorded position.posted := by
  cases exactHistory : position.posted with
  | nil => exact (filled exactHistory).elim
  | cons _ _ => simp [phase, exactHistory]

theorem posted_due :
    recordedDue source attack position.posted community key = recordedDue source attack past community key := by
  conv_rhs => rw [position.history_eq]
  symm
  apply recordedDue_append_without_receipts
  intro item listed
  rw [position.noItems] at listed
  exact (List.not_mem_nil listed).elim

def account (input : Input) (quiet : inventory (endAt opening past) [input] = []) :
    Position claim (past ++ [input]) where
  posted := position.posted
  accounting := position.accounting ++ [input]
  history_eq := (congrArg (fun earlier => earlier ++ [input]) position.history_eq).trans
    (List.append_assoc _ _ _)
  noItems := by
    rw [inventory_append, position.noItems, ← endAt_append, ← position.history_eq]
    exact quiet

def publish (_position : Position claim past) (input : Input) : Position claim (past ++ [input]) :=
  ⟨past ++ [input], [], List.append_nil _ |>.symm, rfl⟩

theorem publish_phase (input : Input) : (position.publish input).phase = .recorded (past ++ [input]) := by
  cases past <;> rfl

private def reindex {s t s' t' : Birth.Stage source attack} (before : s = s') (after : t = t')
    (motion : Motion (Birth.law claim) s' t') : Motion (Birth.law claim) s t := by
  cases before
  cases after
  exact motion

/-- Only the material publication can select the strict settlement step. -/
def publication (input : Input) :
    Motion (Birth.law claim) position.phase (position.publish input).phase := by
  by_cases initial : position.posted = []
  · have before := position.phase_empty initial
    apply reindex before (position.publish_phase input)
    by_cases closed : recordedDue source attack (past ++ [input]) community key = 0
    · exact .inl (.payRecordedStart _ closed)
    · exact .inr (.recordedStart (by simpa only [List.append_nil] using claim.paid) _)
  · have before := position.phase_nonempty initial
    let more := position.accounting ++ [input]
    have extended : past ++ [input] = position.posted ++ more :=
      (congrArg (fun earlier => earlier ++ [input]) position.history_eq).trans (List.append_assoc _ _ _)
    have after := (position.publish_phase input).trans (congrArg Birth.Stage.recorded extended)
    apply reindex before after
    by_cases positive : 0 < recordedDue source attack position.posted community key
    · by_cases closed : recordedDue source attack (position.posted ++ more) community key = 0
      · exact .inl (.payRecordedNext _ _ positive closed)
      · exact .inr (.recordedNext _ _)
    · exact .inr (.recordedNext _ _)

theorem exact_settlement :
    Nonempty ((Birth.law claim).SettlementAt position.phase) ↔
      recordedDue source attack past community key = 0 := by
  rw [← position.posted_due]
  by_cases initial : position.posted = []
  · have zero : recordedDue source attack position.posted community key ≠ 0 := by
      rw [initial, recordedDue_at_opening claim]
      exact ne_of_gt claim.positive
    have before := position.phase_empty initial
    rw [before]
    constructor
    · rintro ⟨paid⟩
      cases paid with
      | actual _ closed =>
        exact ((ne_of_gt claim.positive) ((initial_remaining_is_the_original_amount claim).symm.trans closed)).elim
    · exact fun closed => (zero closed).elim
  · have before := position.phase_nonempty initial
    rw [before]
    constructor
    · rintro ⟨paid⟩
      cases paid with
      | actualRecorded _ zero => exact zero
    · exact fun zero => ⟨.actualRecorded (Quantities.record opening position.posted) zero⟩

end Position

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
