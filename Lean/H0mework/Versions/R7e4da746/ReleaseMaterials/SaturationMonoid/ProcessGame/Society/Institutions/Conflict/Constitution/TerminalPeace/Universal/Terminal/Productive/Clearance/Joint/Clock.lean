import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Domain
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
open Capitalism.Universal.Source.Program
open Reparation.Actual (ReceiptAnswers Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (reserve : Party → Good → ℚ) (firstWrite : Script Party Good Port Technology Instrument)
  (offers : ProductionMenu Party Good Port Technology Instrument)

local notation "Word" => Script Party Good Port Technology Instrument
local notation "Fits" => Feasible loss answers reserve firstWrite offers

def paidTimes : Set ℝ :=
  {tick | ∃ word : Word, Fits word ∧ ((prefixRaw loss word).clock : ℝ) = tick}

def firstPossibleTime : ℝ := sInf (paidTimes loss answers reserve firstWrite offers)

local notation "Times" => paidTimes loss answers reserve firstWrite offers
local notation "Floor" => firstPossibleTime loss answers reserve firstWrite offers

private theorem paidTimes_bddBelow : BddBelow Times := by
  refine ⟨((endAt seed (Occurrence.history loss)).raw.clock : ℝ), ?_⟩
  rintro tick ⟨word, _, rfl⟩
  have physical := the_actual_script_never_runs_the_clock_backwards
    (endAt seed (Occurrence.history loss)) word
  rw [← endAt_append] at physical
  exact_mod_cast physical

theorem physical_deadline_above_floor_iff (paid : PaidFrontier loss answers reserve firstWrite offers) (deadline : ℝ) :
    Floor < deadline ↔ ∃ word : Word, Fits word ∧ ((prefixRaw loss word).clock : ℝ) < deadline := by
  constructor
  · intro above
    have nonempty : Set.Nonempty Times := ⟨_, paid.word, paid.feasible, rfl⟩
    obtain ⟨_, ⟨word, fits, rfl⟩, timely⟩ := exists_lt_of_csInf_lt nonempty above
    exact ⟨word, fits, timely⟩
  · rintro ⟨word, fits, timely⟩
    exact (csInf_le (paidTimes_bddBelow loss answers reserve firstWrite offers) ⟨word, fits, rfl⟩).trans_lt timely

/-- If heterogeneous durations have no first physical timestamp, the
solver returns actual paid prefixes at every strictly later bound. -/
inductive PhysicalFrontier where
  | attained (word : Word) (fits : Fits word) (time : ((prefixRaw loss word).clock : ℝ) = Floor)
      (run : Realization loss answers (fun _ => True) word offers)
      (earliestVisit : ∀ other : Word, Fits other → ((prefixRaw loss other).clock : ℝ) = Floor →
        word.length ≤ other.length)
  | approached (missing : Floor ∉ Times)
      (near : ∀ deadline : ℝ, Floor < deadline →
        (word : Word) × {_run : Realization loss answers (fun _ => True) word offers //
          Fits word ∧ Floor < ((prefixRaw loss word).clock : ℝ) ∧ ((prefixRaw loss word).clock : ℝ) < deadline})

def selectFirstPhysicalTime (paid : PaidFrontier loss answers reserve firstWrite offers) :
    PhysicalFrontier loss answers reserve firstWrite offers := by
  classical
  by_cases attained : Floor ∈ Times
  · let first := shortestWord
      (fun word : Word => Fits word ∧ ((prefixRaw loss word).clock : ℝ) = Floor) attained
    exact .attained first.val first.property.1.1 first.property.1.2 (realize first.property.1.1.living)
      (fun other fits atFloor => first.property.2 other ⟨fits, atFloor⟩)
  · refine .approached attained fun deadline after => ?_
    have available := (physical_deadline_above_floor_iff loss answers reserve firstWrite offers paid deadline).mp after
    let word := Classical.choose available
    have fits := Classical.choose_spec available
    have physical : ((prefixRaw loss word).clock : ℝ) ∈ Times := ⟨word, fits.1, rfl⟩
    have lower := csInf_le (paidTimes_bddBelow loss answers reserve firstWrite offers) physical
    exact ⟨word, ⟨realize fits.1.living, fits.1, lt_of_le_of_ne lower (fun eq => attained (eq.symm ▸ physical)), fits.2⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint
