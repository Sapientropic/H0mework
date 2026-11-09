import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Calendar
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Assignments

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Exit
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
open PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]

local notation "Slice" => Cell Party Good Port Technology Instrument

/-- Preserve the two physical clock readings of each original posting.
The native start and commit guards are different for a positive-duration word. -/
structure TimedPosting (Party Good Port Technology Instrument : Type) where
  posting : Posting Party Good Port Technology Instrument
  commit : ℚ

def Cell.positions (cell : Slice) : List (TimedPosting Party Good Port Technology Instrument) :=
  cell.history.flatMap fun day => day.postings.map fun posting => ⟨posting, day.after.clock⟩

variable (task : PublicTaskSpec Party Good) (cell : Cell Party Good Port Technology Instrument)

abbrev Slot := Fin task.slots.length
abbrev Position := Fin cell.positions.length
abbrev Matching := Finset (Slot task × Position cell)

def eligibleUse (slot : Slot task) (position : Position cell) : Bool :=
  let need := task.slots[slot]
  let posted := cell.positions[position]
  posted.posting.accepted &&
    decide (task.earliest ≤ posted.posting.item.before.clock ∧ posted.commit ≤ task.deadline ∧
      Necessity.UseMatches posted.posting.item.request.operation need.bearer need.goods need.purpose)

def fullAssignments : List (Matching task cell) :=
  assignments (eligibleUse task cell) (List.finRange _) (List.finRange _)

def selectedPositions (assigned : Matching task cell) : List (Position cell) :=
  (List.finRange _).filter fun position => decide (position ∈ assigned.image Prod.snd)

private theorem fold_max_le_iff (clocks : List ℚ) (start expiry : ℚ) :
    clocks.foldr max start ≤ expiry ↔ start ≤ expiry ∧ ∀ clock ∈ clocks, clock ≤ expiry := by
  induction clocks with
  | nil => simp
  | cons clock tail ih =>
    simp only [List.foldr_cons, max_le_iff, ih, List.forall_mem_cons]
    tauto

def lastService (assigned : Matching task cell) : ℚ :=
  ((selectedPositions task cell assigned).map fun position => cell.positions[position].commit).foldr
    max cell.band.lower

omit [DecidableEq Party] [DecidableEq Good] in
theorem last_service_iff (assigned : Matching task cell) (expiry : ℚ) :
    lastService task cell assigned ≤ expiry ↔
      cell.band.lower ≤ expiry ∧
        ∀ edge ∈ assigned, cell.positions[edge.2].commit ≤ expiry := by
  rw [lastService, fold_max_le_iff, and_congr_right_iff]
  intro _
  constructor
  · intro latest edge original
    apply latest _ (List.mem_map.mpr ⟨edge.2, ?_, rfl⟩)
    exact List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true (Finset.mem_image_of_mem _ original)⟩
  · intro latest _ found
    obtain ⟨position, used, rfl⟩ := List.mem_map.mp found
    obtain ⟨edge, original, rfl⟩ := Finset.mem_image.mp (of_decide_eq_true (List.mem_filter.mp used).2)
    exact latest _ original

/-- The exact term of this assignment ends no earlier than its last
service commitment and strictly before its registered review. -/
def termBand (assigned : Matching task cell) : Band :=
  ⟨lastService task cell assigned, (cell.band.below cell.target.clock).upper⟩

omit [DecidableEq Party] [DecidableEq Good] in
theorem term_band_exact (assigned : Matching task cell) (expiry : ℚ) :
    (termBand task cell assigned).Holds expiry ↔ cell.band.Holds expiry ∧
      expiry < cell.target.clock ∧
        ∀ edge ∈ assigned, cell.positions[edge.2].commit ≤ expiry := by
  have lower :
      lastService task cell assigned ≤ expiry ↔
        cell.band.lower ≤ expiry ∧
          ∀ edge ∈ assigned, cell.positions[edge.2].commit ≤ expiry :=
    last_service_iff task cell assigned expiry
  have period := Band.below_iff cell.band cell.target.clock expiry
  have belowLower (h : (cell.band.below cell.target.clock).Holds expiry) : cell.band.lower ≤ expiry :=
    Band.lower_le (band := cell.band.below cell.target.clock) h
  constructor
  · intro fits
    have committed := lower.mp (Band.lower_le fits)
    have beforeReview := period.mp
      ⟨fun clock same => (Option.some.inj same).symm ▸ committed.1, fits.2⟩
    exact ⟨beforeReview.1, beforeReview.2, committed.2⟩
  · rintro ⟨calendar, early, committed⟩
    have fits := period.mpr ⟨calendar, early⟩
    exact ⟨fun clock same => (Option.some.inj same).symm ▸ lower.mpr ⟨belowLower fits, committed⟩,
      fits.2⟩

def ServiceSafeAt (expiry : ℚ) : Prop :=
  cell.band.Holds expiry ∧ expiry ≤ task.deadline ∧ expiry < cell.target.clock ∧
    ∃ assigned : Matching task cell,
      ExactAssignment (eligibleUse task cell) (List.finRange _) (List.finRange _) assigned ∧
        ∀ edge ∈ assigned, cell.positions[edge.2].commit ≤ expiry

def safeAssignments : List (Matching task cell) :=
  (fullAssignments task cell).filter fun assigned =>
    decide ((termBand task cell assigned).Holds (termBand task cell assigned).lower ∧
      (termBand task cell assigned).lower ≤ task.deadline)

/-- Neither a discretization nor a supplied horizon is needed. The
finite literal debit assignments describe all rational safe expiries. -/
theorem safe_service_iff_listed_assignment (expiry : ℚ) :
    ServiceSafeAt task cell expiry ↔
      expiry ≤ task.deadline ∧ ∃ assigned ∈ safeAssignments task cell, (termBand task cell assigned).Holds expiry := by
  have exactMatching (assigned : Matching task cell) :=
    assignments_are_exact (eligibleUse task cell) (List.finRange _) (List.finRange _)
      (List.nodup_finRange _) assigned
  constructor
  · rintro ⟨calendar, due, review, assigned, whole, committed⟩
    have fits := (term_band_exact task cell assigned expiry).mpr ⟨calendar, review, committed⟩
    exact ⟨due, assigned, List.mem_filter.mpr ⟨(exactMatching assigned).mpr whole,
      decide_eq_true ⟨Band.lower_fits fits, (Band.lower_le fits).trans due⟩⟩, fits⟩
  · rintro ⟨due, assigned, listed, fits⟩
    obtain ⟨calendar, review, committed⟩ := (term_band_exact task cell assigned expiry).mp fits
    exact ⟨calendar, due, review, assigned, (exactMatching assigned).mp (List.mem_filter.mp listed).1, committed⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation
