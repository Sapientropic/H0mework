import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.ReviewWindow
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation

open Capitalism.Universal.Source.Program PublicFunction PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Slice" => Cell Party Good Port Technology Instrument

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : PublicFunction.Mandate.Scope (Party := Party) (Good := Good) (Port := Port))
  (first second : Party) (unit : Good)
  (initial : RawCurrent Party Good (State Party Technology) Instrument)
  (words : List (RawEvent Party Good Port (State Party Technology) Instrument))

/-- A fitted term comes with its actual addressed debit assignment and
a funded independent review. All fields are outputs of the finite scan. -/
structure SafeTerm where
  cell : Cell Party Good Port Technology Instrument
  assigned : Matching scope.task cell
  matching : assigned ∈ safeAssignments scope.task cell
  ready : ReleaseReady base scope cell.target first second unit (termBand scope.task cell assigned).lower

variable {base scope first second unit}

def SafeTerm.band (term : SafeTerm base scope first second unit) : Band :=
  termBand scope.task term.cell term.assigned

def SafeTerm.Allows (term : SafeTerm base scope first second unit) (expiry : ℚ) : Prop :=
  expiry ≤ scope.task.deadline ∧ term.band.Holds expiry

theorem SafeTerm.at_least_owns_its_review (term : SafeTerm base scope first second unit) :
    term.Allows term.band.lower :=
  let fit := of_decide_eq_true (List.mem_filter.mp term.matching).2
  ⟨fit.2, fit.1⟩

theorem SafeTerm.release (term : SafeTerm base scope first second unit) (expiry : ℚ)
    (fits : term.Allows expiry) :
    ReleaseReady base scope term.cell.target first second unit expiry := by
  have firstTime := ((term_band_exact scope.task term.cell term.assigned term.band.lower).mp
    term.at_least_owns_its_review.2).2.1
  have actualTime := ((term_band_exact scope.task term.cell term.assigned expiry).mp fits.2).2.1
  exact (release_ready_iff_expired_cell base scope term.cell.target first second unit firstTime actualTime).mp term.ready

variable (base scope first second unit)

def authorizedTerms (cell : Slice) : List (SafeTerm base scope first second unit) :=
  (safeAssignments scope.task cell).attach.filterMap fun assigned =>
    if ready : ReleaseReady base scope cell.target first second unit
      (termBand scope.task cell assigned.val).lower then
      some ⟨cell, assigned.val, assigned.property, ready⟩
    else none

def frontier : List (SafeTerm base scope first second unit) :=
  (cells base scope ⟨initial.clock, none⟩ initial words).flatMap (authorizedTerms base scope first second unit)

def Feasible (expiry : ℚ) : Prop :=
  ∃ cell ∈ cells base scope ⟨initial.clock, none⟩ initial words,
    ServiceSafeAt scope.task cell expiry ∧ ReleaseReady base scope cell.target first second unit expiry

/-- Interpret a proposed date directly in its original submitted words,
without invoking the deadline solver or choosing any prepared endpoint. -/
def submittedAt (expiry : ℚ) : Slice :=
  let actual := replay base scope expiry initial words
  ⟨⟨initial.clock, none⟩, actual.1, actual.2⟩

theorem feasible_iff_the_original_submission_pays_at_the_date (expiry : ℚ) :
    Feasible base scope first second unit initial words expiry ↔
      ServiceSafeAt scope.task (submittedAt base scope initial words expiry) expiry ∧
      ReleaseReady base scope (submittedAt base scope initial words expiry).target first second unit expiry := by
  constructor
  · rintro ⟨cell, listed, service, review⟩
    obtain ⟨root, exact⟩ := (cell_replays_at_every_deadline base scope ⟨initial.clock, none⟩
      initial words cell listed).2 expiry service.1
    unfold submittedAt
    rw [exact]
    exact ⟨⟨root, service.2⟩, review⟩
  · intro checked
    have root := checked.1.1
    obtain ⟨cell, listed, fits⟩ :=
      cells_cover_all_deadlines base scope ⟨initial.clock, none⟩ initial words expiry root
    have exact := ((cell_replays_at_every_deadline base scope ⟨initial.clock, none⟩
      initial words cell listed).2 expiry fits).2
    unfold submittedAt at checked
    rw [exact] at checked
    exact ⟨cell, listed, ⟨fits, checked.1.2⟩, checked.2⟩

theorem frontier_is_exact (expiry : ℚ) :
    Feasible base scope first second unit initial words expiry ↔
      ∃ term ∈ frontier base scope first second unit initial words, term.Allows expiry := by
  constructor
  · rintro ⟨cell, listed, service, review⟩
    obtain ⟨due, assigned, exactAssignment, fits⟩ :=
      (safe_service_iff_listed_assignment scope.task cell expiry).mp service
    have atLower := Band.lower_fits fits
    have firstTime := ((term_band_exact scope.task cell assigned _).mp atLower).2.1
    have lastTime := ((term_band_exact scope.task cell assigned expiry).mp fits).2.1
    have ready := (release_ready_iff_expired_cell base scope cell.target first second unit lastTime firstTime).mp review
    refine ⟨⟨cell, assigned, exactAssignment, ready⟩, ?_, due, fits⟩
    apply List.mem_flatMap.mpr
    refine ⟨cell, listed, List.mem_filterMap.mpr ?_⟩
    refine ⟨⟨assigned, exactAssignment⟩, by simp, ?_⟩
    simp only [dif_pos ready]
  · rintro ⟨term, listed, fits⟩
    obtain ⟨cell, visited, trial⟩ := List.mem_flatMap.mp listed
    obtain ⟨assigned, _member, selected⟩ := List.mem_filterMap.mp trial
    split at selected
    next checked =>
      cases Option.some.inj selected
      exact ⟨cell, visited,
        (safe_service_iff_listed_assignment scope.task cell expiry).mpr
          ⟨fits.1, assigned.val, assigned.property, fits.2⟩, (SafeTerm.mk cell assigned.val assigned.property checked).release expiry fits⟩
    next => cases selected

def shortest? :=
  Threshold.best (fun term : SafeTerm base scope first second unit => -term.band.lower)
    (frontier base scope first second unit initial words)

theorem shortest_exact {term : SafeTerm base scope first second unit}
    (selected : shortest? base scope first second unit initial words = some term) :
    term ∈ frontier base scope first second unit initial words ∧
      IsLeast {expiry | Feasible base scope first second unit initial words expiry} term.band.lower := by
  have exactTerm := Threshold.best_spec selected
  refine ⟨exactTerm.1, (frontier_is_exact base scope first second unit initial words _).mpr
    ⟨term, exactTerm.1, term.at_least_owns_its_review⟩, ?_⟩
  intro expiry fits
  obtain ⟨other, considered, fits⟩ :=
    (frontier_is_exact base scope first second unit initial words expiry).mp fits
  exact (neg_le_neg_iff.mp (exactTerm.2 other considered)).trans (Band.lower_le fits.2)

theorem shortest_eq_none_iff :
    shortest? base scope first second unit initial words = none ↔
      ∀ expiry, ¬ Feasible base scope first second unit initial words expiry := by
  rw [shortest?, Threshold.best_eq_none]
  constructor
  · intro empty expiry safe
    obtain ⟨term, considered, _⟩ :=
      (frontier_is_exact base scope first second unit initial words expiry).mp safe
    rw [empty] at considered
    cases considered
  · intro fails
    cases ready : frontier base scope first second unit initial words with
    | nil => rfl
    | cons term later =>
      exact (fails _ ((frontier_is_exact base scope first second unit initial words _).mpr
        ⟨term, by rw [ready]; exact List.mem_cons_self, term.at_least_owns_its_review⟩)).elim

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation
