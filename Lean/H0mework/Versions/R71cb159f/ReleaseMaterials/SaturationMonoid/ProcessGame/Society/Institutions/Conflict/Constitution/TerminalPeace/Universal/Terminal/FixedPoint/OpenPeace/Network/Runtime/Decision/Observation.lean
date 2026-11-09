import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Scope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open NoFreeProbe (PaidReview)

/-- A terminating finite observer may choose every query from all earlier
answers. Its output has no primitive equality test on functions. -/
inductive DurationQueries (Raw : Type)
  | done (covered : Bool)
  | read (atState : Raw) (next : ℚ → DurationQueries Raw)

namespace DurationQueries

variable {Raw : Type}

def run (duration : Raw → ℚ) : DurationQueries Raw → List Raw × Bool
  | .done covered => ([], covered)
  | .read atState next =>
    let later := run duration (next (duration atState))
    (atState :: later.1, later.2)

theorem run_eq_of_trace_agreement (plan : DurationQueries Raw) (first second : Raw → ℚ)
    (agrees : ∀ state ∈ (run first plan).1, second state = first state) :
    run second plan = run first plan := by
  induction plan with
  | done covered => rfl
  | read atState next ih =>
    have here := agrees atState List.mem_cons_self
    have later := ih (first atState) (fun state present => agrees state (List.mem_cons_of_mem _ present))
    simp only [run, here, later]

end DurationQueries

variable {Party Good Port Technology Instrument : Type}

local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Prog" => ProgrammeSource.Input Party Good Port Technology Instrument

private def lastClock (states : List Raw) : ℚ :=
  (states.map RawCurrent.clock).foldr max 0

private theorem sampled_le_last (states : List Raw) (state : Raw) (present : state ∈ states) :
    state.clock ≤ lastClock states := by
  induction states with
  | nil => exact (List.not_mem_nil present).elim
  | cons first rest ih =>
    change state.clock ≤ max first.clock (lastClock rest)
    rcases List.mem_cons.mp present with rfl | later
    · exact le_max_left _ _
    · exact (ih later).trans (le_max_right _ _)

private def changeDuration (original : Prog) (clock : ℚ) : Prog :=
  { original with law := { original.law with duration :=
      fun raw => if raw.clock = clock then original.law.duration raw + 1 else original.law.duration raw } }

private theorem changeDuration_violates_protected_terms (original : Prog) (clock : ℚ) :
    ¬ KeepsPublicTerms original (changeDuration original clock) := by
  let site := { original.initial with clock := clock }
  intro kept
  have equality := congrArg (fun programme : Prog => programme.law.duration site) kept
  change (if site.clock = clock then original.law.duration site + 1 else original.law.duration site) =
    original.law.duration site at equality
  rw [if_pos rfl] at equality
  linarith only [equality]

/-- With identical adaptive readings, a raw proposal can still change a
protected duration elsewhere. The change can be proved at that address. -/
theorem every_finite_duration_reader_has_a_hidden_protected_change
    (plan : DurationQueries Raw) (original : Prog) :
    ∃ (candidate : Prog) (site : Raw),
      DurationQueries.run candidate.law.duration plan = DurationQueries.run original.law.duration plan ∧
      ∃ different : ¬ KeepsPublicTerms original candidate,
        checkTermField original candidate (fun programme => programme.law.duration site) =
          some (.isTrue different) := by
  let clock := lastClock (DurationQueries.run original.law.duration plan).1 + 1
  let site := { original.initial with clock := clock }
  let candidate := changeDuration original clock
  have same := DurationQueries.run_eq_of_trace_agreement plan original.law.duration candidate.law.duration (by
    intro state listed
    have bound := sampled_le_last _ state listed
    have fresh : state.clock ≠ clock := by
      dsimp [clock]
      linarith only [bound]
    change (if state.clock = clock then original.law.duration state + 1 else original.law.duration state) = _
    rw [if_neg fresh])
  refine ⟨candidate, site, same, changeDuration_violates_protected_terms original clock, ?_⟩
  unfold checkTermField inheritedTerms
  rw [dif_pos]
  change (if site.clock = clock then original.law.duration site + 1 else original.law.duration site) ≠
    original.law.duration site
  rw [if_pos rfl]
  linarith


variable {Community : Type} [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}
  {current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)}
  {bid : ReviewBid Party Good Port Technology Instrument}

theorem the_paid_original_programme_has_empty_scope (paid : PaidReview current bid) :
    paidEffects paid current.programme = ∅ := by
  ext effect
  cases effect with
  | inl claim => simp [paidEffects_loss, paidLosses_eq, original_programme_has_no_losses]
  | inr value =>
    cases value
    simp [paidEffects_public_terms, KeepsPublicTerms.refl]

/-- Exact initial coverage is not computable by any finite adaptive
reader of the protected duration function alone. This is already a
failure on the actual paid comparison, not a counterfactual write. -/
theorem no_finite_duration_reader_decides_the_paid_scope (paid : PaidReview current bid)
    (plan : DurationQueries Raw) :
    ¬ ∀ proposal : Prog,
      (DurationQueries.run proposal.law.duration plan).2 = true ↔
        paidEffects paid proposal ⊆
          (Language.initial : Language (RawEvent Party Good Port Technology Instrument)
            (Effect Party Good Port Technology Instrument)).covered := by
  intro complete
  obtain ⟨candidate, _, same, different, _⟩ :=
    every_finite_duration_reader_has_a_hidden_protected_change plan current.programme
  have baseline : (DurationQueries.run current.programme.law.duration plan).2 = true := by
    apply (complete current.programme).mpr
    rw [the_paid_original_programme_has_empty_scope paid]
    exact Set.empty_subset _
  have outside := (complete candidate).mp (congrArg Prod.snd same |>.trans baseline)
    ((paidEffects_public_terms paid candidate).mpr different)
  rw [Language.covered_initial] at outside
  exact outside

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision
