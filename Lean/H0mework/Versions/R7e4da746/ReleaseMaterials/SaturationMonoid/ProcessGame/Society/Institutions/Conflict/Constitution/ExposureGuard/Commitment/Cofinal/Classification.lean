import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {Observation : Type u}
  {seed : Root.Cut Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument}

local notation "M" => PublicFunction.Mandate.State Party Technology
local notation "Rival" => RivalPolicy Party Good Port M Instrument

variable (policy : ObservationPolicy Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument Observation)
  (answers : OwnerAnswers seed)
  (interleaving : Option (RivalPolicy Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument))
  (opening : PaidVisit seed community anchor)

local notation "visit" => runAgainst policy answers interleaving opening
local notation "succeeds" => Succeeds policy answers interleaving opening
local notation "refused" => Refused policy answers interleaving opening

def clock (round : Nat) : ℚ :=
  (endAt seed (visit round).history).raw.clock

def FirstFailure (round : Nat) : Prop :=
  refused round ∧ ∀ earlier < round, succeeds earlier

def AllPaid : Prop := ∀ round, succeeds round

def ClockBounded : Prop :=
  ∃ horizon : ℚ, ∀ round, clock policy answers interleaving opening round ≤ horizon

def CofinalRun : Prop :=
  AllPaid policy answers interleaving opening ∧
    ∀ horizon : ℚ, ∃ round, horizon < clock policy answers interleaving opening round

theorem the_clock_never_runs_backwards (round : Nat) :
    clock policy answers interleaving opening round ≤ clock policy answers interleaving opening (round + 1) :=
  clock_monotone_under_original_extension (seed := seed)
    (every_round_extends_the_exact_original_history policy answers interleaving opening round)

theorem a_refused_round_keeps_the_same_visit_at_all_later_rounds (round : Nat)
    (failed : refused round) (later : Nat) :
    visit (round + later) = visit round := by
  induction later with
  | zero => rfl
  | succ later inherited =>
    have again : refused (round + later) := by
      unfold Refused at *
      rwa [inherited]
    rw [Nat.add_succ,
      a_refused_round_keeps_its_exact_original_visit policy answers interleaving opening (round + later) again,
      inherited]

/-- Classify the one actual execution for this fixed observation policy.
The bounded branch has no refused round, and each failed branch retains
the exact original issue at its first refused cut. -/
theorem trichotomy :
    (∃ round, FirstFailure policy answers interleaving opening round) ∨
      (AllPaid policy answers interleaving opening ∧ ClockBounded policy answers interleaving opening) ∨
      CofinalRun policy answers interleaving opening := by
  classical
  by_cases paid : AllPaid policy answers interleaving opening
  · by_cases bounded : ClockBounded policy answers interleaving opening
    · exact Or.inr (Or.inl ⟨paid, bounded⟩)
    · refine Or.inr (Or.inr ⟨paid, fun horizon => ?_⟩)
      by_contra! below
      exact bounded ⟨horizon, below⟩
  · have failed : ∃ round, refused round := by
      by_contra none
      exact paid (fun round => (succeeds_iff_not_refused policy answers interleaving opening round).2
        fun issue => none ⟨round, issue⟩)
    refine Or.inl ⟨Nat.find failed, Nat.find_spec failed, fun earlier h => ?_⟩
    exact (succeeds_iff_not_refused policy answers interleaving opening earlier).2 (Nat.find_min failed h)

theorem failure_or_bounded_iff_not_cofinal :
    ¬ CofinalRun policy answers interleaving opening ↔
      (∃ round, FirstFailure policy answers interleaving opening round) ∨
      (AllPaid policy answers interleaving opening ∧ ClockBounded policy answers interleaving opening) := by
  constructor
  · intro denied
    rcases trichotomy policy answers interleaving opening with failed | bounded | cofinal
    · exact Or.inl failed
    · exact Or.inr bounded
    · exact (denied cofinal).elim
  · rintro (⟨round, first⟩ | ⟨_, horizon, bounded⟩) cofinal
    · exact (succeeds_iff_not_refused policy answers interleaving opening round).mp
        (cofinal.1 round) first.1
    · obtain ⟨round, beyond⟩ := cofinal.2 horizon
      exact not_lt_of_ge (bounded round) beyond

omit interleaving in
theorem a_fixed_policy_loses_cofinality_iff_one_actual_interleaving_witnesses_it :
    (¬ ∀ actual : Option Rival, CofinalRun policy answers actual opening) ↔
      ∃ actual : Option Rival, (∃ round, FirstFailure policy answers actual opening round) ∨
        (AllPaid policy answers actual opening ∧ ClockBounded policy answers actual opening) := by
  classical
  rw [not_forall]
  exact exists_congr (fun actual => failure_or_bounded_iff_not_cofinal policy answers actual opening)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal
