import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Plan
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Reservation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_append)

noncomputable section

universe u

/-- Fix the observation and nomination before running any interleaving. -/
structure ObservationPolicy (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
    (Observation : Type u) where
  observe : Root.Cut Party Good Port Technology Instrument → Observation
  nominate : Observation → Reparation.Actual.Script Party Good Port Technology Instrument

/-- After each paid batch a rival may submit a finite block. Every
proposal reads the original history left by the preceding visit. -/
structure RivalPolicy (Party Good Port Technology Instrument : Type) where
  refuser : Party
  count : Nat → Reparation.Actual.Script Party Good Port Technology Instrument → Nat
  choose : Nat → Nat → Reparation.Actual.Script Party Good Port Technology Instrument →
    Reparation.Actual.Input Party Good Port Technology Instrument

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {Observation : Type u}

local notation "M" => PublicFunction.Mandate.State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "P" => ObservationPolicy Party Good Port M Instrument Observation
local notation "Rival" => RivalPolicy Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument}

def candidate (policy : P) (prior : PaidVisit seed community anchor) : Word :=
  policy.nominate (policy.observe (endAt seed prior.history))

theorem equal_observations_nominate_the_same_original_word (policy : P)
    (left right : PaidVisit seed community anchor)
    (same : policy.observe (endAt seed left.history) = policy.observe (endAt seed right.history)) :
    candidate policy left = candidate policy right :=
  congrArg policy.nominate same

def check (policy : P) (answers : OwnerAnswers seed) (prior : PaidVisit seed community anchor) :
    PlanFailure prior answers (candidate policy prior) ⊕
      PLift (Certified prior answers (candidate policy prior)) :=
  inspectPlan prior answers (candidate policy prior)

def step (policy : P) (answers : OwnerAnswers seed) (prior : PaidVisit seed community anchor) :
    PlanFailure prior answers (candidate policy prior) ⊕ PaidVisit seed community anchor :=
  match check policy answers prior with
  | .inl failure => .inl failure
  | .inr accepted => .inr (advancePaid prior answers (candidate policy prior) accepted.down.due)

def rivalScheduler (rival : Rival) (round : Nat) : Scheduler Party Good Port M Instrument where
  lane := fun _ _ => .rival
  personal := fun _ _ => none
  rival := rival.choose round
  offer := fun _ _ _ => []

def rivalRun (answers : OwnerAnswers seed) (rival : Rival) (round : Nat)
    (paid : PaidVisit seed community anchor) (visited : Nat) : PaidVisit seed community anchor :=
  (rivalScheduler rival round).run answers rival.refuser grantRule
    (fun _ _ => paidProbe seed anchor) paid visited

theorem rival_run_reads_the_next_actual_adversary_input (answers : OwnerAnswers seed)
    (rival : Rival) (round : Nat) (paid : PaidVisit seed community anchor) (visited : Nat) :
    let current := rivalRun answers rival round paid visited
    rivalRun answers rival round paid (visited + 1) =
      current.step (withhold answers rival.refuser) grantRule (paidProbe seed anchor)
        (rival.choose round visited current.history) :=
  rfl

def rivalVisit (answers : OwnerAnswers seed) (interleaving : Option Rival)
    (round : Nat) (paid : PaidVisit seed community anchor) : PaidVisit seed community anchor :=
  match interleaving with
  | none => paid
  | some rival => rivalRun answers rival round paid (rival.count round paid.history)

theorem rival_visit_extends_the_same_original_history (answers : OwnerAnswers seed)
    (interleaving : Option Rival) (round : Nat) (paid : PaidVisit seed community anchor) :
    paid.history.IsPrefix (rivalVisit answers interleaving round paid).history := by
  cases interleaving with
  | none => exact List.prefix_rfl
  | some rival =>
    have original (visited : Nat) : paid.history.IsPrefix (rivalRun answers rival round paid visited).history := by
      induction visited with
      | zero => exact List.prefix_rfl
      | succ visited previous =>
        rw [rival_run_reads_the_next_actual_adversary_input]
        exact previous.trans (List.prefix_append _ _)
    exact original (rival.count round paid.history)

variable (policy : ObservationPolicy Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument Observation)
  (answers : OwnerAnswers seed)
  (interleaving : Option (RivalPolicy Party Good Port (PublicFunction.Mandate.State Party Technology) Instrument))
  (opening : PaidVisit seed community anchor)

/-- The recurrence observes the written successor of the previous round.
A refused word keeps the exact original visit for the failure readout. -/
def runAgainst (round : Nat) : PaidVisit seed community anchor :=
  Nat.rec opening (fun index prior =>
    (step policy answers prior).elim (fun _ => prior) (rivalVisit answers interleaving index)) round

theorem runAgainst_succ (round : Nat) :
    let prior := runAgainst policy answers interleaving opening round
    runAgainst policy answers interleaving opening (round + 1) =
      (step policy answers prior).elim (fun _ => prior) (rivalVisit answers interleaving round) :=
  rfl

abbrev run := runAgainst policy answers none opening

def Succeeds (round : Nat) : Prop :=
  ∃ accepted, check policy answers (runAgainst policy answers interleaving opening round) = .inr accepted

def Refused (round : Nat) : Prop :=
  ∃ failure, check policy answers (runAgainst policy answers interleaving opening round) = .inl failure

theorem succeeds_iff_not_refused (round : Nat) :
    Succeeds policy answers interleaving opening round ↔ ¬ Refused policy answers interleaving opening round := by
  unfold Succeeds Refused
  cases check policy answers (runAgainst policy answers interleaving opening round) <;> simp

theorem an_accepted_round_writes_its_exact_original_word (round : Nat)
    {accepted : PLift (Certified (runAgainst policy answers interleaving opening round) answers
      (candidate policy (runAgainst policy answers interleaving opening round)))}
    (written : check policy answers (runAgainst policy answers interleaving opening round) = .inr accepted) :
    let prior := runAgainst policy answers interleaving opening round
    let paid := advancePaid prior answers (candidate policy prior) accepted.down.due
    runAgainst policy answers interleaving opening (round + 1) =
      rivalVisit answers interleaving round paid := by
  dsimp only
  rw [runAgainst_succ, step, written]
  rfl

theorem a_refused_round_keeps_its_exact_original_visit (round : Nat)
    (failed : Refused policy answers interleaving opening round) :
    runAgainst policy answers interleaving opening (round + 1) =
      runAgainst policy answers interleaving opening round := by
  obtain ⟨issue, rejected⟩ := failed
  rw [runAgainst_succ, step, rejected]
  rfl

theorem every_round_extends_the_exact_original_history (round : Nat) :
    (runAgainst policy answers interleaving opening round).history.IsPrefix
      (runAgainst policy answers interleaving opening (round + 1)).history := by
  let prior := runAgainst policy answers interleaving opening round
  cases outcome : check policy answers prior with
  | inl failure =>
    rw [a_refused_round_keeps_its_exact_original_visit policy answers interleaving opening round ⟨failure, outcome⟩]
  | inr accepted =>
    rw [an_accepted_round_writes_its_exact_original_word policy answers interleaving opening round outcome]
    let paid := advancePaid prior answers (candidate policy prior) accepted.down.due
    have appended : prior.history.IsPrefix paid.history := List.prefix_append _ _
    exact appended.trans (rival_visit_extends_the_same_original_history answers interleaving round paid)

omit [DecidableEq Community] in
theorem clock_monotone_under_original_extension {left right : Word} (extension : left.IsPrefix right) :
    (endAt seed left).raw.clock ≤ (endAt seed right).raw.clock := by
  obtain ⟨tail, rfl⟩ := extension
  rw [endAt_append]
  exact Quantities.Execution.the_actual_script_never_runs_the_clock_backwards _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal
