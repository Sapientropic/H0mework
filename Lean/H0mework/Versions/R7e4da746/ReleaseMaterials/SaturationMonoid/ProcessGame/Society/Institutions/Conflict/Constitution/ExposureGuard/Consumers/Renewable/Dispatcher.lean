import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Certificate
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Cofinal.Independent
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Root

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Commitment
open Installed (Port Tech)
open Quantities.Execution (endAt remainingNative nativePayments)

noncomputable section

/-- The material body is fixed. Each nomination reads only the number
of still unpaid native positions at the actual current. -/
def policy : Cofinal.ObservationPolicy Bool Bool Port Tech Unit Nat :=
  ⟨remainingNative, fun mass => nativePayments mass ++ [service]⟩

def authors : OwnerAnswers start := fun _ _ _ _ => true

def firstVisit : PaidVisit start (id : Bool → Bool) [] :=
  paidView (ExposureGuard.start base Installed.scope start id [] noControl
    ⟨wordAt (run 0), live_certificate 0⟩)

private theorem the_actual_owner_lanes_sign_each_period (past word : Word) :
    Exit.SignersChose authors past word := by
  induction word generalizing past with
  | nil => trivial
  | cons _ _ earlier => exact ⟨fun _ => rfl, earlier _⟩

private theorem nomination_at (prior : PaidVisit start (id : Bool → Bool) []) (period : Nat)
    (original : prior.history = history period) :
    Cofinal.candidate policy prior = wordAt (run period) := by
  unfold Cofinal.candidate
  rw [original, run_is_its_own_native_fold]
  rfl

private theorem checked_at (prior : PaidVisit start (id : Bool → Bool) []) (period : Nat)
    (original : prior.history = history period) :
    MandateExit.LiveCertificate start [] prior.history (id : Bool → Bool) base Installed.scope noControl
      (Cofinal.candidate policy prior) := by
  rw [nomination_at prior period original, original]
  exact live_certificate period

private theorem approved_at (prior : PaidVisit start (id : Bool → Bool) []) (period : Nat)
    (original : prior.history = history period) : Certified prior authors (Cofinal.candidate policy prior) := by
  exact certify_signed_live_exit prior authors (Cofinal.candidate policy prior)
    (checked_at prior period original) (the_actual_owner_lanes_sign_each_period _ _)

abbrev paidRun := Cofinal.run policy authors firstVisit

theorem the_registered_renewal_is_the_guarded_observed_run (period : Nat) :
    (paidRun period).history = history period := by
  induction period with
  | zero => rfl
  | succ period original =>
    let prior := paidRun period
    obtain ⟨_, verified⟩ := an_admissible_commitment_is_returned_as_certified prior authors
      (Cofinal.candidate policy prior) (approved_at prior period original)
    have written := Cofinal.an_accepted_round_writes_its_exact_original_word policy authors none firstVisit period verified
    change (Cofinal.runAgainst policy authors none firstVisit (period + 1)).history = _
    rw [written]
    change prior.history ++ Cofinal.candidate policy prior = history (period + 1)
    rw [nomination_at prior period original, original]
    rfl

/-- Each call through the reserved dispatcher writes exactly the next
paid visit of the observed production recurrence. -/
theorem the_next_actual_period_is_written_against_every_arbiter
    (period : Nat) (rival : Scheduler Bool Bool Port Tech Unit) (person : Bool) :
    execute (paidRun period) authors rival person (Cofinal.candidate policy (paidRun period)) =
      .inr (paidRun (period + 1)) := by
  let prior := paidRun period
  have checked := approved_at prior period (the_registered_renewal_is_the_guarded_observed_run period)
  obtain ⟨_, verified⟩ := an_admissible_commitment_is_returned_as_certified prior authors
    (Cofinal.candidate policy prior) checked
  have same := Cofinal.an_accepted_round_writes_its_exact_original_word policy authors none firstVisit period verified
  change execute prior authors rival person (Cofinal.candidate policy prior) =
    .inr (Cofinal.runAgainst policy authors none firstVisit (period + 1))
  rw [same]
  exact execute_writes_the_certified_literal_word prior authors rival person _ checked

theorem the_observed_run_has_its_actual_clock_and_fresh_independent_exit (period : Nat) :
    let current := paidRun period
    let word := Cofinal.candidate policy current
    (endAt start current.history).raw.clock = 4 + (period : ℚ) ∧
      ∃ next : GuardedVisit base Installed.scope start (id : Bool → Bool) [] noControl,
        resume base Installed.scope noControl current word = .inr next ∧ paidView next = current ∧
        ∃ chosen : MandateExit.Chosen next authors, chosen.word = word := by
  let current := paidRun period
  have original := the_registered_renewal_is_the_guarded_observed_run period
  refine ⟨?_, the_signed_exit_reopens_the_exact_paid_visit current authors (Cofinal.candidate policy current)
    (checked_at current period original) (the_actual_owner_lanes_sign_each_period _ _)⟩
  rw [show current.history = history period from original, run_is_its_own_native_fold]
  exact actual_clock period

theorem the_registered_independent_supply_produces_cofinal_paid_peace :
    Cofinal.CofinalRun policy authors none firstVisit := by
  refine ⟨fun period => ?_, fun horizon => ?_⟩
  · let prior := paidRun period
    exact an_admissible_commitment_is_returned_as_certified prior authors (Cofinal.candidate policy prior)
      (approved_at prior period (the_registered_renewal_is_the_guarded_observed_run period))
  · obtain ⟨period, beyond⟩ := exists_nat_gt horizon
    refine ⟨period, ?_⟩
    change horizon < (endAt start (paidRun period).history).raw.clock
    rw [(the_observed_run_has_its_actual_clock_and_fresh_independent_exit period).1]
    linarith

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable
