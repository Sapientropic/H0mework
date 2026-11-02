import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution

/-- Arithmetic rows are a readout of evaluated source trials. They do not
select a history, authorize a payment or constitute an outcome oracle. -/
structure RiskRow where
  weight : ℚ
  succeeded : Bool
  loss : ℚ
  deriving DecidableEq

def successMass (rows : List RiskRow) : ℚ :=
  (rows.map fun row => if row.succeeded then row.weight else 0).sum

def failureLoss (rows : List RiskRow) : ℚ :=
  (rows.map fun row => if row.succeeded then 0 else row.weight * row.loss).sum

def cashChange (row : RiskRow) (reward : ℚ) : ℚ :=
  if row.succeeded then reward else -row.loss

def expectedChange (rows : List RiskRow) (reward : ℚ) : ℚ :=
  (rows.map fun row => row.weight * cashChange row reward).sum

/-- The reward is payable on a witnessed success. The failure branch retains
its actual loss rather than receiving an invented successful return. -/
def contingentReward (rows : List RiskRow) (outside loading : ℚ) : ℚ :=
  (failureLoss rows + outside + loading) / successMass rows

theorem expected_change_separates_actual_failure_losses (rows : List RiskRow) (reward : ℚ) :
    expectedChange rows reward = successMass rows * reward - failureLoss rows := by
  induction rows with
  | nil => simp [expectedChange, successMass, failureLoss]
  | cons row rows ih =>
      have step : expectedChange (row :: rows) reward =
          row.weight * cashChange row reward + expectedChange rows reward := rfl
      rw [step, ih]
      cases outcome : row.succeeded <;>
        simp [successMass, failureLoss, cashChange, outcome, List.map_cons, List.sum_cons] <;> ring

theorem the_source_quote_pays_the_declared_ex_ante_return
    (rows : List RiskRow) (outside loading : ℚ) (possible : 0 < successMass rows) :
    expectedChange rows (contingentReward rows outside loading) = outside + loading := by
  rw [expected_change_separates_actual_failure_losses]
  unfold contingentReward
  rw [mul_div_cancel₀ _ (ne_of_gt possible)]
  ring

theorem a_nonnegative_loading_meets_the_participants_outside_option
    (rows : List RiskRow) (outside loading : ℚ) (possible : 0 < successMass rows)
    (paidLoading : 0 ≤ loading) :
    outside ≤ expectedChange rows (contingentReward rows outside loading) := by
  rw [the_source_quote_pays_the_declared_ex_ante_return rows outside loading possible]
  linarith

theorem a_positive_loading_strictly_improves_the_participants_outside_option
    (rows : List RiskRow) (outside loading : ℚ) (possible : 0 < successMass rows)
    (paidLoading : 0 < loading) :
    outside < expectedChange rows (contingentReward rows outside loading) := by
  rw [the_source_quote_pays_the_declared_ex_ante_return rows outside loading possible]
  linarith

theorem a_real_failure_still_has_its_real_loss (row : RiskRow) (reward : ℚ)
    (failed : row.succeeded = false) : cashChange row reward = -row.loss := by
  simp [cashChange, failed]

theorem no_success_mass_cannot_finance_a_positive_failure_loss
    (rows : List RiskRow) (reward : ℚ) (impossible : successMass rows = 0)
    (lost : 0 < failureLoss rows) : expectedChange rows reward < 0 := by
  rw [expected_change_separates_actual_failure_losses, impossible]
  linarith

theorem the_reward_changes_with_the_source_failure_loss
    (first second : List RiskRow) (outside loading : ℚ)
    (sameMass : successMass second = successMass first) :
    contingentReward second outside loading - contingentReward first outside loading =
      (failureLoss second - failureLoss first) / successMass first := by
  unfold contingentReward
  rw [sameMass]
  ring

def prefersParticipation (rows : List RiskRow) (outside loading : ℚ) : Bool :=
  decide (0 < successMass rows ∧
    outside ≤ expectedChange rows (contingentReward rows outside loading))

theorem the_quoted_participation_choice_precedes_the_actual_outcome
    (rows : List RiskRow) (outside loading : ℚ) (possible : 0 < successMass rows)
    (paidLoading : 0 ≤ loading) : prefersParticipation rows outside loading = true := by
  apply decide_eq_true
  exact ⟨possible, a_nonnegative_loading_meets_the_participants_outside_option
    rows outside loading possible paidLoading⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution
