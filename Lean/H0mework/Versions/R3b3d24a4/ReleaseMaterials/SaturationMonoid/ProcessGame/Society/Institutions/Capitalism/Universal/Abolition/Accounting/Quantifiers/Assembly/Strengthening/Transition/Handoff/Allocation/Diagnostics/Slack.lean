import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Prefix
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Affine
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Minimum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

variable {Label : Type*} {n : ℕ} {rows : List (Tagged Label n)}

def Conflict.violation (failure : Conflict rows) (values : Fin n → ℚ) : ℚ :=
  dot failure.failed.inequality.coeff values - failure.failed.inequality.bound

theorem Conflict.violation_positive (failure : Conflict rows) {values : Fin n → ℚ}
    (prior : Feasible (numeric (rows.take failure.position.val)) values) :
    0 < failure.violation values :=
  sub_pos.mpr (lt_of_not_ge (failure.first_row_rules_out_every_prefix_assignment prior))

private def violationForm (failure : Conflict rows) : Affine n :=
  ⟨failure.failed.inequality.coeff, -failure.failed.inequality.bound⟩

private theorem violationForm_exact (failure : Conflict rows) (values : Fin n → ℚ) :
    (violationForm failure).eval values = failure.violation values := by
  unfold violationForm Affine.eval Conflict.violation
  ring

private def slackObjective (failure : Conflict rows) : List (Inequality (n + 1)) :=
  let violation := (violationForm failure).lift
  let slack := Affine.variableAt (Fin.last n)
  Affine.le violation slack :: Affine.le slack violation ::
    (numeric (rows.take failure.position.val)).map liftInequality

private theorem slackObjective_exact (failure : Conflict rows) (values : Fin (n + 1) → ℚ) :
    Feasible (slackObjective failure) values ↔
      Feasible (numeric (rows.take failure.position.val)) (Fin.init values) ∧
        values (Fin.last n) = failure.violation (Fin.init values) := by
  simp only [slackObjective, feasible_cons, Affine.holds_le, Affine.eval_lift, Affine.eval_variableAt,
    violationForm_exact, feasible_map, liftInequality_exact]
  constructor
  · rintro ⟨lower, upper, prior⟩
    exact ⟨prior, le_antisymm upper lower⟩
  · rintro ⟨prior, equality⟩
    exact ⟨equality.ge, equality.le, prior⟩

/-- The tight increase to the bound of the first impossible original
constraint, with all preceding constraints fixed. -/
structure Slack (failure : Conflict rows) where
  amount : ℚ
  allocation : Fin n → ℚ
  prefixFits : Feasible (numeric (rows.take failure.position.val)) allocation
  positive : 0 < amount
  attained : failure.violation allocation = amount
  least : ∀ values, Feasible (numeric (rows.take failure.position.val)) values →
    amount ≤ failure.violation values

private theorem slackObjective_lifts (failure : Conflict rows) (values : Fin n → ℚ)
    (prior : Feasible (numeric (rows.take failure.position.val)) values) :
    Feasible (slackObjective failure) (Fin.snoc values (failure.violation values)) := by
  apply (slackObjective_exact failure _).mpr
  exact ⟨by simpa only [Fin.init_snoc] using prior, by rw [Fin.init_snoc, Fin.snoc_last]⟩

def Conflict.minimumSlack (failure : Conflict rows) : Slack failure :=
  match minimumLast (slackObjective failure) with
  | .empty impossible =>
      False.elim (impossible ⟨_, slackObjective_lifts failure failure.witness failure.prior⟩)
  | .unboundedBelow lower =>
      let earlier := lower 0
      have exact := (slackObjective_exact failure earlier.val).mp earlier.property.1
      have positive : 0 < earlier.val (Fin.last n) :=
        exact.2.symm ▸ failure.violation_positive exact.1
      False.elim (not_lt_of_gt positive earlier.property.2)
  | .attained values checked least =>
      have exact := (slackObjective_exact failure values).mp checked
      {
        amount := values (Fin.last n)
        allocation := Fin.init values
        prefixFits := exact.1
        positive := exact.2.symm ▸ failure.violation_positive exact.1
        attained := exact.2.symm
        least := fun other prior => (least _ (slackObjective_lifts failure other prior)).trans_eq (Fin.snoc_last _ _)
      }

theorem Slack.relaxation_fits_iff {failure : Conflict rows} (answer : Slack failure) (extra : ℚ) :
    (∃ values, Feasible (numeric (rows.take failure.position.val)) values ∧
      ({ failure.failed.inequality with bound := failure.failed.inequality.bound + extra }).Holds values) ↔
      answer.amount ≤ extra := by
  constructor
  · rintro ⟨values, prior, loosened⟩
    apply (answer.least values prior).trans
    change dot failure.failed.inequality.coeff values ≤ failure.failed.inequality.bound + extra at loosened
    unfold Conflict.violation
    linarith only [loosened]
  · intro enough
    refine ⟨answer.allocation, answer.prefixFits, ?_⟩
    have attained := answer.attained
    unfold Conflict.violation at attained
    change dot failure.failed.inequality.coeff answer.allocation ≤ failure.failed.inequality.bound + extra
    linarith only [attained, enough]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics
