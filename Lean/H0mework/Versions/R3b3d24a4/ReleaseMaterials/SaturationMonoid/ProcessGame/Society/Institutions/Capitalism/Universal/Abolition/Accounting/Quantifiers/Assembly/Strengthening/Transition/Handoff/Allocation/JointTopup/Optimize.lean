import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup.Limits
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Minimum
import Mathlib.Algebra.Order.BigOperators.Group.List

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear Diagnostics

variable {Label : Type*} {n : ℕ}

private def scoredRows (rows : List (Tagged Label n)) (score : Affine n) : List (Inequality (n + 1)) :=
  Affine.le score.lift (Affine.variableAt (Fin.last n)) ::
    (numeric rows).map liftInequality

private theorem scoredRows_exact (rows : List (Tagged Label n)) (score : Affine n)
    (values : Fin (n + 1) → ℚ) :
    Feasible (scoredRows rows score) values ↔
      score.eval (Fin.init values) ≤ values (Fin.last n) ∧ Feasible (numeric rows) (Fin.init values) := by
  simp only [scoredRows, feasible_cons, Affine.holds_le, Affine.eval_lift, Affine.eval_variableAt,
    feasible_map, liftInequality_exact]
  rfl

private theorem scoredRows_attain_value (rows : List (Tagged Label n)) (score : Affine n)
    (values : Fin n → ℚ) (admitted : Feasible (numeric rows) values) :
    Feasible (scoredRows rows score) (Fin.snoc values (score.eval values)) := by
  apply (scoredRows_exact rows score _).mpr
  simpa only [Fin.init_snoc, Fin.snoc_last, le_refl, true_and] using admitted

inductive Optimum (rows : List (Tagged Label n)) (score : Affine n) where
  | attained (values : Fin n → ℚ) (admitted : Feasible (numeric rows) values)
      (least : ∀ other, Feasible (numeric rows) other → score.eval values ≤ score.eval other)
  | blocked (conflict : Conflict rows)

/-- An externally chosen objective ranks the original feasible vectors.
The numerical rejection retains the original labelled constraints. -/
def minimize (rows : List (Tagged Label n)) (score : Affine n)
    (nonnegative : ∀ values, Feasible (numeric rows) values → 0 ≤ score.eval values) : Optimum rows score :=
  match minimumLast (scoredRows rows score) with
  | .empty impossible =>
      .blocked (conflictOfInfeasible rows (fun ⟨values, checked⟩ =>
        impossible ⟨_, scoredRows_attain_value rows score values checked⟩))
  | .unboundedBelow lower =>
      let below := lower 0
      have checked := (scoredRows_exact rows score below.val).mp below.property.1
      False.elim (not_lt_of_ge ((nonnegative _ checked.2).trans checked.1) below.property.2)
  | .attained values checked least =>
      have exact := (scoredRows_exact rows score values).mp checked
      .attained (Fin.init values) exact.2 fun other admitted =>
        exact.1.trans ((least _ (scoredRows_attain_value rows score other admitted)).trans_eq (Fin.snoc_last _ _))

variable {Address : Type*} [DecidableEq Address]

private def scaled (weight : ℚ) (form : Affine n) : Affine n :=
  ⟨fun i => weight * form.coeff i, weight * form.constant⟩

private theorem scaled_exact (weight : ℚ) (form : Affine n) (values : Fin n → ℚ) :
    (scaled weight form).eval values = weight * form.eval values := by
  simp only [scaled, Affine.eval, dot, mul_add, mul_assoc, Finset.mul_sum]

def weightedTotal (keys : List Address) (weights extra : Address → ℚ) : ℚ :=
  (keys.map (fun key => weights key * extra key)).sum

def weightedForm (keys : List Address) (distinct : keys.Nodup) (n : ℕ)
    (weights : Address → ℚ) : Affine (n + keys.length) :=
  Affine.sum (keys.map fun key => scaled (weights key) (extraForm keys distinct n key))

theorem weightedForm_exact (keys : List Address) (distinct : keys.Nodup)
    (weights : Address → ℚ) (values : Fin (n + keys.length) → ℚ) :
    (weightedForm keys distinct n weights).eval values =
      weightedTotal keys weights (extraAt keys distinct values) := by
  simp only [weightedForm, weightedTotal, Affine.eval_sum, List.map_map, Function.comp_def,
    scaled_exact, extraForm_exact]

omit [DecidableEq Address] in
theorem weightedTotal_nonnegative (keys : List Address) (weights extra : Address → ℚ)
    (weightsNonnegative : ∀ key ∈ keys, 0 ≤ weights key)
    (quantities : ∀ key ∈ keys, 0 ≤ extra key) :
    0 ≤ weightedTotal keys weights extra := by
  apply List.sum_nonneg
  intro amount listed
  obtain ⟨key, source, rfl⟩ := List.mem_map.mp listed
  exact mul_nonneg (weightsNonnegative key source) (quantities key source)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup
