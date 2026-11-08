import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Rat

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

open scoped BigOperators

structure Inequality (n : ℕ) where
  coeff : Fin n → ℚ
  bound : ℚ

variable {n : ℕ}

def dot (coeff values : Fin n → ℚ) : ℚ :=
  ∑ i, coeff i * values i

def Inequality.Holds (row : Inequality n) (values : Fin n → ℚ) : Prop :=
  dot row.coeff values ≤ row.bound

def Feasible (rows : List (Inequality n)) (values : Fin n → ℚ) : Prop :=
  ∀ row ∈ rows, row.Holds values

inductive Result (rows : List (Inequality n)) where
  | feasible (values : Fin n → ℚ) (checked : Feasible rows values)
  | infeasible (impossible : ¬ ∃ values, Feasible rows values)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
