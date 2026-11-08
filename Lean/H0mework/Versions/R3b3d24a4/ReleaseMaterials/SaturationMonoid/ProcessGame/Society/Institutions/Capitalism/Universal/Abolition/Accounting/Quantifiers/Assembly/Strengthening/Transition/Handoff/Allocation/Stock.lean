import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Affine
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.Opening

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
open Reserve

variable {n : ℕ} {Row Address Item : Type*} [DecidableEq Address]

def heldForm (rows : List Row) (address : Row → Address) (key : Address) (remaining : Row → Affine n) :
    Affine n :=
  Affine.sum (rows.map fun row => if address row = key then remaining row else Affine.literal 0)

theorem heldForm_eval (rows : List Row) (address : Row → Address) (key : Address)
    (remaining : Row → Affine n) (values : Fin n → ℚ) :
    (heldForm rows address key remaining).eval values =
      held rows address (fun row => (remaining row).eval values) key := by
  simp only [heldForm, Affine.eval_sum, List.map_map, held, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro row _
  by_cases same : address row = key <;> simp [atAddress, same]

def paidSteps (steps : List (Step Row Address Item)) (pay : Item → Row → Affine n) (values : Fin n → ℚ) :
    List (Step Row Address Item) :=
  steps.map fun step => { step with paid := fun row => (pay step.item row).eval values }

/-- Both the reserved stock and the gross debit must fit before the
current item's credit. Only allocations to held rows release their stock. -/
def stockConstraintsFor (rows : List Row) (address : Row → Address) (key : Address)
    (pay : Item → Row → Affine n) :
    List (Step Row Address Item) → (Row → Affine n) → Affine n → List (Inequality n)
  | [], remaining, stock =>
    [Affine.le (Affine.literal 0) stock, Affine.le (heldForm rows address key remaining) stock]
  | step :: rest, remaining, stock =>
    let after := fun row => (remaining row).sub (pay step.item row)
    Affine.le (Affine.literal 0) stock ::
    Affine.le (heldForm rows address key remaining) stock ::
    Affine.le (Affine.literal (step.debit key)) stock ::
    Affine.le ((Affine.literal (step.debit key)).add (heldForm rows address key after)) stock ::
    stockConstraintsFor rows address key pay rest after
      ((stock.add (Affine.literal (step.credit key))).sub (Affine.literal (step.debit key)))

theorem stockConstraintsFor_exact (rows : List Row) (address : Row → Address) (key : Address)
    (steps : List (Step Row Address Item)) (pay : Item → Row → Affine n) (remaining : Row → Affine n)
    (stock : Affine n) (values : Fin n → ℚ) :
    Feasible (stockConstraintsFor rows address key pay steps remaining stock) values ↔
      Protects rows address key (paidSteps steps pay values)
        (fun row => (remaining row).eval values) (stock.eval values) := by
  induction steps generalizing remaining stock with
  | nil => simp [stockConstraintsFor, feasible_cons, paidSteps, Protects, heldForm_eval]
  | cons step rest ih =>
    simp only [stockConstraintsFor, feasible_cons, Affine.holds_le, Affine.eval_literal, Affine.eval_add,
      heldForm_eval, Affine.eval_sub, paidSteps, List.map_cons, Protects, Step.balance, ih]
    rfl

def stockConstraints (rows : List Row) (address : Row → Address) (key : Address)
    (pay : Item → Row → Affine n) (steps : List (Step Row Address Item)) (remaining : Row → Affine n)
    (stock : ℚ) : List (Inequality n) :=
  stockConstraintsFor rows address key pay steps remaining (Affine.literal stock)

theorem stockConstraints_exact (rows : List Row) (address : Row → Address) (key : Address)
    (steps : List (Step Row Address Item)) (pay : Item → Row → Affine n) (remaining : Row → Affine n)
    (stock : ℚ) (values : Fin n → ℚ) :
    Feasible (stockConstraints rows address key pay steps remaining stock) values ↔
      Protects rows address key (paidSteps steps pay values) (fun row => (remaining row).eval values) stock := by
  simpa only [stockConstraints, Affine.eval_literal] using
    stockConstraintsFor_exact rows address key steps pay remaining (Affine.literal stock) values

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation
