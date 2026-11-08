import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity

open scoped BigOperators

/-- Finite readers of the original due rows and original material ordinals.
The payment matrix only assigns parts of already debited material. -/
structure Profile (Address Row Item : Type*) where
  start : ℚ
  opening : Address → ℚ
  commit : Item → ℚ
  credit : Item → Address → ℚ
  debit : Item → Address → ℚ
  address : Row → Address
  deadline : Row → ℚ
  required : Row → ℚ
  paid : Row → Item → ℚ

namespace Profile

variable {Address Row Item : Type*}
variable [Fintype Row] [Fintype Item] [DecidableEq Address]

def credited (view : Profile Address Row Item) (time : ℚ) (address : Address) : ℚ :=
  ∑ item, if view.commit item ≤ time then view.credit item address else 0

def debited (view : Profile Address Row Item) (time : ℚ) (address : Address) : ℚ :=
  ∑ item, if view.commit item ≤ time then view.debit item address else 0

def actualStock (view : Profile Address Row Item) (time : ℚ) (address : Address) : ℚ :=
  view.opening address + view.credited time address - view.debited time address

def paidThrough (view : Profile Address Row Item) (time : ℚ) (row : Row) : ℚ :=
  ∑ item, if view.commit item ≤ time ∧ view.commit item ≤ view.deadline row then view.paid row item else 0

def outstandingDue (view : Profile Address Row Item) (time : ℚ) (address : Address) : ℚ :=
  ∑ row, if view.address row = address ∧ view.deadline row ≤ time then
    view.required row - view.paidThrough time row else 0

def grossDue (view : Profile Address Row Item) (time : ℚ) (address : Address) : ℚ :=
  ∑ row, if view.address row = address ∧ view.deadline row ≤ time then view.required row else 0

def chargedAt (view : Profile Address Row Item) (time : ℚ) (address : Address) (item : Item) : ℚ :=
  ∑ row, if view.address row = address ∧ view.deadline row ≤ time ∧ view.commit item ≤ view.deadline row
    then view.paid row item else 0

def otherDebits (view : Profile Address Row Item) (time : ℚ) (address : Address) : ℚ :=
  ∑ item, if view.commit item ≤ time then view.debit item address - view.chargedAt time address item else 0

def gap (view : Profile Address Row Item) (time : ℚ) (address : Address) : ℚ :=
  view.outstandingDue time address - view.actualStock time address

private theorem split_due (view : Profile Address Row Item) (time : ℚ) (address : Address) :
    view.outstandingDue time address =
      view.grossDue time address -
      ∑ row, if view.address row = address ∧ view.deadline row ≤ time then view.paidThrough time row else 0 := by
  unfold outstandingDue grossDue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro row _
  by_cases due : view.address row = address ∧ view.deadline row ≤ time <;> simp [due]

private theorem transpose_payment (view : Profile Address Row Item) (time : ℚ) (address : Address) :
    (∑ row, if view.address row = address ∧ view.deadline row ≤ time then view.paidThrough time row else 0) =
      ∑ item, if view.commit item ≤ time then view.chargedAt time address item else 0 := by
  unfold paidThrough chargedAt
  have distributed (row : Row) :
      (if view.address row = address ∧ view.deadline row ≤ time then
        ∑ item, if view.commit item ≤ time ∧ view.commit item ≤ view.deadline row then view.paid row item else 0
      else 0) =
        ∑ item, if view.address row = address ∧ view.deadline row ≤ time then
          (if view.commit item ≤ time ∧ view.commit item ≤ view.deadline row then view.paid row item else 0)
        else 0 := by
    by_cases due : view.address row = address ∧ view.deadline row ≤ time <;> simp [due]
  simp_rw [distributed]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro item _
  by_cases commit : view.commit item ≤ time
  · simp only [if_pos commit]
    apply Finset.sum_congr rfl
    intro row _
    by_cases due : view.address row = address ∧ view.deadline row ≤ time
    · simp [commit, due.1, due.2]
    · simp [due, ← and_assoc]
  · simp [commit]

/-- A receipt used for an original due row is charged exactly once. -/
theorem same_due_receipt_is_not_charged_twice (view : Profile Address Row Item) (time : ℚ) (address : Address) :
    view.gap time address =
      view.grossDue time address + view.otherDebits time address -
        view.opening address - view.credited time address := by
  unfold gap actualStock otherDebits debited
  rw [split_due, transpose_payment]
  have difference :
      (∑ item, ((if view.commit item ≤ time then view.debit item address else 0) -
        (if view.commit item ≤ time then view.chargedAt time address item else 0))) =
      ∑ item, if view.commit item ≤ time then view.debit item address - view.chargedAt time address item else 0 := by
    apply Finset.sum_congr rfl
    intro item _
    by_cases commit : view.commit item ≤ time <;> simp [commit]
  rw [← difference, Finset.sum_sub_distrib]
  ring

end Profile

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity
