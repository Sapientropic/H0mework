import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Origin
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A finite share map lives inside each original liability's residual.
Raw party keys are coordinates, not actors; their authority is supplied by
the original occurrence's generated birth handle.  No finite genesis list
limits who may subsequently acquire a source-authorized share. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped BigOperators

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev Holder (_input : ProgrammeSource.Input Party Good Port Technology Instrument) := Party

def holderParty (_input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (holder : Holder _input) : Party := holder

def holderIndex (_input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (party : Party) : Holder _input := party

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem holderParty_index (party : Party) : holderParty input (holderIndex input party) = party := rfl

abbrev Balance (_input : ProgrammeSource.Input Party Good Port Technology Instrument) := Party →₀ ℚ

private def addShare (_input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (balance : Balance _input) (holder : Holder _input) (quantity : ℚ) : Balance _input where
  support := (insert holder balance.support).filter
    (fun index => balance index + (if index = holder then quantity else 0) ≠ 0)
  toFun := fun index => balance index + if index = holder then quantity else 0
  mem_support_toFun := by
    intro index
    rw [Finset.mem_filter]
    constructor
    · exact And.right
    · intro present
      refine ⟨?_, present⟩
      by_cases same : index = holder
      · exact Finset.mem_insert.mpr (Or.inl same)
      · exact Finset.mem_insert.mpr (Or.inr (Finsupp.mem_support_iff.mpr
          (by simpa only [if_neg same, add_zero] using present)))

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
private theorem addShare_eq (balance : Balance input) (holder : Holder input) (quantity : ℚ) :
    addShare input balance holder quantity = balance + Finsupp.single holder quantity := by
  apply Finsupp.ext
  intro index
  simp [addShare, Finsupp.single_apply, eq_comm]

def initialBalance (claim : IssuedClaim input) : Balance input := addShare input 0 claim.holder claim.quantity

def total (_input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (balance : Balance _input) : ℚ := balance.sum (fun _ quantity => quantity)

def pay (_input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (balance : Balance _input) (holder : Holder _input) (quantity : ℚ) : Balance _input :=
  addShare _input balance holder (-quantity)

def assign (_input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (balance : Balance _input) (sender recipient : Holder _input) (quantity : ℚ) : Balance _input :=
  addShare _input (pay _input balance sender quantity) recipient quantity

def Nonnegative (_input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (balance : Balance _input) : Prop := ∀ holder, 0 ≤ balance holder

omit [DecidableEq Port] in
theorem initial_nonnegative (claim : IssuedClaim input) : Nonnegative input (initialBalance input claim) := by
  intro holder
  change 0 ≤ 0 + if holder = claim.holder then claim.quantity else 0
  rw [zero_add]
  split_ifs <;> first | exact claim.quantity_nonnegative input | exact le_refl _

omit [DecidableEq Port] in
theorem initial_total (claim : IssuedClaim input) : total input (initialBalance input claim) = claim.quantity := by
  unfold initialBalance total
  rw [addShare_eq, zero_add, Finsupp.sum_single_index rfl]

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem pay_total (balance : Balance input) (holder : Holder input) (quantity : ℚ) :
    total input (pay input balance holder quantity) = total input balance - quantity := by
  unfold total pay
  rw [addShare_eq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl]
  ring

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem assign_total (balance : Balance input) (sender recipient : Holder input) (quantity : ℚ) :
    total input (assign input balance sender recipient quantity) = total input balance := by
  change (addShare input (pay input balance sender quantity) recipient quantity).sum _ = _
  rw [addShare_eq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl]
  change total input (pay input balance sender quantity) + quantity = _
  rw [pay_total]
  ring

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem pay_apply (balance : Balance input) (holder : Holder input) (quantity : ℚ) (index : Party) :
    pay input balance holder quantity index = balance index - if index = holder then quantity else 0 := by
  change balance index + (if index = holder then -quantity else 0) = _
  split_ifs <;> ring

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem assign_apply (balance : Balance input) (sender recipient : Holder input)
    (quantity : ℚ) (index : Party) :
    assign input balance sender recipient quantity index =
      balance index - (if index = sender then quantity else 0) + if index = recipient then quantity else 0 := by
  change pay input balance sender quantity index + _ = _
  rw [pay_apply]

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem pay_nonnegative (balance : Balance input) (holder : Holder input) (quantity : ℚ)
    (before : Nonnegative input balance) (covered : quantity ≤ balance holder) :
    Nonnegative input (pay input balance holder quantity) := by
  intro index
  rw [pay_apply]
  by_cases same : index = holder
  · subst index
    simpa using sub_nonneg.mpr covered
  · simpa only [if_neg same, sub_zero] using before index

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem assign_nonnegative (balance : Balance input) (sender recipient : Holder input) (quantity : ℚ)
    (before : Nonnegative input balance) (positive : 0 ≤ quantity) (covered : quantity ≤ balance sender) :
    Nonnegative input (assign input balance sender recipient quantity) := by
  intro index
  have retained := pay_nonnegative input balance sender quantity before covered index
  change 0 ≤ pay input balance sender quantity index + (if index = recipient then quantity else 0)
  exact add_nonneg retained (by split_ifs <;> first | exact positive | exact le_refl _)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem zero_of_total_zero (balance : Balance input) (nonnegative : Nonnegative input balance)
    (cleared : total input balance = 0) : balance = 0 := by
  apply Finsupp.ext
  intro holder
  change balance holder = 0
  by_cases present : holder ∈ balance.support
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun index _ => nonnegative index)).mp cleared holder present
  · simpa only [Finsupp.mem_support_iff, not_not] using present

/-- A computable singleton uses the same source balance update as payments
and assignments; it does not add an admission or a settlement event. -/
def initialShare (holder : Holder input) (quantity : ℚ) : Balance input :=
  addShare input 0 holder quantity

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem initialShare_eq_single (holder : Holder input) (quantity : ℚ) :
    initialShare input holder quantity = Finsupp.single holder quantity := by
  rw [initialShare, addShare_eq, zero_add]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
