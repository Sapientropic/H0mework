import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Split

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation

open Source.Program

structure Working (Party Good : Type) where
  netProductive : Party × Good → ℚ
  gross : Entitlement.Duty.Key (Party := Party) (Good := Good) → ℚ
  gross_nonnegative : ∀ key, 0 ≤ gross key

def room {Party Good : Type} (old : Party × Good → ℚ) (work : Working Party Good) (key : Party × Good) : ℚ :=
  max 0 (old key - max 0 (work.netProductive key))

/-- Two restrictions of the same source calculation. The actual root always
selects actual readings; primitive readings support the resource calculation. -/
structure Readings (Party Good Port Technology Instrument : Type) where
  debit : ExecutionItem Party Good Port Technology Instrument → Flow Party Good
  credit : ExecutionItem Party Good Port Technology Instrument → Flow Party Good

namespace Kernel

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]

def incoming (readings : Readings Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) : ℚ :=
  max 0 (flowAt (readings.credit item) key.1 key.2)

def reservation (cohort : List Party) (positive : List (Party × Good))
    (readings : Readings Party Good Port Technology Instrument)
    (old : Party × Good → ℚ) (p : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) : ℚ :=
  if p = true ∧ key ∈ positive then
    match item.request.operation with
    | .transfer sender recipient _ =>
        if sender ∈ cohort ∧ recipient = key.1 then first (room old work key) (incoming readings item key) else 0
    | _ => 0
  else 0

def net (cohort : List Party) (positive : List (Party × Good))
    (readings : Readings Party Good Port Technology Instrument) (p : Bool)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) : ℚ :=
  if p = true ∧ key ∈ positive then
    let debit := flowAt (readings.debit item) key.1 key.2
    match item.request.operation with
    | .produce operator | .revise operator _ =>
        (if operator ∈ cohort then flowAt (readings.credit item) key.1 key.2 else 0) - debit
    | .transfer .. | .use .. => -debit
    | _ => 0
  else 0

def gross (cohort : List Party) (positive : List (Party × Good))
    (scope : List (Entitlement.Duty.Key (Party := Party) (Good := Good)))
    (readings : Readings Party Good Port Technology Instrument)
    (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) : ℚ :=
  if g = true ∧ key ∈ scope then
    match item.request.operation with
    | .transfer sender recipient _ =>
        if sender = key.2.1 ∧ recipient = key.1 then
          min (work.gross key) (max 0 (incoming readings item (key.1,key.2.2) -
            reservation cohort positive readings old p work item (key.1,key.2.2))) else 0
    | _ => 0
  else 0

def productiveCredit (cohort : List Party) (positive : List (Party × Good))
    (scope : List (Entitlement.Duty.Key (Party := Party) (Good := Good)))
    (readings : Readings Party Good Port Technology Instrument)
    (old : Party × Good → ℚ) (p g : Bool) (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Party × Good) : ℚ :=
  if p = true ∧ key ∈ positive then
    match item.request.operation with
    | .transfer sender recipient _ =>
        if sender ∈ cohort ∧ recipient = key.1 then incoming readings item key -
          gross cohort positive scope readings old p g work item (recipient,sender,key.2) else 0
    | _ => 0
  else 0

theorem gross_nonnegative (cohort : List Party) (positive : List (Party × Good))
    (scope : List (Entitlement.Duty.Key (Party := Party) (Good := Good)))
    (readings : Readings Party Good Port Technology Instrument) (old : Party × Good → ℚ)
    (p g : Bool) (work : Working Party Good) (item : ExecutionItem Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    0 ≤ gross cohort positive scope readings old p g work item key := by
  unfold gross
  split
  · split <;> try exact le_rfl
    split
    · exact le_min (work.gross_nonnegative key) (le_max_left _ _)
    · exact le_rfl
  · exact le_rfl

def after (cohort : List Party) (positive : List (Party × Good))
    (scope : List (Entitlement.Duty.Key (Party := Party) (Good := Good)))
    (readings : Readings Party Good Port Technology Instrument) (old : Party × Good → ℚ)
    (p g : Bool) (work : Working Party Good) (item : ExecutionItem Party Good Port Technology Instrument) :
    Working Party Good where
  netProductive := fun key => work.netProductive key + net cohort positive readings p item key +
    productiveCredit cohort positive scope readings old p g work item key
  gross := fun key => max 0 (work.gross key - gross cohort positive scope readings old p g work item key)
  gross_nonnegative := fun _ => le_max_left _ _

end Kernel
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation
