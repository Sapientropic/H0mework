import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty.Scope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty

open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {window : Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}

/-- Material balances live in the shared root current. This row stores only
its own allocated unpaid amounts, never a second spendable raw cursor. -/
structure State (claim : Source.Claim window) where
  private mk ::
  declared : Bool
  remaining : Key (Party := Party) (Good := Good) → ℚ
  nonnegative : ∀ key, 0 ≤ remaining key

namespace State
variable (claim : Source.Claim window)

def initial : State claim := ⟨false,quantity window,by
  intro key
  apply List.sum_nonneg
  intro amount listed
  obtain ⟨demand,_,rfl⟩ := List.mem_map.mp listed
  exact demand.leg.quantity_positive.le⟩

def declare (state : State claim) : State claim := { state with declared := true }

def isPaid (state : State claim) : Prop := ∀ key ∈ scope window, state.remaining key = 0

instance (state : State claim) : Decidable (isPaid claim state) := by unfold isPaid; infer_instance

/-- Only the accepted original refund instruction supplies gross credit.
A later settlement changes its own financial claim, not this earlier credit. -/
def credit (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Key (Party := Party) (Good := Good)) : ℚ :=
  if law.Valid item.before item.request then
    match item.request.operation with
    | .transfer sender recipient goods =>
        if sender = key.2.1 ∧ recipient = key.1 then max 0 (amount Good goods key.2.2) else 0
    | _ => 0
  else 0

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem credit_nonnegative (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Key (Party := Party) (Good := Good)) :
    0 ≤ credit law item key := by
  unfold credit
  split
  · split <;> try exact le_rfl
    split
    · exact le_max_left _ _
    · exact le_rfl
  · exact le_rfl

def afterItem (state : State claim) (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) : State claim :=
  ⟨state.declared,(fun key => max 0 (state.remaining key - credit law item key)),fun _ => le_max_left _ _⟩

def advance (state : State claim) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) : State claim :=
  (law.rawItems before word).foldl (fun prior item => afterItem claim prior law item) state

theorem after_item_never_refills (state : State claim) (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (key : Key (Party := Party) (Good := Good)) :
    (afterItem claim state law item).remaining key ≤ state.remaining key :=
  max_le (state.nonnegative key) (sub_le_self _ (credit_nonnegative law item key))

theorem advance_never_refills (state : State claim) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (key : Key (Party := Party) (Good := Good)) :
    (advance claim state law before word).remaining key ≤ state.remaining key := by
  unfold advance
  generalize law.rawItems before word = items
  induction items generalizing state with
  | nil => exact le_rfl
  | cons item rest inherited =>
      exact (inherited (afterItem claim state law item)).trans (after_item_never_refills claim state law item key)

theorem advance_keeps_declaration (state : State claim) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) :
    (advance claim state law before word).declared = state.declared := by
  unfold advance
  generalize law.rawItems before word = items
  induction items generalizing state with
  | nil => rfl
  | cons item rest inherited => exact inherited (afterItem claim state law item)

theorem actual_payment_does_not_reopen_a_paid_row (state : State claim) (paid : isPaid claim state)
    (law : RawLaw Party Good Port Technology Instrument) (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : isPaid claim (advance claim state law before word) := by
  intro key original
  exact le_antisymm ((advance_never_refills claim state law before word key).trans (paid key original).le)
    ((advance claim state law before word).nonnegative key)

theorem initial_is_unpaid : ¬ isPaid claim (initial claim) := by
  obtain ⟨key,original,positive⟩ := the_original_claim_has_a_positive_group window claim
  intro paid
  exact (ne_of_gt positive) (paid key original)

end State
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty
