import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Material

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family

open Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}

/-- One physical cursor carries the entire finite original harm matrix.
This is one law-owned native obligation, not one independently spendable cursor per cell. -/
structure State (claim : Claim source past nature response) : Type where
  private mk ::
  raw : RawCurrent Party Good Technology Instrument
  remaining : Party × Good → ℚ
  nonnegative : ∀ key, 0 ≤ remaining key
  outside : ∀ key, key ∉ positiveScope source past nature response → remaining key = 0
  declared : Bool

namespace State

variable (claim : Claim source past nature response)

def atCursor (raw : RawCurrent Party Good Technology Instrument) : State claim :=
  ⟨raw,(fun key => if key ∈ positiveScope source past nature response then quantity source past nature response key else 0),
    (by
      intro key
      split_ifs
      · exact le_max_left _ _
      · exact le_rfl),
    (by intro key absent; exact if_neg absent),false⟩

def declare (state : State claim) : State claim :=
  ⟨state.raw,state.remaining,state.nonnegative,state.outside,true⟩

def attempt (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :=
  inspectAttempt actualLaw state.raw (controllerCohort source past nature response)
    (positiveScope source past nature response) word

def advance (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : State claim :=
  ⟨(attempt claim state actualLaw word).cursor,
    (fun key => max 0 (state.remaining key - (attempt claim state actualLaw word).credit key)),
    (fun _ => le_max_left _ _),
    (by
      intro key absent
      have nonnegative := Attempt.credit_nonnegative (attempt claim state actualLaw word) key
      rw [state.outside key absent]
      apply max_eq_left
      linarith),state.declared⟩

def isPaid (state : State claim) : Prop :=
  ∀ key ∈ positiveScope source past nature response, state.remaining key = 0

instance (state : State claim) : Decidable (isPaid claim state) := by
  unfold isPaid
  infer_instance

def budget (state : State claim) : Nat := if state.declared then if isPaid claim state then 0 else 1 else 2

structure SettledAt (state : State claim) : Type where
  declared : state.declared = true
  paid : isPaid claim state

theorem admission_retains_every_original_harm (raw : RawCurrent Party Good Technology Instrument)
    (key : Party × Good) (positive : 0 < partyLoss source past nature response key.1 key.2) :
    (atCursor claim raw).remaining key = partyLoss source past nature response key.1 key.2 := by
  have member := every_positive_original_harm_is_in_the_generated_scope source past nature response key.1 key.2 positive
  change (if key ∈ positiveScope source past nature response then quantity source past nature response key else 0) = _
  rw [if_pos member]
  exact max_eq_right (le_of_lt positive)

theorem admission_remaining_is_the_positive_source_quantity (raw : RawCurrent Party Good Technology Instrument)
    (key : Party × Good) : (atCursor claim raw).remaining key = quantity source past nature response key := by
  change (if key ∈ positiveScope source past nature response then quantity source past nature response key else 0) = _
  by_cases member : key ∈ positiveScope source past nature response
  · exact if_pos member
  · rw [if_neg member]
    apply Eq.symm
    apply max_eq_left
    apply le_of_not_gt
    intro positive
    exact member (every_positive_original_harm_is_in_the_generated_scope source past nature response key.1 key.2 positive)

theorem atCursor_is_unpaid (raw : RawCurrent Party Good Technology Instrument) :
    ¬ isPaid claim (atCursor claim raw) := by
  have someKey : ∃ key, key ∈ positiveScope source past nature response := by
    cases original : positiveScope source past nature response with
    | nil => exact (claim.nonempty original).elim
    | cons key rest => exact ⟨key,List.mem_cons_self⟩
  obtain ⟨key,member⟩ := someKey
  have positive := of_decide_eq_true (List.mem_filter.mp member).2
  intro paid
  have zero := paid key member
  rw [admission_retains_every_original_harm claim raw key positive] at zero
  exact ne_of_gt positive zero

theorem declaration_preserves_every_material_cell (state : State claim) :
    (declare claim state).remaining = state.remaining ∧ (declare claim state).raw = state.raw := ⟨rfl,rfl⟩

theorem declaration_strictly_reduces_its_phase_budget (state : State claim)
    (pending : state.declared = false) : budget claim (declare claim state) < budget claim state := by
  by_cases paid : isPaid claim state
  · have nextPaid : isPaid claim (declare claim state) := paid
    simp only [budget,pending,Bool.false_eq_true,↓reduceIte]
    change (if isPaid claim (declare claim state) then 0 else 1) < 2
    rw [if_pos nextPaid]
    decide
  · have nextUnpaid : ¬ isPaid claim (declare claim state) := paid
    simp only [budget,pending,Bool.false_eq_true,↓reduceIte]
    change (if isPaid claim (declare claim state) then 0 else 1) < 2
    rw [if_neg nextUnpaid]
    decide

theorem actual_advance_never_refills_any_original_cell (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (key : Party × Good) :
    (advance claim state actualLaw word).remaining key ≤ state.remaining key := by
  apply max_le (state.nonnegative key)
  exact sub_le_self _ (Attempt.credit_nonnegative _ _)

theorem zero_cell_requires_sufficient_real_material (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (key : Party × Good)
    (zero : (advance claim state actualLaw word).remaining key = 0) :
    state.remaining key ≤ (attempt claim state actualLaw word).credit key := by
  have bounded := le_max_right (0 : ℚ) (state.remaining key - (attempt claim state actualLaw word).credit key)
  change max 0 (state.remaining key - (attempt claim state actualLaw word).credit key) = 0 at zero
  rw [zero] at bounded
  linarith

theorem actual_advance_never_increases_the_phase_budget (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    budget claim (advance claim state actualLaw word) ≤ budget claim state := by
  by_cases active : state.declared = true
  · by_cases paid : isPaid claim state
    · have nextPaid : isPaid claim (advance claim state actualLaw word) := by
        intro key member
        exact le_antisymm (by simpa only [paid key member] using
          actual_advance_never_refills_any_original_cell claim state actualLaw word key)
          ((advance claim state actualLaw word).nonnegative key)
      simp only [budget,advance,active,↓reduceIte,paid]
      change (if isPaid claim (advance claim state actualLaw word) then 0 else 1) ≤ 0
      rw [if_pos nextPaid]
    · simp only [budget,advance,active,↓reduceIte,paid]
      split_ifs <;> decide
  · simp only [budget,advance,active]
    exact le_rfl

theorem full_actual_payment_strictly_reduces_the_phase_budget (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (active : state.declared = true) (unpaid : ¬ isPaid claim state)
    (paid : isPaid claim (advance claim state actualLaw word)) :
    budget claim (advance claim state actualLaw word) < budget claim state := by
  simp only [budget,advance,active,↓reduceIte,unpaid]
  change (if isPaid claim (advance claim state actualLaw word) then 0 else 1) < 1
  rw [if_pos paid]
  decide

theorem settlement_has_zero_local_phase_budget {state : State claim} (settled : SettledAt claim state) :
    budget claim state = 0 := by
  simp only [budget,settled.declared,↓reduceIte,settled.paid]

theorem actual_advance_retains_every_original_financial_claim (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    (advance claim state actualLaw word).raw.claims = state.raw.claims := by
  change (attempt claim state actualLaw word).cursor.claims = state.raw.claims
  generalize attempt claim state actualLaw word = result
  cases result with
  | accepted valid source =>
    exact actual_family_reparation_preserves_every_original_financial_claim _ _ _ _ _ source
  | rejected item member invalid source =>
    exact actual_family_reparation_preserves_every_original_financial_claim _ _ _ _ _ source
  | foreign request member outside => rfl

end State
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family
