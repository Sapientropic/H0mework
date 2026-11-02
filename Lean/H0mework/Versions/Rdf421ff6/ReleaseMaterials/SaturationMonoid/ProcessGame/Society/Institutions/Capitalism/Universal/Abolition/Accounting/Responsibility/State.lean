import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Reparation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility

open Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {party : Party} {good : Good}

/-- A cache of the original physical cursor and its one source-assessed obligation.
The owning root retains the complete history and all other responsibility rows. -/
structure State (claim : AssessedClaim source past nature response party good) : Type where
  private mk ::
  raw : RawCurrent Party Good Technology Instrument
  remaining : ℚ
  nonnegative : 0 ≤ remaining
  declared : Bool

namespace State

variable (claim : AssessedClaim source past nature response party good)

def atCursor (raw : RawCurrent Party Good Technology Instrument) : State claim :=
  ⟨raw,claim.quantity,le_of_lt claim.positive,false⟩

def initial : State claim :=
  atCursor claim (source.code.law.next source.code.initial (Control.responseWord source past nature response))

def declare (state : State claim) : State claim :=
  ⟨state.raw,state.remaining,state.nonnegative,true⟩

/-- The actual interpreter at this epoch supplies both the new physical cursor
and the material credit; neither a future quote nor a new financial promise pays. -/
def attempt (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :=
  reparationResult actualLaw state.raw (controllerCohort source past nature response) party word good

def advance (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : State claim :=
  ⟨actualLaw.next state.raw word,max 0 (state.remaining - (attempt claim state actualLaw word).credit),
    le_max_left _ _,state.declared⟩

def budget (state : State claim) : Nat :=
  if state.declared then if state.remaining = 0 then 0 else 1 else 2

structure SettledAt (state : State claim) : Type where
  declared : state.declared = true
  paid : state.remaining = 0

theorem initial_retains_the_original_physical_cursor :
    (initial claim).raw = source.code.law.next source.code.initial (Control.responseWord source past nature response) := rfl

theorem initial_quantity_is_the_source_productive_loss :
    (initial claim).remaining = partyLoss source past nature response party good := rfl

theorem declaration_does_not_pay_material (state : State claim) :
    (declare claim state).remaining = state.remaining ∧ (declare claim state).raw = state.raw := ⟨rfl,rfl⟩

theorem initial_budget : budget claim (initial claim) = 2 := rfl

theorem declaration_strictly_reduces_its_phase_budget (state : State claim)
    (pending : state.declared = false) : budget claim (declare claim state) < budget claim state := by
  by_cases zero : state.remaining = 0 <;> simp [budget,declare,pending,zero]

theorem actual_advance_keeps_the_same_physical_source (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    (advance claim state actualLaw word).raw = actualLaw.next state.raw word := rfl

theorem actual_advance_never_refills_the_original_obligation (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    (advance claim state actualLaw word).remaining ≤ state.remaining := by
  apply max_le state.nonnegative
  exact sub_le_self _ (ReparationResult.credit_nonnegative _)

theorem an_exact_blocker_preserves_the_whole_unpaid_quantity (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (issue : ReparationBlocker actualLaw state.raw (controllerCohort source past nature response) party word good)
    (blocked : attempt claim state actualLaw word = .blocked issue) :
    (advance claim state actualLaw word).remaining = state.remaining := by
  change max 0 (state.remaining - (attempt claim state actualLaw word).credit) = state.remaining
  rw [blocked]
  simpa only [ReparationResult.credit,sub_zero] using max_eq_right state.nonnegative

theorem zero_remaining_requires_actual_sufficient_material (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (zero : (advance claim state actualLaw word).remaining = 0) :
    state.remaining ≤ (attempt claim state actualLaw word).credit := by
  have bounded := le_max_right (0 : ℚ) (state.remaining - (attempt claim state actualLaw word).credit)
  change max 0 (state.remaining - (attempt claim state actualLaw word).credit) = 0 at zero
  rw [zero] at bounded
  linarith

theorem a_paid_positive_obligation_retains_every_original_financial_claim (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (positive : 0 < state.remaining)
    (zero : (advance claim state actualLaw word).remaining = 0) :
    (advance claim state actualLaw word).raw.claims = state.raw.claims := by
  exact reparation_keeps_every_original_claim actualLaw state.raw
    (controllerCohort source past nature response) party word good
    (attempt claim state actualLaw word)
    (lt_of_lt_of_le positive (zero_remaining_requires_actual_sufficient_material claim state actualLaw word zero))

theorem full_actual_payment_strictly_reduces_the_phase_budget (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (active : state.declared = true) (positive : 0 < state.remaining)
    (zero : (advance claim state actualLaw word).remaining = 0) :
    budget claim (advance claim state actualLaw word) < budget claim state := by
  have nonzero : state.remaining ≠ 0 := ne_of_gt positive
  simp only [budget,advance,active,↓reduceIte,nonzero]
  change (if (advance claim state actualLaw word).remaining = 0 then 0 else 1) < 1
  rw [if_pos zero]
  decide

theorem settlement_is_locally_zero {state : State claim} (settled : SettledAt claim state) :
    budget claim state = 0 := by
  simp only [budget,settled.declared,↓reduceIte,settled.paid]

end State
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility
