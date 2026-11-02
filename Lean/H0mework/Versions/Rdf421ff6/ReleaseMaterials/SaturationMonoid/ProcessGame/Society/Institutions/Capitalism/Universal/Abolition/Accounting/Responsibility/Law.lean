import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.State
import H0mework.Foundation.Responsibility.DebtWorld

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility

open Source.Program
open Innovation
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- The same source programme, actual past, nature and response retain the original
beneficiary and material; subsequent ownership or presentation is absent from this key. -/
structure OriginId where
  programme : Trials.Mechanism Party Good Port Technology Instrument
  past : List (RawEvent Party Good Port Technology Instrument)
  nature : programme.Nature
  response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  beneficiary : Party
  good : Good

variable {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {party : Party} {good : Good}
  (claim : AssessedClaim source past nature response party good)

def originalId (_claim : AssessedClaim source past nature response party good) : OriginId (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨source,past,nature,response,party,good⟩

/-- Admission advances declaration, while discharge requires the actual, fully paid
material operation; declaring the obligation cannot reduce its material quantity. -/
inductive StepAt : State claim → State claim → Type
  | declaration (state : State claim) (pending : state.declared = false) :
      StepAt state (State.declare claim state)
  | paid (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
      (word : RawEvent Party Good Port Technology Instrument)
      (active : state.declared = true) (positive : 0 < state.remaining)
      (zero : (State.advance claim state actualLaw word).remaining = 0) :
      StepAt state (State.advance claim state actualLaw word)

/-- Ordinary actual continuation keeps the original row, including partial payments
and unsuccessful requests; it cannot mint a new debt identity or refill its quantity. -/
inductive CarryAt : State claim → State claim → Type
  | identity (state : State claim) : CarryAt state state
  | actual (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
      (word : RawEvent Party Good Port Technology Instrument) :
      CarryAt state (State.advance claim state actualLaw word)

theorem actual_carry_never_increases_the_phase_budget (state : State claim)
    (actualLaw : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    State.budget claim (State.advance claim state actualLaw word) ≤ State.budget claim state := by
  by_cases active : state.declared = true
  · by_cases zero : state.remaining = 0
    · have nextZero : (State.advance claim state actualLaw word).remaining = 0 :=
        le_antisymm (by simpa only [zero] using State.actual_advance_never_refills_the_original_obligation claim state actualLaw word)
          (State.advance claim state actualLaw word).nonnegative
      simp [State.budget,State.advance,active,zero] at nextZero ⊢
      exact nextZero
    · simp only [State.budget,State.advance,active,↓reduceIte,zero]
      split_ifs <;> decide
  · simp only [State.budget,State.advance,active]
    exact le_rfl

structure ObstructionAt (state : State claim) : Type where
  actualLaw : RawLaw Party Good Port Technology Instrument
  word : RawEvent Party Good Port Technology Instrument
  unpaid : 0 < (State.advance claim state actualLaw word).remaining

/-- This coface law admits one compulsory original-source obligation without
manufacturing a voluntary financial claim.  Local zero is never a world terminal. -/
def activationLaw : DebtActivationWorld.DebtActivationLaw where
  DebtState := State claim
  DebtId := OriginId (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  DebtClaim := AssessedClaim source past nature response party good
  debtId := originalId claim
  debtClaim := claim
  budget := State.budget claim
  StepAt := StepAt claim
  step_budget_lt step := by
    cases step with
    | declaration pending => exact State.declaration_strictly_reduces_its_phase_budget claim _ pending
    | paid actualLaw word active positive zero =>
      exact State.full_actual_payment_strictly_reduces_the_phase_budget claim _ actualLaw word active positive zero
  transportLaw? := some {
    EventAt := CarryAt claim
    budget_le carry := by
      cases carry with
      | identity => exact le_rfl
      | actual actualLaw word => exact actual_carry_never_increases_the_phase_budget claim _ actualLaw word }
  SettlementAt := State.SettledAt claim
  settlement_budget_zero := State.settlement_is_locally_zero claim
  supportTerminalLaw? := none
  ObstructionAt := ObstructionAt claim

def initialDeclaration : (activationLaw claim).StepAt (State.initial claim)
    (State.declare claim (State.initial claim)) := .declaration _ rfl

theorem initial_declaration_retains_the_unpaid_material :
    (State.declare claim (State.initial claim)).remaining = claim.quantity := rfl

def identityTransport (state : State claim) : (activationLaw claim).TransportAt state state :=
  CarryAt.identity state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility
