import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.State
import H0mework.Foundation.Responsibility.DebtWorld

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family

open Source.Program
open Innovation
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure OriginId where
  programme : Trials.Mechanism Party Good Port Technology Instrument
  past : List (RawEvent Party Good Port Technology Instrument)
  nature : programme.Nature
  response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)

variable {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Claim source past nature response)

def originalId (_claim : Claim source past nature response) : OriginId (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument) := ⟨source,past,nature,response⟩

inductive StepAt : State claim → State claim → Type
  | declaration (state : State claim) (pending : state.declared = false) :
      StepAt state (State.declare claim state)
  | paid (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
      (word : RawEvent Party Good Port Technology Instrument)
      (active : state.declared = true) (unpaid : ¬ State.isPaid claim state)
      (complete : State.isPaid claim (State.advance claim state actualLaw word)) :
      StepAt state (State.advance claim state actualLaw word)

inductive CarryAt : State claim → State claim → Type
  | identity (state : State claim) : CarryAt state state
  | actual (state : State claim) (actualLaw : RawLaw Party Good Port Technology Instrument)
      (word : RawEvent Party Good Port Technology Instrument) : CarryAt state (State.advance claim state actualLaw word)

/-- A failed full settlement retains one exact original cell, its unpaid material
and the actual request word; it never authorizes erasure of any other cell. -/
structure ObstructionAt (state : State claim) : Type where
  actualLaw : RawLaw Party Good Port Technology Instrument
  word : RawEvent Party Good Port Technology Instrument
  key : Party × Good
  original : key ∈ positiveScope source past nature response
  unpaid : 0 < (State.advance claim state actualLaw word).remaining key

def activationLaw : DebtActivationWorld.DebtActivationLaw where
  DebtState := State claim
  DebtId := OriginId (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  DebtClaim := Claim source past nature response
  debtId := originalId claim
  debtClaim := claim
  budget := State.budget claim
  StepAt := StepAt claim
  step_budget_lt step := by
    cases step with
    | declaration pending => exact State.declaration_strictly_reduces_its_phase_budget claim _ pending
    | paid actualLaw word active unpaid complete =>
      exact State.full_actual_payment_strictly_reduces_the_phase_budget claim _ actualLaw word active unpaid complete
  transportLaw? := some {
    EventAt := CarryAt claim
    budget_le carry := by
      cases carry with
      | identity => exact le_rfl
      | actual actualLaw word => exact State.actual_advance_never_increases_the_phase_budget claim _ actualLaw word }
  SettlementAt := State.SettledAt claim
  settlement_budget_zero := State.settlement_has_zero_local_phase_budget claim
  supportTerminalLaw? := none
  ObstructionAt := ObstructionAt claim

def declarationAt (raw : RawCurrent Party Good Technology Instrument) :
    (activationLaw claim).StepAt (State.atCursor claim raw) (State.declare claim (State.atCursor claim raw)) :=
  .declaration _ rfl

def identityTransport (state : State claim) : (activationLaw claim).TransportAt state state :=
  CarryAt.identity state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family
