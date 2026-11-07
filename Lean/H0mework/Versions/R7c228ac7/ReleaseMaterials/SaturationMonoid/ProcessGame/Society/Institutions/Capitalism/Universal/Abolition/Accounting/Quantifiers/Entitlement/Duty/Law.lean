import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty.State
import H0mework.Foundation.Responsibility.DebtWorld

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty

open Source.Program ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {window : Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} (claim : Source.Claim window)

def budget (state : State claim) : Nat :=
  if state.declared then if State.isPaid claim state then 0 else 1 else 2

theorem actual_budget_never_increases (state : State claim) (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) :
    budget claim (State.advance claim state law before word) ≤ budget claim state := by
  cases active : state.declared with
  | false => simp only [budget,State.advance_keeps_declaration,active,Bool.false_eq_true,if_false,le_refl]
  | true =>
      by_cases paid : State.isPaid claim state
      · have after := State.actual_payment_does_not_reopen_a_paid_row claim state paid law before word
        simp only [budget,State.advance_keeps_declaration,active,if_true,paid,after,le_refl]
      · by_cases after : State.isPaid claim (State.advance claim state law before word) <;>
          simp only [budget,State.advance_keeps_declaration,active,if_true,paid,after,if_false] <;> decide

inductive StepAt : State claim → State claim → Type
  | declaration (state : State claim) (pending : state.declared = false) :
      StepAt state (State.declare claim state)
  | paid (state : State claim) (law : RawLaw Party Good Port Technology Instrument)
      (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
      (active : state.declared = true) (unpaid : ¬ State.isPaid claim state)
      (complete : State.isPaid claim (State.advance claim state law before word)) :
      StepAt state (State.advance claim state law before word)

inductive CarryAt : State claim → State claim → Type
  | identity (state : State claim) : CarryAt state state
  | actual (state : State claim) (law : RawLaw Party Good Port Technology Instrument)
      (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument) :
      CarryAt state (State.advance claim state law before word)

structure OriginId where
  input : ProgrammeSource.Input Party Good Port Technology Instrument
  physicalIndex : Nat

def originalId : OriginId (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  ⟨window.input,Financial.Installation.Cursor.lastExecutedIndex window.input window.cursor⟩

structure SettledAt (state : State claim) : Type where
  active : state.declared = true
  paid : State.isPaid claim state

structure ObstructionAt (state : State claim) where
  key : Key (Party := Party) (Good := Good)
  original : key ∈ scope window
  unpaid : 0 < state.remaining key

private theorem smallIte (condition : Prop) [Decidable condition] :
    (if condition then 0 else 1) < (2 : Nat) := by
  by_cases yes : condition <;> simp only [yes,if_true,if_false] <;> decide

def activationLaw : DebtActivationWorld.DebtActivationLaw where
  DebtState := State claim
  DebtId := OriginId (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  DebtClaim := Source.Claim window
  debtId := originalId (window := window)
  debtClaim := claim
  budget := budget claim
  StepAt := StepAt claim
  step_budget_lt := by
    intro source target step
    cases step with
    | declaration pending =>
        simp only [budget,State.declare,pending,Bool.false_eq_true,if_false,if_true]
        exact smallIte _
    | paid law before word active unpaid complete =>
        simp only [budget,State.advance_keeps_declaration,active,if_true,unpaid,complete,if_false]
        decide
  transportLaw? := some {
    EventAt := CarryAt claim
    budget_le := by
      intro source target carry
      cases carry with
      | identity => exact le_rfl
      | actual law before word => exact actual_budget_never_increases claim source law before word }
  SettlementAt := SettledAt claim
  settlement_budget_zero := fun settled => by simp only [budget,settled.active,if_true,settled.paid]
  supportTerminalLaw? := none
  ObstructionAt := ObstructionAt claim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty
