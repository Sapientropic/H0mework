import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Unfolding.Budget
import H0mework.Foundation.Responsibility.DebtWorld

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Gross

open Source.Program Innovation
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

inductive Step : Current seed claim → Current seed claim → Type
  | declaration (current : Current seed claim) (pending : current.grossDeclared = false) :
      Step current (Current.declareGross seed claim current)
  | paid (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
      (active : current.grossDeclared = true)
      (unpaid : ¬ Current.grossPaid seed claim current)
      (paid : Current.grossPaid seed claim (Current.advance seed claim current word)) :
      Step current (Current.advance seed claim current word)

inductive Carry : Current seed claim → Current seed claim → Type
  | identity (current : Current seed claim) : Carry current current
  | actual (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :
      Carry current (Current.advance seed claim current word)

structure SettledAt (current : Current seed claim) : Type where
  active : current.grossDeclared = true
  paid : Current.grossPaid seed claim current

structure ObstructionAt (current : Current seed claim) : Type where
  key : Entitlement.Duty.Key (Party := Party) (Good := Good)
  original : key ∈ Entitlement.Duty.scope (window seed)
  unpaid : 0 < current.gross key

private theorem declaration_decreases (current : Current seed claim)
    (pending : current.grossDeclared = false) :
    Current.grossBudget seed claim (Current.declareGross seed claim current) <
      Current.grossBudget seed claim current := by
  unfold Current.grossBudget Current.declareGross
  simp only [pending,Bool.false_eq_true,if_false,if_true]
  split <;> decide

def law : DebtActivationWorld.DebtActivationLaw where
  DebtState := Current seed claim
  DebtId := (Entitlement.Duty.activationLaw claim).DebtId
  DebtClaim := (Entitlement.Duty.activationLaw claim).DebtClaim
  debtId := (Entitlement.Duty.activationLaw claim).debtId
  debtClaim := (Entitlement.Duty.activationLaw claim).debtClaim
  budget := Current.grossBudget seed claim
  StepAt := Step seed claim
  step_budget_lt := by
    intro source target step
    cases step with
    | declaration pending => exact declaration_decreases seed claim source pending
    | paid word active unpaid paid =>
        simp only [Current.grossBudget,
          (Current.actual_word_retains_declarations seed claim source word).2,
          active,if_true,unpaid,paid,if_false]
        decide
  transportLaw? := some {
    EventAt := Carry seed claim
    budget_le := by
      intro source target carry
      cases carry with
      | identity => exact le_rfl
      | actual word => exact Current.actual_word_never_increases_gross_budget seed claim source word }
  SettlementAt := SettledAt seed claim
  settlement_budget_zero := fun settled => by
    simp only [Current.grossBudget,settled.active,if_true,settled.paid]
  supportTerminalLaw? := none
  ObstructionAt := ObstructionAt seed claim

def declaration : (law seed claim).StepAt (Current.initial seed claim)
    (Current.declareGross seed claim (Current.initial seed claim)) := Step.declaration _ rfl

def actual (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :
    (law seed claim).TransportAt current (Current.advance seed claim current word) := Carry.actual current word

theorem the_new_row_retains_the_original_cause_identity :
    (law seed claim).debtId = (Entitlement.Duty.activationLaw claim).debtId ∧
      (law seed claim).debtClaim = claim := ⟨rfl,rfl⟩

theorem declaration_is_not_payment :
    (Current.declareGross seed claim (Current.initial seed claim)).raw = currentRaw seed ∧
      (Current.declareGross seed claim (Current.initial seed claim)).productive = (productiveState seed).remaining ∧
      (Current.declareGross seed claim (Current.initial seed claim)).gross =
        (Entitlement.Duty.State.initial claim).remaining := ⟨rfl,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Gross
