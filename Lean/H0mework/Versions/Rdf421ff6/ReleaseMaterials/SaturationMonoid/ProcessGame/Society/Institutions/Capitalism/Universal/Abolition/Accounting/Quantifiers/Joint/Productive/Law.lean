import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Unfolding.Budget
import H0mework.Foundation.Responsibility.DebtWorld

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Productive

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
  (grossClaim : Entitlement.Source.Claim (window seed))

abbrev oldLaw := Responsibility.Family.activationLaw seed.claim

/-- The legacy cache survives as history. Current states refer to the one
joint cursor; callers may not use the old Family API as a spending pool. -/
inductive State
  | legacy (old : (oldLaw seed).DebtState)
  | current (shared : Current seed grossClaim)

def backward : State seed grossClaim → (oldLaw seed).DebtState
  | .legacy old => old
  | .current _ => productiveState seed

def stateRetract : ConstructiveRetract (oldLaw seed).DebtState (State seed grossClaim) :=
  ⟨State.legacy,backward seed grossClaim,fun _ => rfl⟩

def budget : State seed grossClaim → Nat
  | .legacy old => (oldLaw seed).budget old
  | .current shared => Current.productiveBudget seed grossClaim shared

inductive Step : State seed grossClaim → State seed grossClaim → Type
  | legacy {source target : (oldLaw seed).DebtState} (step : (oldLaw seed).StepAt source target) :
      Step (.legacy source) (.legacy target)
  | paid (shared : Current seed grossClaim) (word : RawEvent Party Good Port Technology Instrument)
      (active : shared.productiveDeclared = true)
      (unpaid : ¬ Current.productivePaid seed grossClaim shared)
      (paid : Current.productivePaid seed grossClaim (Current.advance seed grossClaim shared word)) :
      Step (.current shared) (.current (Current.advance seed grossClaim shared word))

inductive Transport : State seed grossClaim → State seed grossClaim → Type
  | legacy {source target : (oldLaw seed).DebtState} (transport : (oldLaw seed).TransportAt source target) :
      Transport (.legacy source) (.legacy target)
  | enter : Transport (.legacy (productiveState seed)) (.current (Current.initial seed grossClaim))
  | declareGross (shared : Current seed grossClaim) :
      Transport (.current shared) (.current (Current.declareGross seed grossClaim shared))
  | actual (shared : Current seed grossClaim) (word : RawEvent Party Good Port Technology Instrument) :
      Transport (.current shared) (.current (Current.advance seed grossClaim shared word))
  | identity (state : State seed grossClaim) : Transport state state

structure CurrentSettled (shared : Current seed grossClaim) : Type where
  active : shared.productiveDeclared = true
  paid : Current.productivePaid seed grossClaim shared

def SettlementAt : State seed grossClaim → Type
  | .legacy old => (oldLaw seed).SettlementAt old
  | .current shared => CurrentSettled seed grossClaim shared

structure CurrentObstruction (shared : Current seed grossClaim) : Type where
  key : Party × Good
  original : key ∈ Responsibility.Family.positiveScope mechanism past nature response
  unpaid : 0 < shared.productive key

def ObstructionAt : State seed grossClaim → Type
  | .legacy old => (oldLaw seed).ObstructionAt old
  | .current shared => CurrentObstruction seed grossClaim shared

def law : DebtActivationWorld.DebtActivationLaw where
  DebtState := State seed grossClaim
  DebtId := (oldLaw seed).DebtId
  DebtClaim := (oldLaw seed).DebtClaim
  debtId := (oldLaw seed).debtId
  debtClaim := (oldLaw seed).debtClaim
  budget := budget seed grossClaim
  StepAt := Step seed grossClaim
  step_budget_lt := fun step => by cases step with
    | legacy original => exact (oldLaw seed).step_budget_lt original
    | paid shared word active unpaid paid =>
        simp only [budget,Current.productiveBudget,
          (Current.actual_word_retains_declarations seed grossClaim shared word).1,
          active,if_true,unpaid,paid,if_false]
        decide
  transportLaw? := some {
    EventAt := Transport seed grossClaim
    budget_le := fun transport => by
      cases transport with
      | legacy original => exact (oldLaw seed).transport_budget_le original
      | enter => exact (Current.the_productive_initial_budget_is_literal seed grossClaim).le
      | declareGross shared => exact le_rfl
      | actual shared word => exact Current.actual_word_never_increases_productive_budget seed grossClaim shared word
      | identity state => exact le_rfl }
  SettlementAt := SettlementAt seed grossClaim
  settlement_budget_zero := fun {state} settled => by
    cases state with
    | legacy old => exact (oldLaw seed).settlement_budget_zero settled
    | current shared =>
        simp only [budget,Current.productiveBudget,settled.active,if_true,settled.paid]
  supportTerminalLaw? := none
  ObstructionAt := ObstructionAt seed grossClaim

theorem original_identity_and_claim_are_literal :
    (law seed grossClaim).debtId = (oldLaw seed).debtId ∧
      (law seed grossClaim).debtClaim = (oldLaw seed).debtClaim := ⟨rfl,rfl⟩

theorem every_legacy_budget_is_literal (old : (oldLaw seed).DebtState) :
    (law seed grossClaim).budget (.legacy old) = (oldLaw seed).budget old := rfl

def enter : (law seed grossClaim).TransportAt (.legacy (productiveState seed))
    (.current (Current.initial seed grossClaim)) := Transport.enter

def actual (shared : Current seed grossClaim) (word : RawEvent Party Good Port Technology Instrument) :
    (law seed grossClaim).TransportAt (.current shared)
      (.current (Current.advance seed grossClaim shared word)) := Transport.actual shared word

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Productive
