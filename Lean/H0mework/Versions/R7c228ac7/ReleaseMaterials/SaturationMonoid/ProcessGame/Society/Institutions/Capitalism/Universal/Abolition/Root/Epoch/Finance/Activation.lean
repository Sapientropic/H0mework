import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Instruction
import H0mework.Realization.Audit.DebtFirstWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Activation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtAdmissionFirstWrite
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  (before : (process input depth count).GeneratedState) (claim : Claim input depth count)

def admitted : (process input depth count).GeneratedState :=
  before.step (process input depth count) (.admit claim)

inductive State
  | pending
  | registered (account : (process input depth count).GeneratedState)
      (native : Nonempty ((process input depth count).Run (admitted input depth count before claim).current account.current))

def account : State input depth count before claim → (process input depth count).GeneratedState
  | .pending => before
  | .registered state _ => state

def first : State input depth count before claim := .registered (admitted input depth count before claim) ⟨.nil⟩

def rank : State input depth count before claim → Nat
  | .pending => 1
  | .registered _ _ => 0

inductive RegistrationStep : State input depth count before claim → State input depth count before claim → Type
  | execute : RegistrationStep .pending (first input depth count before claim)

/-- Continuation transports the original admission through a native Run;
registration does not manufacture a financial settlement receipt. -/
inductive SameDebtTransport : State input depth count before claim → State input depth count before claim → Type
  | unchanged (state : State input depth count before claim) : SameDebtTransport state state
  | actualInstruction (state : (process input depth count).GeneratedState)
      (prior : Nonempty ((process input depth count).Run (admitted input depth count before claim).current state.current))
      (origin : ActualItem input depth count) : SameDebtTransport (.registered state prior)
        (.registered ((consume input depth count origin state).next input depth count)
          (prior.map (fun run => run.concatRuns (process input depth count)
            ((consume input depth count origin state).transition input depth count))))

def SettlementAt : State input depth count before claim → Type
  | .pending => PEmpty
  | .registered state _ =>
      { archive : TerminalArchive (vocabulary input depth count) //
        state.current.slots[before.current.slots.length]? = some (.terminal archive) ∧
        archive.obligation.content = claim }

def ObstructionAt : State input depth count before claim → Type
  | .pending => PEmpty
  | .registered state _ =>
      { obligation : AdmittedObligation (vocabulary input depth count) //
        state.current.slots[before.current.slots.length]? = some (.live obligation) ∧
        obligation.content = claim }

def law : DebtActivationLaw where
  DebtState := State input depth count before claim
  DebtId := Origin input depth count
  DebtClaim := Claim input depth count
  debtId := claim.origin input depth count
  debtClaim := claim
  budget := rank input depth count before claim
  StepAt := RegistrationStep input depth count before claim
  step_budget_lt := fun step => by cases step; exact Nat.zero_lt_succ 0
  transportLaw? := some {
    EventAt := SameDebtTransport input depth count before claim
    budget_le := fun transport => by
      cases transport with
      | unchanged _ => exact Nat.le_refl _
      | actualInstruction _ _ _ => exact Nat.le_refl 0 }
  SettlementAt := SettlementAt input depth count before claim
  settlement_budget_zero := fun {state} receipt => by
    cases state with
    | pending => exact receipt.elim
    | registered _ _ => rfl
  ObstructionAt := ObstructionAt input depth count before claim

def firstStep : SourceFixedDebtAdmissionEventAt (law input depth count before claim) .pending :=
  .ofStep (RegistrationStep.execute (input := input) (depth := depth) (count := count) (before := before) (claim := claim))

theorem target_is_actual_native_admission :
    account input depth count before claim (firstStep input depth count before claim).target =
      admitted input depth count before claim := rfl

theorem first_slot_is_the_actual_original_loan :
    (account input depth count before claim (firstStep input depth count before claim).target).current.slots[before.current.slots.length]? = some (.live (admission input depth count claim).toObligation) :=
  (process input depth count).admit_target_slot claim

theorem first_principal_is_not_spent_on_registration :
    Financial.total input (admission input depth count claim).residual = claim.quantity input depth count := by
  cases claim with
  | inl original => exact Financial.initial_total input original
  | inr original =>
      change Financial.total input (claimInitial input depth count (.inr original)) = original.quantity
      rw [new_initial_balance_is_the_same_single]
      simp only [Financial.total, Finsupp.sum_single_index]

theorem registration_is_not_financial_settlement :
    ¬ Nonempty ((law input depth count before claim).SettlementAt (firstStep input depth count before claim).target) := by
  rintro ⟨archive, terminal, _⟩
  have live := first_slot_is_the_actual_original_loan input depth count before claim
  change (admitted input depth count before claim).current.slots[before.current.slots.length]? = _ at live
  rw [terminal] at live
  cases live

def registered_obstruction : (law input depth count before claim).ObstructionAt
    (firstStep input depth count before claim).target :=
  ⟨(admission input depth count claim).toObligation,
    first_slot_is_the_actual_original_loan input depth count before claim, by cases claim <;> rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Activation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Activation.target_is_actual_native_admission
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Activation.registration_is_not_financial_settlement
