import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Instruction
import H0mework.Realization.Audit.DebtFirstWrite

/-! The activation rank counts the one unexecuted registration instruction.
Its actual step is the native admission append.  Financial principal stays
in the original slot; reaching rank zero is not a settlement receipt. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Activation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtAdmissionFirstWrite

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : (process input).GeneratedState) (claim : IssuedClaim input)

inductive State
  | pending
  | registered (account : (process input).GeneratedState)
      (native : Nonempty ((process input).Run (admit input before claim).current account.current))

def account : State input before claim → (process input).GeneratedState
  | .pending => before
  | .registered account _ => account

def first : State input before claim := .registered (admit input before claim) ⟨.nil⟩

def rank : State input before claim → Nat
  | .pending => 1
  | .registered _ _ => 0

inductive RegistrationStep : State input before claim → State input before claim → Type
  | execute : RegistrationStep .pending (first input before claim)

def afterMovement (state : (process input).GeneratedState)
    (native : Nonempty ((process input).Run (admit input before claim).current state.current))
    (origin : InstructionOrigin input) (movement : Movement input origin) : State input before claim :=
  let allocation := allocate input origin state movement.quantity (movement.quantity_nonnegative input)
  .registered allocation.after (native.map (fun prior => prior.concatRuns (process input) allocation.transition))

def afterAdmission (state : (process input).GeneratedState)
    (native : Nonempty ((process input).Run (admit input before claim).current state.current))
    (newClaim : IssuedClaim input) : State input before claim :=
  .registered (admit input state newClaim) (native.map (fun prior => .step prior (.admit newClaim)))

inductive SameDebtTransport : State input before claim → State input before claim → Type
  | unchanged (state : State input before claim) : SameDebtTransport state state
  | movement (state : (process input).GeneratedState)
      (native : Nonempty ((process input).Run (admit input before claim).current state.current))
      (origin : InstructionOrigin input) (source : Movement input origin) :
      SameDebtTransport (.registered state native)
        (afterMovement input before claim state native origin source)
  | anotherAdmission (state : (process input).GeneratedState)
      (native : Nonempty ((process input).Run (admit input before claim).current state.current))
      (newClaim : IssuedClaim input) :
      SameDebtTransport (.registered state native)
        (afterAdmission input before claim state native newClaim)

def SettlementAt : State input before claim → Type
  | .pending => PEmpty
  | .registered state _ =>
      { archive : TerminalArchive (vocabulary input) //
        state.current.slots[before.current.slots.length]? = some (.terminal archive) ∧
        archive.obligation.content = claim }

def ObstructionAt : State input before claim → Type
  | .pending => PEmpty
  | .registered state _ =>
      { obligation : AdmittedObligation (vocabulary input) //
        state.current.slots[before.current.slots.length]? = some (.live obligation) ∧
        obligation.content = claim }

def law : DebtActivationLaw where
  DebtState := State input before claim
  DebtId := InstructionOrigin input
  DebtClaim := IssuedClaim input
  debtId := claim.origin
  debtClaim := claim
  budget := rank input before claim
  StepAt := RegistrationStep input before claim
  step_budget_lt := fun step => by cases step; exact Nat.zero_lt_succ 0
  transportLaw? := some {
    EventAt := SameDebtTransport input before claim
    budget_le := fun transport => by
      cases transport with
      | unchanged state => exact Nat.le_refl _
      | movement _ _ _ _ => exact Nat.le_refl 0
      | anotherAdmission _ _ _ => exact Nat.le_refl 0 }
  SettlementAt := SettlementAt input before claim
  settlement_budget_zero := fun {state} receipt => by
    cases state with
    | pending => exact receipt.elim
    | registered _ _ => rfl
  ObstructionAt := ObstructionAt input before claim

def firstStep : SourceFixedDebtAdmissionEventAt (law input before claim) .pending :=
  .ofStep (RegistrationStep.execute (input := input) (before := before) (claim := claim))

theorem target_is_actual_native_admission :
    account input before claim (firstStep input before claim).target = admit input before claim := rfl

theorem first_slot_is_the_original_loan :
    (account input before claim (firstStep input before claim).target).current.slots[before.current.slots.length]? =
      some (.live (admission input claim).toObligation) :=
  admit_keeps_original_bearer input before claim

theorem first_principal_is_not_spent_on_registration :
    total input (admission input claim).residual = claim.quantity := initial_total input claim

theorem registered_has_zero_rank : (law input before claim).budget (firstStep input before claim).target = 0 := rfl

theorem registration_is_not_financial_settlement :
    ¬ Nonempty ((law input before claim).SettlementAt (firstStep input before claim).target) := by
  rintro ⟨archive, terminal, _⟩
  have live := admit_keeps_original_bearer input before claim
  rw [terminal] at live
  cases live

def registered_obstruction : (law input before claim).ObstructionAt (firstStep input before claim).target :=
  ⟨(admission input claim).toObligation, first_slot_is_the_original_loan input before claim, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Activation
