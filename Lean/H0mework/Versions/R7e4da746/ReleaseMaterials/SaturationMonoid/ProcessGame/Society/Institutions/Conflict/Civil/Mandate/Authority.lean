import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Law

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Mandate

open Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "S" => PublicFunction.Mandate.State Party Technology
local notation "Raw" => RawCurrent Party Good S Instrument
local notation "Req" => Request Party Good Port S Instrument
local notation "Word" => RawEvent Party Good Port S Instrument
local notation "L" => RawLaw Party Good Port Technology Instrument
local notation "Scope" => PublicFunction.Mandate.Scope (Party := Party) (Good := Good) (Port := Port)

def Released (current : Raw) : Prop :=
  current.technology.holder = none ∧ current.technology.offered = none

def DoesNotPropose (request : Req) : Prop :=
  match request.operation with
  | .revise _ target => ∀ candidate, target.last ≠ some (.propose candidate)
  | _ => True

/-- Without a fresh proposal on the original task, every candidate step
keeps a released mandate closed, even with a new request or state version. -/
theorem a_step_without_new_nomination_keeps_release
    (base : L) (scope : Scope) (current : Raw) (request : Req)
    (released : Released current) (noOffer : DoesNotPropose request) :
    Released ((PublicFunction.Mandate.law base scope).step current request) := by
  by_cases accepted : (PublicFunction.Mandate.law base scope).Valid current request
  · rw [RawLaw.step, if_pos accepted]
    cases operation : request.operation
    case revise operator target =>
      have policy := accepted.1.2
      cases marked : target.last with
      | none =>
          simp [PublicFunction.Mandate.law, RawLaw.operationAllowed, RawPolicy.eval, operation, marked] at policy
      | some command =>
          simp only [PublicFunction.Mandate.law, RawLaw.operationAllowed, RawPolicy.eval, operation,
            marked, decide_eq_true_eq] at policy
          simp only [Released, RawLaw.paidStep, operation]
          rw [policy.2.2.2.2.1]
          cases command with
          | propose candidate =>
              exact ((show ∀ candidate, target.last ≠ some (.propose candidate) from
                by simpa only [DoesNotPropose, operation] using noOffer) candidate marked).elim
          | accept =>
              have offered := policy.2.2.2.2.2.1
              rw [released.2] at offered
              cases offered
          | renew =>
              have offered := policy.2.2.2.2.2.1
              rw [released.2] at offered
              cases offered
          | exit => exact ⟨rfl, rfl⟩
          | revoke => exact ⟨rfl, rfl⟩
          | review =>
              unfold PublicFunction.Mandate.advance
              split <;> simp_all [Released]
    all_goals simpa only [Released, RawLaw.paidStep, operation] using released
  · rw [(PublicFunction.Mandate.law base scope).rejected_preserves_current _ _ accepted]
    exact released

theorem a_finite_word_without_new_nomination_keeps_release
    (base : L) (scope : Scope) (current : Raw) (index : Nat) (word : Word)
    (released : Released current) (noOffer : ∀ request ∈ word, DoesNotPropose request) :
    Released ((PublicFunction.Mandate.law base scope).execute current index word).final := by
  induction word generalizing current index with
  | nil => exact released
  | cons request tail inherited =>
      exact inherited _ _ (a_step_without_new_nomination_keeps_release base scope current request
        released (noOffer _ List.mem_cons_self)) (fun next listed => noOffer next (List.mem_cons_of_mem _ listed))

def NeedsAuthority (base : L) (scope : Scope) (current : Raw) (request : Req) : Prop :=
  match request.operation with
  | .revise .. => False
  | _ => scope.service ∈ base.requiredPorts (PublicFunction.Mandate.eraseCurrent current)
      (PublicFunction.Mandate.eraseRequest request) ∨ PublicFunction.Mandate.TaskUse scope request

omit [DecidableEq Instrument] in
theorem a_released_mandate_refuses_every_protected_operation
    (base : L) (scope : Scope) (current : Raw) (request : Req)
    (released : Released current) (controlled : NeedsAuthority base scope current request) :
    ¬ (PublicFunction.Mandate.law base scope).Valid current request := by
  intro valid
  have policy := valid.1.2
  cases operation : request.operation
  case revise operator target =>
    simp only [NeedsAuthority, operation] at controlled
  all_goals
    simp only [PublicFunction.Mandate.law, RawLaw.operationAllowed, RawPolicy.eval,
      operation, Bool.and_eq_true, decide_eq_true_eq] at policy
    have holder := (policy.2 (by simpa only [NeedsAuthority, operation] using controlled)).1
    rw [released.1] at holder
    cases holder

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Mandate
