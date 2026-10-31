import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.TransportRuntime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Source.ProgrammeFace

/-- Signing this exact challenge-port submission assumes follow-up of the
request to withdraw the currently named authority snapshot. It spends no
revision stock and does not itself withdraw that authority. -/
def submission : Action := ⟨false, [], scope.challenge, [scope.challenge], .present⟩

theorem submission_valid (current : Current) : law.Valid current submission := by
  simp [law, Mandate.law, submission, RawLaw.Valid, RawLaw.SignerMatches,
    RawLaw.operationAllowed, RawPolicy.eval, eraseCurrent, eraseRequest, eraseOperation,
    base, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard,
    TaskUse, scope, task, Delegation.members, NonnegativeBundle]

theorem submission_preserves_authority_and_stock (current : Current) :
    law.step current submission = current :=
  law.presentation_preserves_material_and_claims current submission rfl

def isSubmission (actual : Action) : Bool :=
  decide (actual.signer = false) && actual.consents.isEmpty &&
    decide (actual.purpose = scope.challenge) && decide (actual.gates = [scope.challenge]) &&
    match actual.operation with | .present => true | _ => false

theorem isSubmission_iff (actual : Action) : isSubmission actual = true ↔ actual = submission := by
  rcases actual with ⟨signer, consents, purpose, gates, operation⟩
  cases operation <;> simp [isSubmission, submission, Request.mk.injEq, and_assoc]

def isRevoke (current : Current) (actual : Action) : Bool :=
  decide (actual.signer = false) && actual.consents.isEmpty &&
    decide (actual.purpose = scope.challenge) && decide (actual.gates = [scope.challenge]) &&
    match actual.operation with
    | .revise operator target => decide (operator = false ∧ target = advance scope current .revoke)
    | _ => false

theorem isRevoke_iff (current : Current) (actual : Action) :
    isRevoke current actual = true ↔ actual = request scope current false .revoke := by
  rcases actual with ⟨signer, consents, purpose, gates, operation⟩
  cases operation <;> simp [isRevoke, request, Request.mk.injEq, and_assoc]

def isHolderExit (current : Current) (actual : Action) : Bool :=
  actual.consents.isEmpty && decide (actual.purpose = scope.challenge) &&
    decide (actual.gates = [scope.challenge]) && decide (current.technology.holder = some actual.signer) &&
    match actual.operation with
    | .revise operator target => decide (operator = actual.signer ∧ target = advance scope current .exit)
    | _ => false

theorem isHolderExit_iff (current : Current) (actual : Action) :
    isHolderExit current actual = true ↔
      actual = request scope current actual.signer .exit ∧ current.technology.holder = some actual.signer := by
  rcases actual with ⟨signer, consents, purpose, gates, operation⟩
  cases operation <;> simp [isHolderExit, request, Request.mk.injEq, and_assoc, and_left_comm, and_comm]

def isWithdrawal (current : Current) (actual : Action) := isRevoke current actual || isHolderExit current actual

theorem isWithdrawal_iff (current : Current) (actual : Action) :
    isWithdrawal current actual = true ↔
      actual = request scope current false .revoke ∨
      (actual = request scope current actual.signer .exit ∧ current.technology.holder = some actual.signer) := by
  simp only [isWithdrawal, Bool.or_eq_true, isRevoke_iff, isHolderExit_iff]

variable (fuel : ℚ) (inputs : List (List Action))

abbrev I := input fuel inputs

structure Position where
  ordinal : Nat
  index : Fin (Registered.traceItems (I fuel inputs)
    (ProgrammeHistory.visitAt (I fuel inputs) ordinal).current).length

def Position.origin (position : Position fuel inputs) : Financial.InstructionOrigin (I fuel inputs) :=
  Financial.traceOriginAt (I fuel inputs) (ProgrammeHistory.visitAt (I fuel inputs) position.ordinal) position.index

def Position.item (position : Position fuel inputs) :=
  (Registered.traceItems (I fuel inputs) (ProgrammeHistory.visitAt (I fuel inputs) position.ordinal).current).get position.index

theorem Position.decoded (position : Position fuel inputs) :
    (position.origin fuel inputs).instruction? (I fuel inputs) = some (position.item fuel inputs) :=
  Financial.traceOriginAt_instruction _ _ _

structure Claim where
  private mk ::
  position : Position fuel inputs
  signed : (position.item fuel inputs).request = submission
  accepted : law.Valid (position.item fuel inputs).before (position.item fuel inputs).request
  active : (position.item fuel inputs).before.technology.holder.isSome = true ∨
    (position.item fuel inputs).before.technology.offered.isSome = true

def read (position : Position fuel inputs) : Option (Claim fuel inputs) :=
  if signed : isSubmission (position.item fuel inputs).request = true then
    if active : (position.item fuel inputs).before.technology.holder.isSome = true ∨
        (position.item fuel inputs).before.technology.offered.isSome = true then
      some ⟨position, (isSubmission_iff _).mp signed, by rw [(isSubmission_iff _).mp signed]; exact submission_valid _, active⟩
    else none
  else none

def positionsAt (ordinal : Nat) : List (Position fuel inputs) :=
  (List.finRange _).map (fun index => ⟨ordinal, index⟩)

def claimsAt (ordinal : Nat) := (positionsAt fuel inputs ordinal).filterMap (read fuel inputs)

def Claim.origin (claim : Claim fuel inputs) := claim.position.origin fuel inputs
abbrev Claim.snapshot (claim : Claim fuel inputs) := (claim.position.item fuel inputs).before.technology

theorem Claim.signer_present (claim : Claim fuel inputs) :
    ActualBirth.presentAt (I fuel inputs) (claim.origin fuel inputs).visit false := by
  have mem := (claim.origin fuel inputs).instruction_mem (I fuel inputs)
    (claim.position.item fuel inputs) (claim.position.decoded fuel inputs)
  change false ∈ (parties (I fuel inputs).law _)
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨claim.position.item fuel inputs, mem, ?_⟩
  change false ∈ (claim.position.item fuel inputs).request.signer :: _
  rw [claim.signed]
  exact List.mem_cons_self

def Claim.birth (claim : Claim fuel inputs) :=
  ActualBirth.generate (I fuel inputs) (claim.origin fuel inputs).visit false (claim.signer_present fuel inputs)

def Claim.actor (claim : Claim fuel inputs) := (claim.birth fuel inputs).actor (I fuel inputs)

/-- A literal member revoke or holder-owned exit against this exact snapshot.
Validity remains separate so an unpaid withdrawal retains its real refusal. -/
structure Attempt (claim : Claim fuel inputs) where
  position : Position fuel inputs
  later : claim.position.ordinal < position.ordinal ∨
    (claim.position.ordinal = position.ordinal ∧ claim.position.index.val < position.index.val)
  signed : (position.item fuel inputs).request = request scope (position.item fuel inputs).before false .revoke ∨
    ((position.item fuel inputs).request = request scope (position.item fuel inputs).before (position.item fuel inputs).request.signer .exit ∧
      (position.item fuel inputs).before.technology.holder = some (position.item fuel inputs).request.signer)
  snapshot : (position.item fuel inputs).before.technology = claim.snapshot fuel inputs

def readAttempt (claim : Claim fuel inputs) (position : Position fuel inputs) : Option (Attempt fuel inputs claim) :=
  if checked : (claim.position.ordinal < position.ordinal ∨
        (claim.position.ordinal = position.ordinal ∧ claim.position.index.val < position.index.val)) ∧
      isWithdrawal (position.item fuel inputs).before (position.item fuel inputs).request = true ∧
      (position.item fuel inputs).before.technology = claim.snapshot fuel inputs then
    some ⟨position, checked.1, (isWithdrawal_iff _ _).mp checked.2.1, checked.2.2⟩
  else none

theorem Attempt.actual_withdrawal (claim : Claim fuel inputs) (attempt : Attempt fuel inputs claim)
    (accepted : law.Valid (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request) :
    (law.step (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request).technology.holder = none ∧
    (law.step (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request).technology.offered = none ∧
    (law.step (attempt.position.item fuel inputs).before (attempt.position.item fuel inputs).request).technology.version =
      (claim.snapshot fuel inputs).version + 1 := by
  rw [RawLaw.step, if_pos accepted]
  rcases attempt.signed with signed | ⟨signed, held⟩
  · have operation := congrArg Request.operation signed
    simp only [RawLaw.paidStep, operation, request, advance, attempt.snapshot, and_self]
  · have operation := congrArg Request.operation signed
    simp only [RawLaw.paidStep, operation, request, advance, attempt.snapshot, and_self]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection
