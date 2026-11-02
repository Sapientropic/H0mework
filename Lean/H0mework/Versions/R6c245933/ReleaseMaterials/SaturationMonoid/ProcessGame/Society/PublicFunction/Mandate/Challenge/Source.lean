import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Programme
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Fold

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type}
  (bound : ProgrammeFamily base scope Index)
  (inputs : Index)

abbrev I := bound.inputAt inputs

def Submission (action : Request Party Good Port (State Party Technology) Instrument) : Prop :=
  action.signer ∈ Delegation.members scope.task ∧ action.consents = [] ∧
  action.purpose = scope.challenge ∧ action.gates = [scope.challenge] ∧
  match action.operation with | .present => True | _ => False

instance (action : Request Party Good Port (State Party Technology) Instrument) : Decidable (Submission (scope := scope) action) := by
  unfold Submission
  cases action.operation <;> infer_instance

structure Position where
  ordinal : Nat
  index : Fin (Registered.traceItems (I bound inputs)
    (ProgrammeHistory.visitAt (I bound inputs) ordinal).current).length

def Position.origin (position : Position bound inputs) : Financial.InstructionOrigin (I bound inputs) :=
  Financial.traceOriginAt (I bound inputs) (ProgrammeHistory.visitAt (I bound inputs) position.ordinal) position.index

def Position.item (position : Position bound inputs) :=
  (Registered.traceItems (I bound inputs) (ProgrammeHistory.visitAt (I bound inputs) position.ordinal).current).get position.index

theorem Position.decoded (position : Position bound inputs) :
    (position.origin bound inputs).instruction? (I bound inputs) = some (position.item bound inputs) :=
  Financial.traceOriginAt_instruction _ _ _

def Later (first second : Position bound inputs) : Prop :=
  first.ordinal < second.ordinal ∨ (first.ordinal = second.ordinal ∧ first.index.val < second.index.val)

instance (first second : Position bound inputs) : Decidable (Later bound inputs first second) :=
  inferInstanceAs (Decidable (_ ∨ _))

structure Claim where
  private mk ::
  position : Position bound inputs
  signed : Submission (scope := scope) (position.item bound inputs).request
  accepted : (law base scope).Valid (position.item bound inputs).before (position.item bound inputs).request
  active : (position.item bound inputs).before.technology.holder.isSome = true ∨
    (position.item bound inputs).before.technology.offered.isSome = true

def read (position : Position bound inputs) : Option (Claim bound inputs) :=
  if signed : Submission (scope := scope) (position.item bound inputs).request then
    if accepted : (law base scope).Valid (position.item bound inputs).before (position.item bound inputs).request then
      if active : (position.item bound inputs).before.technology.holder.isSome = true ∨
          (position.item bound inputs).before.technology.offered.isSome = true then
        some ⟨position, signed, accepted, active⟩
      else none
    else none
  else none

theorem read_position (position : Position bound inputs) (claim : Claim bound inputs)
    (decoded : read bound inputs position = some claim) : claim.position = position := by
  unfold read at decoded
  split at decoded
  · split at decoded
    · split at decoded
      · cases Option.some.inj decoded; rfl
      · cases decoded
    · cases decoded
  · cases decoded

theorem Claim.valid_at_actual_source (claim : Claim bound inputs) :
    (I bound inputs).law.Valid (claim.position.item bound inputs).before (claim.position.item bound inputs).request := by
  rw [show (I bound inputs).law = law base scope from bound.law_exact inputs]
  exact claim.accepted

def positionsAt (ordinal : Nat) : List (Position bound inputs) :=
  (List.finRange _).map (fun index => ⟨ordinal, index⟩)

def claimsAt (ordinal : Nat) := (positionsAt bound inputs ordinal).filterMap (read bound inputs)

def Claim.origin (claim : Claim bound inputs) := claim.position.origin bound inputs
abbrev Claim.snapshot (claim : Claim bound inputs) := (claim.position.item bound inputs).before.technology
abbrev Claim.signer (claim : Claim bound inputs) := (claim.position.item bound inputs).request.signer

theorem Claim.signer_present (claim : Claim bound inputs) :
    ActualBirth.presentAt (I bound inputs) (claim.origin bound inputs).visit (claim.signer bound inputs) := by
  have actual := (claim.origin bound inputs).instruction_mem (I bound inputs)
    (claim.position.item bound inputs) (claim.position.decoded bound inputs)
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  exact ⟨claim.position.item bound inputs, actual, List.mem_cons_self⟩

def Claim.birth (claim : Claim bound inputs) :=
  ActualBirth.generate (I bound inputs) (claim.origin bound inputs).visit (claim.signer bound inputs)
    (claim.signer_present bound inputs)

def Claim.actor (claim : Claim bound inputs) := (claim.birth bound inputs).actor (I bound inputs)

/-- Expired review counts only when it actually ends the named jurisdiction.
An ordinary paid review cannot settle a withdrawal request. -/
def Withdrawal (current : RawCurrent Party Good (State Party Technology) Instrument)
    (action : Request Party Good Port (State Party Technology) Instrument) : Prop :=
  action.consents = [] ∧ action.purpose = scope.challenge ∧ action.gates = [scope.challenge] ∧
  match action.operation with
  | .revise operator target => operator = action.signer ∧
      ((action.signer ∈ Delegation.members scope.task ∧ target = advance scope current .revoke) ∨
       (current.technology.holder = some action.signer ∧ target = advance scope current .exit) ∨
       (action.signer ∈ Delegation.members scope.task ∧ scope.task.deadline < current.clock ∧
        target = advance scope current .review))
  | _ => False

instance (current : RawCurrent Party Good (State Party Technology) Instrument)
    (action : Request Party Good Port (State Party Technology) Instrument) : Decidable (Withdrawal (scope := scope) current action) := by
  unfold Withdrawal
  cases action.operation <;> infer_instance

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem withdrawal_commands (current : RawCurrent Party Good (State Party Technology) Instrument)
    (action : Request Party Good Port (State Party Technology) Instrument) (signed : Withdrawal (scope := scope) current action) :
    (action.signer ∈ Delegation.members scope.task ∧ action = request scope current action.signer .revoke) ∨
    (current.technology.holder = some action.signer ∧ action = request scope current action.signer .exit) ∨
    (action.signer ∈ Delegation.members scope.task ∧ scope.task.deadline < current.clock ∧
      action = request scope current action.signer .review) := by
  rcases action with ⟨signer, consents, purpose, gates, operation⟩
  cases operation <;> simp_all [Withdrawal, request, Request.mk.injEq]

structure Attempt (claim : Claim bound inputs) where
  private mk ::
  position : Position bound inputs
  later : Later bound inputs claim.position position
  signed : Withdrawal (scope := scope) (position.item bound inputs).before (position.item bound inputs).request
  snapshot : (position.item bound inputs).before.technology = claim.snapshot bound inputs

def readAttempt (claim : Claim bound inputs) (position : Position bound inputs) : Option (Attempt bound inputs claim) :=
  if checked : Later bound inputs claim.position position ∧
      Withdrawal (scope := scope) (position.item bound inputs).before (position.item bound inputs).request ∧
      (position.item bound inputs).before.technology = claim.snapshot bound inputs then
    some ⟨position, checked.1, checked.2.1, checked.2.2⟩
  else none

theorem Attempt.actual_withdrawal (claim : Claim bound inputs) (attempt : Attempt bound inputs claim)
    (accepted : (law base scope).Valid (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request) :
    ((law base scope).step (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request).technology.holder = none ∧
    ((law base scope).step (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request).technology.offered = none ∧
    ((law base scope).step (attempt.position.item bound inputs).before (attempt.position.item bound inputs).request).technology.version =
      (claim.snapshot bound inputs).version + 1 := by
  rw [RawLaw.step, if_pos accepted]
  rcases withdrawal_commands _ _ attempt.signed with ⟨_, signed⟩ | ⟨_, signed⟩ | ⟨_, expired, signed⟩
  · have operation := congrArg Request.operation signed
    simp only [RawLaw.paidStep, operation, request, advance, attempt.snapshot, and_self]
  · have operation := congrArg Request.operation signed
    simp only [RawLaw.paidStep, operation, request, advance, attempt.snapshot, and_self]
  · have operation := congrArg Request.operation signed
    simp only [RawLaw.paidStep, operation, request, advance, if_pos expired, attempt.snapshot, and_self]

private theorem lookup_retained (ordinal distance : Nat) (signer : Party) (witness : ActualBirth.Witness (I bound inputs))
    (found : ActualBirth.lookup (I bound inputs) (ProgrammeHistory.visitAt (I bound inputs) ordinal) signer = some witness) :
    ActualBirth.lookup (I bound inputs) (ProgrammeHistory.visitAt (I bound inputs) (ordinal + distance)) signer = some witness := by
  induction distance with
  | zero => exact found
  | succ distance ih => exact ActualBirth.lookup_retains_original_birth (I bound inputs) _ rfl signer witness ih

theorem same_original_actor (first second : Claim bound inputs)
    (later : Later bound inputs first.position second.position) (signer : second.signer bound inputs = first.signer bound inputs) :
    second.actor bound inputs = first.actor bound inputs := by
  have le : first.position.ordinal ≤ second.position.ordinal := by
    rcases later with lt | ⟨same, _⟩
    · exact Nat.le_of_lt lt
    · exact Nat.le_of_eq same
  have found := lookup_retained bound inputs first.position.ordinal
    (second.position.ordinal - first.position.ordinal) _ (first.birth bound inputs).original
    (first.birth bound inputs).generated
  rw [Nat.add_sub_of_le le] at found
  have sameLookup := congrArg (fun signer => ActualBirth.lookup (I bound inputs) (second.origin bound inputs).visit signer) signer
  have secondFound := sameLookup.symm.trans (second.birth bound inputs).generated
  have same := Option.some.inj (secondFound.symm.trans found)
  exact congrArg (ActualBirth.Witness.actor (I bound inputs)) same

structure Reconfirmation (original : Claim bound inputs) where
  private mk ::
  target : Claim bound inputs
  later : Later bound inputs original.position target.position
  signer : target.signer bound inputs = original.signer bound inputs
  actor : target.actor bound inputs = original.actor bound inputs

def readReconfirmation (original : Claim bound inputs) (position : Position bound inputs) : Option (Reconfirmation bound inputs original) :=
  match read bound inputs position with
  | none => none
  | some target =>
      if checked : Later bound inputs original.position target.position ∧ target.signer bound inputs = original.signer bound inputs then
        some ⟨target, checked.1, checked.2, same_original_actor bound inputs original target checked.1 checked.2⟩
      else none

inductive Target (original : Claim bound inputs)
  | initial
  | renewed (receipt : Reconfirmation bound inputs original)

def Target.claim {original : Claim bound inputs} : Target bound inputs original → Claim bound inputs
  | .initial => original
  | .renewed receipt => receipt.target

theorem Target.actor {original : Claim bound inputs} (target : Target bound inputs original) :
    (target.claim bound inputs).actor bound inputs = original.actor bound inputs := by
  cases target with
  | initial => rfl
  | renewed receipt => exact receipt.actor

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge
