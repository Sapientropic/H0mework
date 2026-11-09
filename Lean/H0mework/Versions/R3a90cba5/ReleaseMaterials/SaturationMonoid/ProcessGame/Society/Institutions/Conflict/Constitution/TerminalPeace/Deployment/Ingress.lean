import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Facade
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Continuation.Waiting

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment.Ingress

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Clearance (dueFor)
open Clearance.Joint.Reinterpreted.OriginalConsumer
open Clearance.Joint.OriginalExchange (claim)
open Reparation.Actual (Occurrence Balance)
open FixedPoint.OpenPeace.Network

/-- Public callers can invoke the named root inputs at their source slot.
Their payloads and signed orders are resolved by the installed source. -/
inductive Input
  | advance
  | review
  | due
  | evidence

def Input.parse : String → Option Input
  | "advance" => some .advance
  | "review" => some .review
  | "due" => some .due
  | "evidence" => some .evidence
  | _ => none

inductive Position
  | opening (stage : Stage)
  | waiting (paid : Nat)
  | revised (waited paid : Nat)

def start : Position := .opening .source

def consume : Position → Input → Option Position
  | .opening .source, .advance => some (.opening .due)
  | .opening .due, .advance => some (.opening .refusal)
  | .opening .refusal, .advance => some (.opening .settlement)
  | .opening .settlement, .advance => some (.opening .installation)
  | .opening .installation, .review => some (.opening .pendingReview)
  | .opening .pendingReview, .advance => some (.waiting 0)
  | .waiting n, .due => some (.waiting (n + 1))
  | .waiting n, .evidence => some (.revised n 0)
  | .revised n m, .due => some (.revised n (m + 1))
  | _, _ => none

def Position.label : Position → String
  | .opening stage => stage.label
  | .waiting 0 => Stage.rebase.label
  | .waiting (_ + 1) => "due-awaiting-evidence"
  | .revised _ 0 => Stage.revision.label
  | .revised _ (_ + 1) => "due-renewed"

def Position.clock : Position → ℚ
  | .opening stage => (publicRead stage).clock
  | .waiting n => (renewStock n).clock
  | .revised n m => (renewStock (n + m)).clock

def Position.remaining : Position → ℚ
  | .opening stage => (publicRead stage).remaining
  | .waiting _ | .revised _ _ => 0

noncomputable section

def Position.root : Position → AnyAuthoritativeRootCurrent.{0}
  | .opening stage => rootAt stage
  | .waiting n => (Deployment.waiting n).current.ledger.resident.erase
  | .revised n m => (afterWaiting n m).current.ledger.resident.erase

def Position.raw : Position → Original.Raw
  | .opening stage => rawAt stage
  | .waiting n => (Deployment.waiting n).current.physical.raw
  | .revised n m => (afterWaiting n m).current.physical.raw

def Position.rows : Position → List (Occurrence Original.seed Original.community × Balance)
  | .opening stage => rowsAt stage
  | .waiting n => (Deployment.waiting n).current.ledger.stack.balances
  | .revised n m => (afterWaiting n m).current.ledger.stack.balances

theorem public_clock_is_native (position : Position) : position.clock = position.raw.clock := by
  cases position with
  | opening stage => exact (publicRead stage).clockExact
  | waiting n => exact congrArg RawCurrent.clock (waitingRead n).1.symm
  | revised n m => exact congrArg RawCurrent.clock (afterWaitingRead n m).1.symm

theorem public_balance_is_native (position : Position) : position.remaining = dueFor claim position.rows := by
  have cleared := (due_balance_is_the_original_read Stage.settlement).symm
  cases position with
  | opening stage => exact (publicRead stage).remainingExact
  | waiting n => exact cleared.trans (congrArg (dueFor claim) (waitingRows n)).symm
  | revised n m => exact cleared.trans (congrArg (dueFor claim) (afterWaitingRows n m)).symm

theorem evidence_is_admitted_only_once (n m : Nat) :
    consume (.waiting n) .evidence = some (.revised n 0) ∧ consume (.revised n m) .evidence = none :=
  ⟨rfl, rfl⟩

theorem waiting_and_revised_inputs_consume_the_actual_due (n m : Nat) :
    consume (.waiting n) .due = some (.waiting (n + 1)) ∧
      Position.root (.waiting (n + 1)) =
        (Runtime.advance home namedReplies (waiting n) quiet).next.current.ledger.resident.erase ∧
      consume (.revised n m) .due = some (.revised n (m + 1)) ∧
      Position.root (.revised n (m + 1)) =
        (Runtime.advance home namedReplies (afterWaiting n m) quiet).next.current.ledger.resident.erase :=
  ⟨rfl, rfl, rfl, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment.Ingress
