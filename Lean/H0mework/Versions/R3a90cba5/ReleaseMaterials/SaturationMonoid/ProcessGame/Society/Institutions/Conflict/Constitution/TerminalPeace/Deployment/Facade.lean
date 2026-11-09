import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Continuation
import H0mework.Foundation.Source.AccountedUnfolding

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Clearance (dueFor)
open Clearance.Joint.Reinterpreted
open Clearance.Joint.Reinterpreted.OriginalConsumer
open Clearance.Joint.OriginalExchange (claim)
open FixedPoint.OpenPeace.Network
open Reparation.Actual (Occurrence Balance)
open private afterDue afterSigned dueStock dueRows dueSix from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalDue.Settlement

/-- Observation positions of the one installed named source. These
constructors do not grant access to a raw action or a different source. -/
inductive Stage where
  | source
  | due
  | refusal
  | settlement
  | installation
  | pendingReview
  | rebase
  | revision
  | renewal (n : Nat)
  deriving DecidableEq, Repr

def Stage.next : Stage → Stage
  | .source => .due
  | .due => .refusal
  | .refusal => .settlement
  | .settlement => .installation
  | .installation => .pendingReview
  | .pendingReview => .rebase
  | .rebase => .revision
  | .revision => .renewal 0
  | .renewal n => .renewal (n + 1)

def Stage.label : Stage → String
  | .source => "source-open"
  | .due => "due-paid"
  | .refusal => "victim-refused"
  | .settlement => "settled"
  | .installation => "network-installed"
  | .pendingReview => "prepaid-awaiting-evidence"
  | .rebase => "production-generated"
  | .revision => "u8-written"
  | .renewal _ => "due-renewed"

def Stage.physical : Stage → Original.Raw
  | .source => afterTrial
  | .due | .refusal => afterDue
  | .settlement | .installation => afterSigned
  | .pendingReview => chargedStock
  | .rebase | .revision => rebaseStock
  | .renewal n => renewStock (n + 1)

def Stage.dueBalance : Stage → ℚ
  | .source | .due | .refusal => 6
  | _ => 0

def Stage.address : Nat × Nat × Reparation.Key Bool Bool := (2, 0, claim)

noncomputable section

/-- The closed inventory points at the source's actual writes. This
carrier retains different worlds on the two sides of U8. -/
def FaceAt : Stage → Type 8
  | .source => ULift.{8} UnsettledEntrance
  | .due => ULift.{8} (type_of% first.due.period)
  | .refusal => ULift.{8} (type_of% first.motion)
  | .settlement => ULift.{8} (type_of% opening.paid)
  | .installation => ULift.{8} (type_of% opening.network)
  | .pendingReview => ULift.{8} (type_of% pending)
  | .rebase => ULift.{8} Replacement
  | .revision => ULift.{8} (type_of% completed)
  | .renewal n => ULift.{8} (type_of% (Runtime.advance home namedReplies (running n) quiet))

def readAt : (stage : Stage) → FaceAt stage
  | .source => ⟨originalDue⟩
  | .due => ⟨first.due.period⟩
  | .refusal => ⟨first.motion⟩
  | .settlement => ⟨opening.paid⟩
  | .installation => ⟨opening.network⟩
  | .pendingReview => ⟨pending⟩
  | .rebase => ⟨replacement⟩
  | .revision => ⟨completed⟩
  | .renewal n => ⟨Runtime.advance home namedReplies (running n) quiet⟩

private def currentOf : (stage : Stage) → FaceAt stage → AnyAuthoritativeRootCurrent.{0}
  | .source, ⟨entered⟩ => entered.initial.current.ledger.resident.erase
  | .due, ⟨written⟩ => written.next.ledger.resident.erase
  | .refusal, ⟨refused⟩ => refused.next.current.ledger.resident.erase
  | .settlement, ⟨paid⟩ => paid.next.ledger.resident.erase
  | .installation, ⟨installed⟩ => installed.state.current.ledger.resident.erase
  | .pendingReview, ⟨charged⟩ => charged.live.current.ledger.resident.erase
  | .rebase, ⟨changed⟩ => changed.recorded.current.ledger.resident.erase
  | .revision, ⟨revision⟩ => revision.next.current.ledger.resident.erase
  | .renewal _, ⟨paid⟩ => paid.next.current.ledger.resident.erase

def rootAt (stage : Stage) : AnyAuthoritativeRootCurrent.{0} :=
  currentOf stage (readAt stage)

theorem the_rebase_face_is_the_next_scheduler_input :
    rootAt .rebase = reached.2.current.ledger.resident.erase := by
  rw [reachedFromPending]
  rfl

theorem the_revision_face_is_the_next_material_input :
    rootAt .revision = (running 0).current.ledger.resident.erase := rfl

def rawAt : Stage → Original.Raw
  | .source => originalDue.initial.current.physical.raw
  | .due => first.due.next.current.physical.raw
  | .refusal => afterRefusal.current.physical.raw
  | .settlement => opening.paid.next.physical.raw
  | .installation => start.current.physical.raw
  | .pendingReview => pending.live.current.physical.raw
  | .rebase => reached.2.current.physical.raw
  | .revision => completed.next.current.physical.raw
  | .renewal n => (running (n + 1)).current.physical.raw

theorem physical_is_the_source_read (stage : Stage) : rawAt stage = stage.physical := by
  cases stage with
  | source =>
    exact (congrArg (fun current : Current loss front => current.physical.raw) originalDue.original).trans actualTrial.revisedStock
  | due => exact dueStock
  | refusal => exact refusedStock
  | settlement => exact (congrArg (fun physical => physical.raw) opening.network.physical).symm.trans opening.exactStock
  | installation => exact opening.exactStock
  | pendingReview => exact pendingStock
  | rebase => exact reachedStock
  | revision => exact completedStock
  | renewal n => exact (runningRead (n + 1)).1

theorem address_is_the_original_row : loss.address = Stage.address := Original.exact_address

theorem old_row_remains_on_the_running_root (n : Nat) :
    ((running n).current.ledger.stack.balances.map fun row => row.1.address) = [Stage.address] ∧
      ∀ row ∈ (running n).current.ledger.stack.balances, row.2.remaining = 0 := by
  rw [runningRows n, ← opening.network.rows]
  refine ⟨?_, opening.network.paid⟩
  change List.map ((fun row : Occurrence Original.seed Original.community => row.address) ∘ Prod.fst) _ = _
  have kept := congrArg (List.map (fun row : Occurrence Original.seed Original.community => row.address)) opening.exactRows
  simpa only [List.map_map, List.map_cons, List.map_nil, address_is_the_original_row] using kept

def rowsAt : Stage → List (Occurrence Original.seed Original.community × Balance)
  | .source => originalDue.initial.current.ledger.stack.balances
  | .due => first.due.next.current.ledger.stack.balances
  | .refusal => afterRefusal.current.ledger.stack.balances
  | .settlement => opening.paid.next.ledger.stack.balances
  | .installation => start.current.ledger.stack.balances
  | .pendingReview => pending.live.current.ledger.stack.balances
  | .rebase => reached.2.current.ledger.stack.balances
  | .revision => completed.next.current.ledger.stack.balances
  | .renewal n => (running (n + 1)).current.ledger.stack.balances

private theorem seedRows : rowsAt .source = [(loss, Original.balance)] := by
  change originalDue.initial.current.ledger.stack.balances = _
  rw [originalDue.original]
  exact the_original_six_survive_the_new_production.1

theorem due_balance_is_the_original_read (stage : Stage) :
    dueFor claim (rowsAt stage) = stage.dueBalance := by
  have unpaid : dueFor claim [(loss, Original.balance)] = 6 :=
    the_original_six_survive_the_new_production.1 ▸ the_original_six_survive_the_new_production.2
  have zero := opening.paid.balances claim
  rw [if_pos rfl, refusedSix, sub_self] at zero
  cases stage with
  | source => exact seedRows.symm ▸ unpaid
  | due => exact dueSix
  | refusal => exact refusedSix
  | settlement => exact zero
  | installation => exact (congrArg (dueFor claim) opening.network.rows).trans zero
  | pendingReview => exact (congrArg (dueFor claim) pendingRows).trans zero
  | rebase => exact (congrArg (dueFor claim) rebaseRows).trans zero
  | revision => exact (congrArg (dueFor claim) completedRows).trans zero
  | renewal n => exact (congrArg (dueFor claim) (runningRows (n + 1))).trans zero

end

structure PublicReadAt (stage : Stage) where
  clock : ℚ
  address : Nat × Nat × Reparation.Key Bool Bool
  remaining : ℚ
  clockExact : clock = (rawAt stage).clock
  addressExact : address = loss.address
  remainingExact : remaining = dueFor claim (rowsAt stage)

/-- The worker serializes this checked projection. The original root
and proof-only fields stay outside the wire format. -/
def publicRead (stage : Stage) : PublicReadAt stage :=
  ⟨stage.physical.clock, Stage.address, stage.dueBalance,
    (congrArg RawCurrent.clock (physical_is_the_source_read stage)).symm,
    address_is_the_original_row.symm, (due_balance_is_the_original_read stage).symm⟩

def observation (fuel : Nat) : RootedAccountedUnfolding Stage :=
  RootedAccountedUnfolding.observe (fun stage => .zero stage.next) .source fuel

/-- The deployed trace is a fold of the named source's generated prefix. -/
def readPrefix (fuel : Nat) : List Stage := (observation fuel).trace

noncomputable def roots (fuel : Nat) : RootedAccountedUnfolding AnyAuthoritativeRootCurrent.{0} :=
  (observation fuel).map rootAt

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment
