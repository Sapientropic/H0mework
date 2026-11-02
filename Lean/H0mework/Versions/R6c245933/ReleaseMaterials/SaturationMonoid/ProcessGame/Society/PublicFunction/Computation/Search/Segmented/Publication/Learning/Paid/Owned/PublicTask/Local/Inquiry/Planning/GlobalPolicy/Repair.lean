import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Committed
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Preservation.Restoration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.Repair
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- Materialize the counterpolicy's own fallback before discarding its unperformed past. -/
def remaining (cache : Inquiry.Frame task) (other : Program task.model.source.code (horizon task.domain)) :
    Complete.FiniteProgram task.model.source.code :=
  let controls := (Prefix.Commitment.padded task.original other).controls.drop cache.past.length
  ⟨controls.length,Splice.word controls⟩

variable {task} (cache : Inquiry.Frame task)
  {protocol : Program task.model.source.code (horizon task.domain)}
  (failure : Prefix.Global.Failure (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original cache.programme protocol)

inductive Judgement (suffix : Complete.FiniteProgram task.model.source.code) where
  | admitted (accepted : Selection.Restoration.acceptable (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original cache.programme
      (Committed.proposal task cache suffix))
  | refused (rejected : Selection.Restoration.Rejection (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original cache.programme
      (Committed.proposal task cache suffix))

/-- Rebuilding a tail after an irreversible prefix requires a fresh complete check. -/
def inspectSuffix (suffix : Complete.FiniteProgram task.model.source.code) : Judgement cache suffix :=
  if accepted : Selection.Restoration.acceptable (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original cache.programme
      (Committed.proposal task cache suffix) then .admitted accepted
  else .refused (Selection.Restoration.rejectionFrom (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _ _ accepted)

def Review : Type := match failure with
  | .inadmissible _ => Unit
  | .dominated other _ _ => Judgement cache (remaining task cache other)

def inspect : Review cache failure := match failure with
  | .inadmissible _ => ()
  | .dominated other _ _ => inspectSuffix cache (remaining task cache other)

structure Response where
  decision : Review cache failure
  checked : decision = inspect cache failure

def respond : Response cache failure := ⟨inspect cache failure,rfl⟩

namespace Response
variable {cache failure} (made : Response cache failure)

def path : Inquiry.Leg task cache := match failure,made.decision with
  | .inadmissible _,_ => Inquiry.Leg.advance cache
  | .dominated _ _ _,.refused _ => Inquiry.Leg.advance cache
  | .dominated other _ _,.admitted accepted => Committed.acceptedPath task cache (remaining task cache other)
      (Selection.Restoration.retains_original_acceptance (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _ _ accepted)

theorem restores : Inquiry.Preservation.Restoration.Accepts task cache.programme made.path.finish.programme := by
  cases failure with
  | inadmissible => exact Inquiry.Preservation.Restoration.frame_advance task cache
  | dominated other accepted strict =>
      cases decided : made.decision with
      | refused => simpa only [path,decided,Inquiry.Leg.advance] using Inquiry.Preservation.Restoration.frame_advance task cache
      | admitted good =>
          simpa only [path,decided,Committed.acceptedPath,Inquiry.Preservation.Restoration.Accepts] using
            Inquiry.Preservation.Restoration.trans task good
              (Inquiry.Preservation.Restoration.frame_advance task
                (Committed.commit task cache (remaining task cache other)
                  (Selection.Restoration.retains_original_acceptance (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _ _ good)))

theorem settles : Inquiry.Preservation.Settles task made.path :=
  Selection.Restoration.retains_original_acceptance (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _ _ made.restores

theorem admitted_executes_the_generated_counterpolicy_head
    (other : Program task.model.source.code (horizon task.domain))
    (accepted : Selection.Restoration.acceptable (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original cache.programme other)
    (strict : Selection.Restoration.strict (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original protocol other)
    (reply : Response cache (.dominated other accepted strict))
    (good : Selection.Restoration.acceptable (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original cache.programme
      (Committed.proposal task cache (remaining task cache other)))
    (admitted : reply.decision = .admitted good)
    (live : Driving.Progress.Live cache.shell) :
    reply.path.word = [(remaining task cache other).2.at task.original 0] := by
  simpa only [path,admitted] using
    Committed.every_admitted_complete_suffix_executes_its_selected_head task cache _
      (Selection.Restoration.retains_original_acceptance (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _ _ good) live

/-- Refusal keeps the old plan active; admission executes only the rechecked tail. -/
theorem advances (live : Driving.Progress.Live cache.shell) : made.path.finish.past.length = cache.past.length+1 := by
  have next : (Inquiry.Frame.advance task cache).past.length = cache.past.length+1 := by
    rw [Inquiry.Frame.advance_past]
    simp only [Driving.Progress.rules,if_pos live,List.length_append,List.length_singleton]
  cases failure with
  | inadmissible => exact next
  | dominated other accepted strict =>
      cases decided : made.decision with
      | refused => simpa only [path,decided,Inquiry.Leg.advance] using next
      | admitted good =>
          have word := Committed.every_admitted_complete_suffix_executes_its_selected_head task cache
            (remaining task cache other) (Selection.Restoration.retains_original_acceptance (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _ _ good) live
          have literal := (Committed.acceptedPath task cache (remaining task cache other)
            (Selection.Restoration.retains_original_acceptance (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _ _ good)).literal
          simp only [path,decided]
          rw [literal,word]
          simp

abbrev current := Planning.current task made.path.finish
abbrev full := made.current.point

theorem actual_source : made.full = Splice.install (Planning.current task cache).point task.rival made.path.word := by
  have after := Paid.State.current_is_the_actual_control_prefix made.path.finish.shell task.point task.rival
  have before := Paid.State.current_is_the_actual_control_prefix cache.shell task.point task.rival
  change (made.path.finish.shell.current task.point task.rival).point = _
  rw [after]
  change Splice.install task.point.point task.rival made.path.finish.past = _
  rw [made.path.literal]
  change List.foldl _ _ (cache.past ++ made.path.word) = _
  rw [List.foldl_append]
  change Splice.install (Splice.install task.point.point task.rival cache.past) task.rival made.path.word = _
  rw [before]

theorem complete_paid_prefix (visit : Nat) (earlier : visit ≤ arrival (Planning.current task cache).point) :
    Native.Coupling.Match task.model.source.code (Planning.current task cache).point.source.input made.full.source.input
      (Financial.accountAt (Planning.current task cache).point.source.input visit) (Financial.accountAt made.full.source.input visit) := by
  rw [made.actual_source]
  exact Installation.Chain.fold_keeps_the_complete_native_financial_prefix (model := task.model)
    _ task.rival _ visit earlier

abbrev bound := Replanning.native task.model made.full
abbrev facade := Native.AuthorityRuntime.facade made.bound
abbrev activated := Inquiry.Runtime.readState made.bound (depth made.full)

theorem the_same_actual_root_consumes_the_obstruction_driven_step_and_its_own_next :
    Inquiry.Preservation.Restoration.Accepts task cache.programme made.path.finish.programme ∧
    Inquiry.Preservation.Settles task made.path ∧
    HEq (made.facade.readoutAt made.activated .responsibilities)
      (made.activated.tick.generated.projectionOutcome (.component ())) ∧
    HEq made.activated.tick.generated.wholeLedgerWriteBack
      (made.activated.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt made.activated.current.visit.current) ∧
    made.activated.tick.nextCurrent = made.facade.process.stateAt (made.facade.process.successor made.activated.state) := by
  have rooted := made.facade.readoutAt_factorizes made.activated .responsibilities
  exact ⟨made.restores,made.settles,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
end Response
end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.GlobalPolicy.Repair
