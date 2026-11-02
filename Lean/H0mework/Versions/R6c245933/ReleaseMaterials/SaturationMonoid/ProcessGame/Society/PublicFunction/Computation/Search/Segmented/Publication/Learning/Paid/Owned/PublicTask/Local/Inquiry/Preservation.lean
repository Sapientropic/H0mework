import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Preservation
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

abbrev Accepts (first last : Program task.model.source.code (horizon task.domain)) :=
  Selection.acceptable task.model task.domain task.original first last

theorem self (cache : Owned.Cache task) : Accepts task cache.programme cache.programme :=
  Prefix.Commitment.admissible_plan_is_its_own_valid_reference
    task.model task.domain task.original task.baseline cache.programme cache.above

theorem trans {first middle last : Program task.model.source.code (horizon task.domain)}
    (left : Accepts task first middle) (right : Accepts task middle last) : Accepts task first last :=
  Selection.acceptable_trans task.model task.domain task.original last middle first right left

theorem progress (cache : Owned.Cache task) : Accepts task cache.programme (Driving.Progress.next cache).programme := by
  unfold Driving.Progress.next
  split
  · exact Prefix.Commitment.padded_acceptance task.model task.domain task.original
      cache.programme cache.programme (self task cache)
  · exact self task cache

theorem advance (cache : Owned.Cache task) : Accepts task cache.programme (Owned.advance task cache).programme :=
  progress task cache

theorem commit (cache : Owned.Cache task) (reader : Fin task.model.source.code.sites)
    (reading : Fin task.model.source.code.signals) (decision : cache.Decision reader) :
    Accepts task cache.programme (cache.commit reader reading decision).programme := by
  cases decision with
  | refused => exact self task cache
  | admitted accepted => exact accepted

theorem walk {cache : Owned.Cache task} (made : Owned.Walk task cache) :
    Accepts task cache.programme made.final.programme := by
  induction made with
  | exhausted | terminal => exact self task _
  | @learned cache live owned decision =>
      exact trans task (commit task cache task.reader _ decision) (advance task _)
  | waiting live foreign later ih => exact trans task (advance task _) ih

theorem turn {cache : Owned.Cache task} (made : Owned.Turn task cache) :
    Accepts task cache.programme made.final.programme := by
  cases made with
  | unsupported => exact self task _
  | unreserved =>
      change Accepts task cache.programme (if task.continueUnreserved then Owned.advance task cache else cache).programme
      split
      · exact advance task _
      · exact self task _
  | unpaid => exact self task _
  | paid supported booked receipt later => exact walk task later

def Settles {cache : Inquiry.Frame task} (leg : Inquiry.Leg task cache) : Prop :=
  Accepts task cache.programme leg.finish.programme

theorem stay (cache : Inquiry.Frame task) : Settles task (Inquiry.Leg.stay cache) := self task cache.shell

theorem frame_advance (cache : Inquiry.Frame task) : Settles task (Inquiry.Leg.advance cache) := by
  exact progress task {cache.shell with beliefs := []}

theorem append {cache : Inquiry.Frame task} (first : Inquiry.Leg task cache)
    (second : Inquiry.Leg task first.finish) (left : Settles task first) (right : Settles task second) :
    Settles task (first.append second) := trans task left right

theorem execute (cache : Inquiry.Frame task) (rule : Prefix.Rule task.model.source.code)
    (accepted : Selection.acceptable task.model task.domain task.original cache.programme (Inquiry.proposal task cache rule))
    (live : Driving.Progress.Live cache.shell) : Settles task (Inquiry.execute task cache rule accepted live) :=
  trans task accepted (frame_advance task (Inquiry.commit task cache rule accepted))

theorem waitAt (cut fuel : Nat) (cache : Inquiry.Frame task) : Settles task (Inquiry.waitAt task cut fuel cache) := by
  induction fuel generalizing cache with
  | zero => exact stay task cache
  | succ fuel ih =>
      unfold Inquiry.waitAt
      split
      · exact append task _ _ (frame_advance task cache) (ih _)
      · exact stay task cache

theorem waitOwn (sender : Fin task.model.source.code.sites) (fuel : Nat) (cache : Inquiry.Frame task) :
    Settles task (Inquiry.waitOwn task sender fuel cache) := by
  induction fuel generalizing cache with
  | zero => exact stay task cache
  | succ fuel ih =>
      unfold Inquiry.waitOwn
      split
      · exact append task _ _ (frame_advance task cache) (ih _)
      · exact stay task cache

theorem activate (sender : Fin task.model.source.code.sites) (planned : Inquiry.Slot task)
    (cache : Inquiry.Frame task) : Settles task (Inquiry.activate task sender planned cache).path := by
  unfold Inquiry.activate
  split
  · rename_i live
    split
    · split
      · split
        · exact stay task cache
        · split
          · dsimp only
            split
            · exact stay task cache
            · rename_i accepted inspected
              split
              · exact execute task cache _ accepted live
              · split <;> exact execute task cache _ accepted live
          · exact stay task cache
      · exact stay task cache
    · exact stay task cache
  · exact stay task cache

theorem dispatch (sender : Fin task.model.source.code.sites)
    (statement : RequestAttestation.Statement (code := task.model.source.code))
    (cache : Inquiry.Frame task) : Settles task (Inquiry.dispatch task sender statement cache).path := by
  unfold Inquiry.dispatch
  split
  · rename_i live
    split
    · split
      · exact stay task cache
      · dsimp only
        split
        · exact stay task cache
        · rename_i accepted inspected
          split
          · exact execute task cache _ accepted live
          · split <;> exact execute task cache _ accepted live
    · exact stay task cache
  · exact stay task cache

theorem receive (statement : RequestAttestation.Statement (code := task.model.source.code))
    (wire : StageTransport.Wire (code := task.model.source.code)) (fuel : Nat) (cache : Inquiry.Frame task) :
    Settles task (Inquiry.receive task statement wire fuel cache).path := by
  induction fuel generalizing cache with
  | zero =>
      unfold Inquiry.receive
      split <;> exact stay task cache
  | succ fuel ih =>
      unfold Inquiry.receive
      split
      · dsimp only
        split
        · exact append task _ _ (frame_advance task cache) (ih _)
        · exact frame_advance task cache
      · exact stay task cache

theorem round (sender : Fin task.model.source.code.sites) (cache : Inquiry.Frame task) :
    Settles task (Inquiry.round task sender cache).path := by
  unfold Inquiry.round
  split
  · exact stay task cache
  · rename_i planned found
    dsimp only
    have waiting := waitAt task planned.body.cut (horizon task.domain+1) cache
    have activated := activate task sender planned (Inquiry.waitAt task planned.body.cut (horizon task.domain+1) cache).finish
    split
    · exact append task _ _ waiting activated
    · rename_i body activatedValue
      apply append task _ _ waiting
      apply append task _ _ activated
      apply append task _ _ (waitOwn task sender (horizon task.domain+1) _)
      split
      · exact dispatch task sender body.statement _
      · rename_i delivered sentValue
        exact append task _ _ (dispatch task sender body.statement _)
          (receive task delivered.statement delivered.wire (horizon task.domain+1) _)

theorem planning_wait (fuel : Nat) (cache : Inquiry.Frame task) :
    Settles task (Planning.wait task fuel cache).path := by
  induction fuel generalizing cache with
  | zero => exact stay task cache
  | succ fuel ih =>
      unfold Planning.wait
      split
      · split
        · exact stay task cache
        · exact append task _ _ (frame_advance task cache) (ih _)
      · exact stay task cache

theorem stage (cache : Inquiry.Frame task) : Settles task (Planning.stage task cache).path := by
  let event := Planning.fee task cache
  have base : Accepts task cache.programme (Inquiry.Frame.pack event.final).programme := turn task event
  unfold Planning.stage
  dsimp only
  split
  · split
    · exact trans task base (planning_wait task (horizon task.domain+1) (Inquiry.Frame.pack event.final))
    · exact base
  · exact base

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Preservation
