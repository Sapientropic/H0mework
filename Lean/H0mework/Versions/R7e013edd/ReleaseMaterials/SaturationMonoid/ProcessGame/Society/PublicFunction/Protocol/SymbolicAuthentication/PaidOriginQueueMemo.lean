import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginHeader
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedDispatchTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueMemo
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedDispatchTrace

-- This is the same accepted predecessor; its cursor retains the incrementally selected rules.
@[irreducible] def previousTrace := CachedCommandRun.run ProductiveDispatchSource.model
 ProductiveDispatchSource.start ProductiveDispatchTrace.emitted

def cachedPoint := PaidInvocationRebase.cursor
 (PaidInvocationSource.paid DispatchWindowSource.old DispatchWindowSource.contract previousTrace.cursor true true)
 DispatchWindowSource.contract.steps

theorem point_is_the_incrementally_computed_paid_successor : point = cachedPoint :=
 point_is_the_original_checked_paid_successor.trans
  (congrArg (fun cursor : Cursor DispatchWindowSource.old => PaidInvocationRebase.cursor
   (PaidInvocationSource.paid DispatchWindowSource.old DispatchWindowSource.contract cursor true true)
   DispatchWindowSource.contract.steps) previousTrace.cursor_eq.symm)

abbrev old := RenewedDispatchSource.code point
abbrev origin := RenewedDispatchSource.start point
def inputs := RenewedDispatchTrace.inputs.take 21 ++ [.idle]
def state := LocalCommandRun.run (RenewedDispatchSource.model point) origin inputs
-- Keep the large computed prefix opaque to elaboration; kernel checks still reduce its literal source.
@[irreducible] def traceAt (point : Cursor DispatchWindowSource.code) :=
 CachedCommandRun.run (RenewedDispatchSource.model point) (RenewedDispatchSource.start point) inputs
def cache := traceAt point
def past := state.stages
abbrev saved := PaidOriginQueue.saved old origin past

private theorem cache_seed
 (model : Native.Authority.Bound (Party := Bool) (Good := Bool)
  (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit))
 (origin : Cursor model.source.code) (state : LocalCommandRun.State model origin)
 (cache : CachedCommandRun.Cache model origin state) :
 EventStep.seed (state.current model origin) = cache.before := by
 rw [← cache.cursor_eq]
 exact cache.before_eq.symm

theorem saved_seed_is_the_actual_incremental_state : EventStep.seed saved = cache.before :=
 cache_seed (RenewedDispatchSource.model point) origin state cache

theorem saved_is_the_actual_incremental_endpoint : saved = cache.cursor := cache.cursor_eq.symm
theorem rows_are_the_actual_incremental_history : StageTrace.records origin past = cache.rows := cache.rows_eq.symm

def contract : PaidInvocationSource.Contract (Party := Bool) (Good := Bool)
 (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit) :=
 DispatchWindowSource.contract
abbrev code := PaidInvocationSource.code old contract

theorem actual_payment_and_acceptance_generate_the_next_window :
 PaidInvocationSource.admitted old contract saved true true = true := by
 rw [saved_is_the_actual_incremental_endpoint]
 unfold cache
 exact (congrArg (fun point : Cursor DispatchWindowSource.code =>
  PaidInvocationSource.admitted (RenewedDispatchSource.code point) contract
   (traceAt point).cursor true true)
  point_is_the_incrementally_computed_paid_successor).trans (by decide +kernel)

theorem ready : PaidOriginQueue.Ready old contract origin past true true :=
 PaidOriginQueue.fromPayment old contract origin past rfl actual_payment_and_acceptance_generate_the_next_window

theorem the_actual_source_plan_generates_ready :
 PaidOriginQueue.plan old contract origin past true true = .ready ready :=
 PaidOriginQueue.ready_was_generated_by_the_actual_source_check ready

abbrev start := ready.start
abbrev final := ready.final
abbrev row := ready.row 1
abbrev vocabulary := RenewedDispatchSource.vocabulary point
def law : StageReception.Law code := ⟨fun _ _ => RenewedDispatchSource.scope point,5⟩
def shortLaw : StageReception.Law code := ⟨fun _ _ => RenewedDispatchSource.scope point,1⟩
def wireAt (point : Cursor DispatchWindowSource.code) : HeaderTransport.Wire (code := RenewedDispatchSource.code point) :=
 (CachedWorkDispatch.issuedAt (RenewedDispatchSource.vocabulary point) (traceAt point).rows 20).getD
  ⟨0,0,RenewedDispatchSource.one point,⟨0,by change 0 < 1;decide⟩,0,
    ⟨0,0,RenewedDispatchSource.zero point,false,RenewedDispatchSource.scope point,true,0⟩⟩
def wire : HeaderTransport.Wire (code := old) := wireAt point



abbrev fundedAt (point : Cursor DispatchWindowSource.code) :=
 PaidInvocationRebase.cursor (PaidInvocationSource.paid (RenewedDispatchSource.code point) contract (traceAt point).cursor true true) contract.steps

def newPhaseLaw : StageReception.Law code :=
 ⟨fun _ _ => {RenewedDispatchSource.scope point with phase := (fundedAt point).cut},5⟩

theorem start_is_the_original_incremental_payment_endpoint : start = fundedAt point :=
 congrArg (fun cursor : Cursor old => PaidInvocationRebase.cursor
  (PaidInvocationSource.paid old contract cursor true true) contract.steps) saved_is_the_actual_incremental_endpoint


def paymentStartAt (point : Cursor DispatchWindowSource.code) :=
 PaidInvocationSource.start (RenewedDispatchSource.code point) contract (traceAt point).cursor
def paidModel (point : Cursor DispatchWindowSource.code) : Native.Authority.Bound (Party := Bool) (Good := Bool)
 (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit) :=
 ⟨ProductiveMandateSource.base,ProductiveMandateSource.scope,(paymentStartAt point).source,rfl,rfl⟩
def beforePayment (point : Cursor DispatchWindowSource.code) :=
 Extension.state (RenewedDispatchSource.code point)
  (CatalogueHandoffSource.supply (RenewedDispatchSource.code point)
   (PaidInvocationSource.catalogue (RenewedDispatchSource.code point) contract)) (traceAt point).before
def paymentAt (point : Cursor DispatchWindowSource.code) :=
 CachedCommandRun.materialAt (paidModel point) (paymentStartAt point) (beforePayment point)
  (PaidInvocationSource.protocol (RenewedDispatchSource.code point) contract true) (EventStep.fixed none)
def acceptanceCursorAt (point : Cursor DispatchWindowSource.code) :=
 (paymentStartAt point).after (PaidInvocationSource.protocol (RenewedDispatchSource.code point) contract true) (EventStep.fixed none)
def acceptanceAt (point : Cursor DispatchWindowSource.code) :=
 CachedCommandRun.materialAt (paidModel point) (acceptanceCursorAt point) (paymentAt point).after
  SilentWindow.quiet (PaidInvocationSource.supplier (RenewedDispatchSource.code point) contract true)
def fundedBeforeAt (point : Cursor DispatchWindowSource.code) :=
 PaidInvocationRebase.credit (acceptanceAt point).after contract.steps
def liftedAt (point : Cursor DispatchWindowSource.code) :=
 PaidOriginQueue.lifted (RenewedDispatchSource.code point) contract (RenewedDispatchSource.start point)
def queueEnvironmentAt (point : Cursor DispatchWindowSource.code) :=
 QueueScheduler.opponent (PaidInvocationSource.code (RenewedDispatchSource.code point) contract)
  (OriginQueue.baseline (RenewedDispatchSource.start point))

theorem queue_environment_is_the_original_environment :
 queueEnvironmentAt point = OriginQueue.environment (liftedAt point) :=
 congrArg (QueueScheduler.opponent code) ready.original_baseline.symm

def firstAt (point : Cursor DispatchWindowSource.code) :=
 CachedCommandRun.materialAt (paidModel point) (fundedAt point) (fundedBeforeAt point)
  SilentWindow.quiet (queueEnvironmentAt point)
def secondCursorAt (point : Cursor DispatchWindowSource.code) :=
 (fundedAt point).after SilentWindow.quiet (queueEnvironmentAt point)
def secondAt (point : Cursor DispatchWindowSource.code) :=
 CachedCommandRun.materialAt (paidModel point) (secondCursorAt point) (firstAt point).after
  SilentWindow.quiet (queueEnvironmentAt point)

private theorem execute_side {code : Code Bool Bool ProductiveMandateSource.Port (Mandate.State Bool Bool) Unit}
 (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
 (EventHistory.execute start stages).side = start.side := by
 induction stages generalizing start with
 | nil => rfl
 | cons stage tail ih => exact ih (start.after stage.1 stage.2)

theorem incremental_cursor_is_original : (traceAt point).cursor.side = .original := by
 rw [(traceAt point).cursor_eq]
 exact (execute_side origin past).trans rfl

theorem payment_seed_is_the_original_incremental_state :
 beforePayment point = EventStep.seed (paymentStartAt point) :=
 (congrArg (Extension.state old (CatalogueHandoffSource.supply old (PaidInvocationSource.catalogue old contract)))
  (traceAt point).before_eq).trans
   (CatalogueHandoffSource.seed old (PaidInvocationSource.catalogue old contract)
    (traceAt point).cursor incremental_cursor_is_original).symm

theorem payment_is_the_original_row : paymentAt point =
 PaidInvocationSource.paymentRow old contract (traceAt point).cursor true :=
 CachedCommandRun.materialAt_eq (paidModel point) (paymentStartAt point) (beforePayment point)
  payment_seed_is_the_original_incremental_state _ _

theorem payment_after_is_the_original_seed :
 (paymentAt point).after = EventStep.seed (acceptanceCursorAt point) :=
 (congrArg (fun record : StageTrace.Record (code := code) => record.after) payment_is_the_original_row).trans
  (StageTrace.material_is_the_actual_step (paymentStartAt point)
   (PaidInvocationSource.protocol old contract true) (EventStep.fixed none)).1

theorem acceptance_is_the_original_row : acceptanceAt point =
 PaidInvocationSource.acceptanceRow old contract (traceAt point).cursor true true :=
 CachedCommandRun.materialAt_eq (paidModel point) (acceptanceCursorAt point) (paymentAt point).after
  payment_after_is_the_original_seed _ _

theorem acceptance_after_is_the_original_paid_seed : (acceptanceAt point).after =
 EventStep.seed (PaidInvocationSource.paid old contract (traceAt point).cursor true true) :=
 (congrArg (fun record : StageTrace.Record (code := code) => record.after) acceptance_is_the_original_row).trans
  (StageTrace.material_is_the_actual_step (acceptanceCursorAt point) SilentWindow.quiet
   (PaidInvocationSource.supplier old contract true)).1

theorem funded_seed_is_the_original_incremental_state :
 EventStep.seed (fundedAt point) = fundedBeforeAt point := by
 have admitted : PaidInvocationSource.admitted old contract (traceAt point).cursor true true = true :=
  (congrArg (fun cursor : Cursor old => PaidInvocationSource.admitted old contract cursor true true)
   saved_is_the_actual_incremental_endpoint).symm.trans actual_payment_and_acceptance_generate_the_next_window
 exact (PaidInvocationSource.paid_opening_preserves_the_entire_actual_endpoint old contract
  (traceAt point).cursor true true admitted).trans
   (congrArg (fun before : Feedback.State code => PaidInvocationRebase.credit before contract.steps)
    acceptance_after_is_the_original_paid_seed.symm)

theorem actual_seed_is_the_original_incremental_state : EventStep.seed start = fundedBeforeAt point := by
 let seed : Cursor code → Feedback.State code := fun cursor =>
  cursor.source.feedbackState cursor.entry cursor.cut
 have transport : EventStep.seed start = EventStep.seed (fundedAt point) :=
  congrArg seed start_is_the_original_incremental_payment_endpoint
 exact transport.trans funded_seed_is_the_original_incremental_state

theorem first_is_the_original_row : firstAt point =
 OriginQueue.row (liftedAt point) (fundedAt point) (fun _ => SilentWindow.quiet) 0 := by
 change CachedCommandRun.materialAt (paidModel point) (fundedAt point) (fundedBeforeAt point)
  SilentWindow.quiet (queueEnvironmentAt point) =
  StageTrace.material (fundedAt point) SilentWindow.quiet (OriginQueue.environment (liftedAt point))
 rw [queue_environment_is_the_original_environment]
 exact CachedCommandRun.materialAt_eq (paidModel point) (fundedAt point) (fundedBeforeAt point)
  funded_seed_is_the_original_incremental_state.symm _ _

theorem first_after_is_the_original_seed : (firstAt point).after = EventStep.seed (secondCursorAt point) :=
 (congrArg (fun record : StageTrace.Record (code := code) => record.after)
  (CachedCommandRun.materialAt_eq (paidModel point) (fundedAt point) (fundedBeforeAt point)
   funded_seed_is_the_original_incremental_state.symm SilentWindow.quiet (queueEnvironmentAt point))).trans
  (StageTrace.material_is_the_actual_step (fundedAt point) SilentWindow.quiet (queueEnvironmentAt point)).1

theorem second_is_the_original_row : secondAt point =
 OriginQueue.row (liftedAt point) (fundedAt point) (fun _ => SilentWindow.quiet) 1 := by
 have result := CachedCommandRun.materialAt_eq (paidModel point) (secondCursorAt point) (firstAt point).after
  first_after_is_the_original_seed SilentWindow.quiet (queueEnvironmentAt point)
 change secondAt point = StageTrace.material
  ((fundedAt point).after SilentWindow.quiet (OriginQueue.environment (liftedAt point)))
  SilentWindow.quiet (OriginQueue.environment (liftedAt point))
 exact result.trans (congrArg (fun environment => StageTrace.material
  ((fundedAt point).after SilentWindow.quiet environment) SilentWindow.quiet environment)
  queue_environment_is_the_original_environment)

theorem actual_first_is_the_incremental_row : ready.row 0 = firstAt point :=
 (congrArg (fun cursor : Cursor code => OriginQueue.row (liftedAt point) cursor (fun _ => SilentWindow.quiet) 0)
  start_is_the_original_incremental_payment_endpoint).trans first_is_the_original_row.symm

theorem actual_second_is_the_incremental_row : ready.row 1 = secondAt point :=
 (congrArg (fun cursor : Cursor code => OriginQueue.row (liftedAt point) cursor (fun _ => SilentWindow.quiet) 1)
  start_is_the_original_incremental_payment_endpoint).trans second_is_the_original_row.symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueMemo
