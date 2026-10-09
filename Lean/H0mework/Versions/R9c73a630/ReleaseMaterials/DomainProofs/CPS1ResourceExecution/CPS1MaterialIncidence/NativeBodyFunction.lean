import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativeBodyUpdate
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeCPFocus

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace CPS1MaterialIncidence.NativeBodyFunctionProbe
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate
open NativePaidEvent NativeAmmoniaDynamics NativeCPContinuationProbe NativePrepareNextProbe NativePrepareBinding
open NativeResumableProbe NativeAdoptionProbe NativeBodyProbe NativeBodyGenomeProbe

variable {oldBody : CPS1BiologicalUpdate.Body} {receipt : LocalRepairReceipt oldBody}
  {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}
  {returned : NativePrepareNext paid continuation} {germ : NativeOriginGerm returned.occurrence}

/-- The five channels are the already-paid source edges. Their physical
response is read at this body's current event, without replaying the receipts. -/
structure ChannelRead (focus : CPFocus paid) (state : PostState current) where
  values : Fin 5 → ℝ
  protonLeaving : values 0 = focus.protonLeaving.read state
  protonForming : values 1 = focus.protonForming.read state
  hydroxylLeaving : values 2 = focus.hydroxylLeaving.read state
  atpLeaving : values 3 = focus.atpLeaving.read state
  atpForming : values 4 = focus.atpForming.read state

def channel_read (focus : CPFocus paid) (state : PostState current) : ChannelRead focus state :=
  ⟨![focus.protonLeaving.read state,focus.protonForming.read state,
      focus.hydroxylLeaving.read state,focus.atpLeaving.read state,focus.atpForming.read state],
    rfl,rfl,rfl,rfl,rfl⟩

inductive FunctionDisposition (focus : CPFocus paid) {state : PostState current} : NativePhysicalResult state → Type
  | positive (event : PaidStep state) (direction : StrictDirection focus state event.after) :
      FunctionDisposition focus (.paid event)
  | channelResidual (event : PaidStep state) (failed : ¬ StrictDirection focus state event.after) :
      FunctionDisposition focus (.paid event)
  | nondifferentiable (failed : ¬ FullSmooth state) :
      FunctionDisposition focus (.nondifferentiable failed)
  | collision (smooth : FullSmooth state) (failed : ¬ Body.ready (endPose state)) :
      FunctionDisposition focus (.collision smooth failed)
  | energyShortage (smooth : FullSmooth state) (ready : Body.ready (endPose state))
      (failed : ¬ energyPrice state ≤ state.reserve) :
      FunctionDisposition focus (.energyShortage smooth ready failed)

def function_disposition (focus : CPFocus paid) {state : PostState current}
    (result : NativePhysicalResult state) : FunctionDisposition focus result := by
  classical
  cases result with
  | paid event =>
      exact if direction : StrictDirection focus state event.after then .positive event direction
        else .channelResidual event direction
  | nondifferentiable failed => exact .nondifferentiable failed
  | collision smooth failed => exact .collision smooth failed
  | energyShortage smooth ready failed => exact .energyShortage smooth ready failed

def DispositionLaw (focus : CPFocus paid) {state : PostState current}
    {result : NativePhysicalResult state} (disposition : FunctionDisposition focus result) : Prop :=
  match disposition with
  | .positive event _ =>
      result.next = event.after ∧ StrictDirection focus state result.next ∧
        state.elapsed < result.next.elapsed ∧
        result.next.rawC = state.rawC + sourceCoefficient current * (result.next.occupied-state.occupied)
  | .channelResidual event _ =>
      result.next = event.after ∧ ¬ StrictDirection focus state result.next ∧
        state.elapsed < result.next.elapsed ∧
        result.next.rawC = state.rawC + sourceCoefficient current * (result.next.occupied-state.occupied)
  | .nondifferentiable _ =>
      ¬ FullSmooth state ∧ result.next = refineState state ∧
        result.next.pose = state.pose ∧ result.next.rawC = state.rawC ∧
        result.next.reserve = state.reserve ∧ result.next.time = state.time/2
  | .collision _ _ =>
      ¬ Body.ready (endPose state) ∧ result.next = refineState state ∧
        result.next.pose = state.pose ∧ result.next.rawC = state.rawC ∧
        result.next.reserve = state.reserve ∧ result.next.time = state.time/2
  | .energyShortage _ _ _ =>
      ¬ energyPrice state ≤ state.reserve ∧ result.next = refineState state ∧
        result.next.pose = state.pose ∧ result.next.rawC = state.rawC ∧
        result.next.reserve = state.reserve ∧ result.next.time = state.time/2

theorem disposition_law (focus : CPFocus paid) {state : PostState current}
    {result : NativePhysicalResult state} (disposition : FunctionDisposition focus result) :
    DispositionLaw focus disposition := by
  cases disposition with
  | positive event direction => exact ⟨rfl,direction,paid_clock event,paid_fullC_increment event⟩
  | channelResidual event failed => exact ⟨rfl,failed,paid_clock event,paid_fullC_increment event⟩
  | nondifferentiable failed => exact ⟨failed,rfl,rfl,rfl,rfl,refinement_time state⟩
  | collision smooth failed => exact ⟨failed,rfl,rfl,rfl,rfl,refinement_time state⟩
  | energyShortage smooth ready failed => exact ⟨failed,rfl,rfl,rfl,rfl,refinement_time state⟩

structure NativeBodyFunction (body : NativeBody receipt returned germ) where
  event : NativeWrite returned germ body.current
  eventActual : event = bodyEvent receipt returned germ body
  beforeRead : ChannelRead continuation.focus body.current.state
  afterRead : ChannelRead continuation.focus event.result.next
  disposition : FunctionDisposition continuation.focus event.result
  dispositionActual : disposition = function_disposition continuation.focus event.result
  next : NativeBody receipt returned germ
  writeActual : next = bodyWrite receipt returned germ body event

def source_generated_native_body_function (body : NativeBody receipt returned germ) : NativeBodyFunction body :=
  let event := bodyEvent receipt returned germ body
  ⟨event,rfl,channel_read continuation.focus body.current.state,
    channel_read continuation.focus event.result.next,function_disposition continuation.focus event.result,
    rfl,bodyWrite receipt returned germ body event,rfl⟩

namespace NativeBodyFunction
variable {body : NativeBody receipt returned germ} (function : NativeBodyFunction body)

theorem actual_result : function.event.result = advanceNative body.current.state := function.event.resultActual

theorem actual_execution : function.event.execution = runPulse body.current := function.event.executionActual

theorem actual_next : function.next = bodyWrite receipt returned germ body (bodyEvent receipt returned germ body) := by
  rw [function.writeActual,function.eventActual]

theorem next_state : function.next.current.state = function.event.result.next := by
  rw [function.writeActual]
  exact write_state receipt returned germ body function.event

theorem next_stock : function.next.current.stock = function.event.execution.stock := by
  rw [function.writeActual]
  exact write_stock receipt returned germ body function.event

theorem next_history : function.next.history = body.history ++ [.written body.current function.event] := by
  rw [function.writeActual]
  rfl

theorem actual_disposition : DispositionLaw continuation.focus function.disposition :=
  disposition_law continuation.focus function.disposition

theorem account : function.next.current.state.energy + function.next.current.state.reserve =
    body.current.state.energy + body.current.state.reserve := by
  rw [function.writeActual]
  exact write_account receipt returned germ body function.event

theorem whole : type_of% function.next.whole := function.next.whole
theorem fields : type_of% function.next.fields := function.next.fields
theorem electrons : type_of% function.next.electrons := function.next.electrons
theorem invariant : BodyInvariant receipt returned germ function.next := body_invariant receipt returned germ function.next

theorem genomic_read : native_damage function.next.current = native_damage body.current := by
  rw [function.writeActual]
  exact (write_genome receipt returned germ body function.event).2.2.2

theorem duties : function.next.pending = body.pending := rfl

theorem strict_state : function.next.current.state ≠ body.current.state := by
  rw [function.writeActual]
  exact write_strict receipt returned germ body function.event

end NativeBodyFunction

theorem unchanged_state_cannot_be_positive (focus : CPFocus paid) (state : PostState current) :
    ¬ StrictDirection focus state state := strict_direction_irrefl focus state

end
end CPS1MaterialIncidence.NativeBodyFunctionProbe
