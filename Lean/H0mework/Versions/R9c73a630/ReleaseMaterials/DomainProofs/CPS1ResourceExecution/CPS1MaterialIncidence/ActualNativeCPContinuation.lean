import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeCPFocus

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeCPContinuationProbe
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativeCarbamoyl NativeAmmoniaDynamics

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}

inductive CPDisposition (paid : SourceGeneratedPaidReturn source current) (focus : CPFocus paid)
  | positive (event : PaidStep paid.physical) (direction : StrictDirection focus paid.physical event.after)
  | wrongDirection (event : PaidStep paid.physical) (failed : ¬ StrictDirection focus paid.physical event.after)
  | nondifferentiable (failed : ¬ FullSmooth paid.physical)
  | collision (smooth : FullSmooth paid.physical) (failed : ¬ Body.ready (endPose paid.physical))
  | energyShortage (smooth : FullSmooth paid.physical) (ready : Body.ready (endPose paid.physical))
      (failed : ¬ energyPrice paid.physical ≤ paid.physical.reserve)

def advanceCP (paid : SourceGeneratedPaidReturn source current) (focus : CPFocus paid) : CPDisposition paid focus := by
  classical
  exact if smooth : FullSmooth paid.physical then
    if ready : Body.ready (endPose paid.physical) then
      if budget : energyPrice paid.physical ≤ paid.physical.reserve then
        let event : PaidStep paid.physical := ⟨smooth,ready,budget⟩
        if direction : StrictDirection focus paid.physical event.after then .positive event direction
        else .wrongDirection event direction
      else .energyShortage smooth ready budget
    else .collision smooth ready
  else .nondifferentiable smooth

def CPDisposition.next {paid : SourceGeneratedPaidReturn source current} {focus : CPFocus paid} :
    CPDisposition paid focus → PostState current
  | .positive event _ => event.after
  | .wrongDirection event _ => event.after
  | .nondifferentiable _ | .collision _ _ | .energyShortage _ _ _ => refineState paid.physical

theorem cp_disposition_account {paid : SourceGeneratedPaidReturn source current} {focus : CPFocus paid}
    (result : CPDisposition paid focus) :
    result.next.energy + result.next.reserve = paid.physical.energy + paid.physical.reserve := by
  cases result with
  | positive event direction => exact paid_account event
  | wrongDirection event failed => exact paid_account event
  | nondifferentiable failed => rfl
  | collision smooth failed => rfl
  | energyShortage smooth ready failed => rfl

theorem cp_disposition_progress {paid : SourceGeneratedPaidReturn source current} {focus : CPFocus paid}
    (result : CPDisposition paid focus) :
    paid.physical.elapsed < result.next.elapsed ∨
      (result.next.elapsed = paid.physical.elapsed ∧ result.next.index = paid.physical.index+1 ∧
        result.next.pose = paid.physical.pose ∧ result.next.rawC = paid.physical.rawC ∧
        result.next.reserve = paid.physical.reserve) := by
  cases result with
  | positive event direction => exact Or.inl (paid_clock event)
  | wrongDirection event failed => exact Or.inl (paid_clock event)
  | nondifferentiable failed => exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl⟩
  | collision smooth failed => exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl⟩
  | energyShortage smooth ready failed => exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl⟩

def CPFieldUpdate {paid : SourceGeneratedPaidReturn source current} {focus : CPFocus paid}
    (result : CPDisposition paid focus) : Prop :=
  match result with
  | .positive _ _ | .wrongDirection _ _ =>
    result.next.rawC = paid.physical.rawC +
      sourceCoefficient current * (result.next.occupied-paid.physical.occupied)
  | .nondifferentiable _ | .collision _ _ | .energyShortage _ _ _ =>
    result.next.rawC = paid.physical.rawC ∧ result.next.time = paid.physical.time/2

theorem cp_field_update {paid : SourceGeneratedPaidReturn source current} {focus : CPFocus paid}
    (result : CPDisposition paid focus) : CPFieldUpdate result := by
  cases result with
  | positive event direction => exact paid_fullC_increment event
  | wrongDirection event failed => exact paid_fullC_increment event
  | nondifferentiable failed => exact ⟨rfl,refinement_time paid.physical⟩
  | collision smooth failed => exact ⟨rfl,refinement_time paid.physical⟩
  | energyShortage smooth ready failed => exact ⟨rfl,refinement_time paid.physical⟩

structure CPNativeContinuation (paid : SourceGeneratedPaidReturn source current) where
  focus : CPFocus paid
  result : CPDisposition paid focus
  actual : result = advanceCP paid focus

def CPNativeContinuation.after {paid : SourceGeneratedPaidReturn source current}
    (continuation : CPNativeContinuation paid) : PostState current := continuation.result.next

def CPNativeContinuation.chargedAnchor {paid : SourceGeneratedPaidReturn source current}
    (_continuation : CPNativeContinuation paid) : ChargedState source current := paid.parent.products.serial.after

def CPNativeContinuation.whole {paid : SourceGeneratedPaidReturn source current}
    (continuation : CPNativeContinuation paid) :
    PostState current × ChargedState source current × List (CPS1ReactiveField.LiveMaterial frame) :=
  (continuation.after,continuation.chargedAnchor,current.remaining)

theorem continuation_account {paid : SourceGeneratedPaidReturn source current}
    (continuation : CPNativeContinuation paid) :
    continuation.after.energy + continuation.after.reserve = paid.physical.energy + paid.physical.reserve :=
  cp_disposition_account continuation.result

theorem continuation_particles {paid : SourceGeneratedPaidReturn source current}
    (continuation : CPNativeContinuation paid) :
    continuation.after.pose.map Body.Node.particle = paid.physical.pose.map Body.Node.particle :=
  continuation.after.particles.trans paid.physical.particles.symm

theorem continuation_whole {paid : SourceGeneratedPaidReturn source current}
    (continuation : CPNativeContinuation paid) :
    continuation.whole.2.1 = paid.parent.products.serial.after ∧
      continuation.whole.2.1.spent = paid.parent.products.serial.after.spent ∧
      continuation.whole.2.2 = current.remaining := ⟨rfl,rfl,rfl⟩

theorem continuation_ne {paid : SourceGeneratedPaidReturn source current}
    (continuation : CPNativeContinuation paid) :
    Matrix.trace (continuation.after.occupied * continuation.after.occupied.conjTranspose) =
      (electronCount source.nodes : ℂ) := post_electron_number continuation.after

theorem source_generated_cp_native_continuation (paid : SourceGeneratedPaidReturn source current) :
    Nonempty (CPNativeContinuation paid) := by
  obtain ⟨focus⟩ := source_cp_focus paid
  exact ⟨⟨focus,advanceCP paid focus,rfl⟩⟩

end
end CPS1MaterialIncidence.NativeCPContinuationProbe
