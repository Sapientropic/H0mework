import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativeBodyUpdate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeRootDataProbe
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate CPS1LiveEditing
open NativePaidEvent NativePaidPositive NativeAmmoniaDynamics NativeCPContinuationProbe
open NativePrepareNextProbe NativePrepareBinding NativeResumableProbe NativeAdoptionProbe
open NativeBodyGenomeProbe NativeBodyProbe

section Native
variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}
  (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)

def source_adopted_data : NativeAdoptedNext returned germ :=
  let adopted := adopted_current returned germ
  ⟨adopted,rfl,advanceNative adopted.state,rfl,runPulse adopted,rfl,advanceSource adopted,rfl⟩

end Native

section Body
variable {oldBody : CPS1BiologicalUpdate.Body} (receipt : LocalRepairReceipt oldBody)
  {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}
  (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)

/-- The high source and germ are family indices. The stored current, stock,
history and all later writes inhabit the root's actual Type0 data universe. -/
abbrev BodyAt : Type := NativeBody receipt returned germ

variable {returned germ}

def source_body_at (adopted : NativeAdoptedNext returned germ) : BodyAt receipt returned germ :=
  admit_body receipt returned germ adopted

def body_event_at (body : BodyAt receipt returned germ) : NativeWrite returned germ body.current :=
  bodyEvent receipt returned germ body

def body_write_at (body : BodyAt receipt returned germ) (event : NativeWrite returned germ body.current) :
    BodyAt receipt returned germ := bodyWrite receipt returned germ body event

def body_next (body : BodyAt receipt returned germ) : BodyAt receipt returned germ :=
  body_write_at receipt body (body_event_at receipt body)

theorem source_body_current (adopted : NativeAdoptedNext returned germ) :
    (source_body_at receipt adopted).current = adopted.next := rfl

theorem body_event_actual (body : BodyAt receipt returned germ) :
    (body_event_at receipt body).result = advanceNative body.current.state ∧
      (body_event_at receipt body).execution = runPulse body.current ∧
      (body_event_at receipt body).next = advanceSource body.current := ⟨rfl,rfl,rfl⟩

theorem body_write_actual (body : BodyAt receipt returned germ) (event : NativeWrite returned germ body.current) :
    body_write_at receipt body event = bodyWrite receipt returned germ body event := rfl

theorem body_next_kernel (body : BodyAt receipt returned germ) :
    (body_next receipt body).current = advanceSource body.current :=
  write_current receipt returned germ body (body_event_at receipt body)

theorem body_next_state (body : BodyAt receipt returned germ) :
    (body_next receipt body).current.state = (advanceNative body.current.state).next := rfl

theorem body_next_stock (body : BodyAt receipt returned germ) :
    (body_next receipt body).current.stock = (runPulse body.current).stock := rfl

theorem body_next_history (body : BodyAt receipt returned germ) :
    (body_next receipt body).history = body.history ++ [.written body.current (body_event_at receipt body)] := rfl

theorem body_next_law (body : BodyAt receipt returned germ) :
    BodyUpdate receipt returned germ body (body_event_at receipt body) (body_next receipt body) :=
  body_write_law receipt returned germ body (body_event_at receipt body)

theorem body_next_invariant (body : BodyAt receipt returned germ) :
    BodyInvariant receipt returned germ (body_next receipt body) :=
  body_invariant receipt returned germ (body_next receipt body)

theorem body_next_strict (body : BodyAt receipt returned germ) :
    (body_next receipt body).current.state ≠ body.current.state :=
  write_strict receipt returned germ body (body_event_at receipt body)

theorem body_next_genome (body : BodyAt receipt returned germ) :
    native_dna (body_next receipt body).current = native_dna body.current ∧
      native_coding (body_next receipt body).current = native_coding body.current ∧
      native_peptide (body_next receipt body).current = native_peptide body.current ∧
      native_damage (body_next receipt body).current = native_damage body.current :=
  write_genome receipt returned germ body (body_event_at receipt body)

def source_body_update_data (adopted : NativeAdoptedNext returned germ) : NativeBodyUpdate receipt adopted :=
  let before := source_body_at receipt adopted
  let first := body_event_at receipt before
  let middle := body_write_at receipt before first
  let second := body_event_at receipt middle
  let next := body_write_at receipt middle second
  ⟨before,rfl,first,rfl,middle,rfl,body_write_law receipt returned germ before first,
    body_invariant receipt returned germ middle,second,rfl,next,rfl,
    body_write_law receipt returned germ middle second,body_invariant receipt returned germ next⟩

theorem source_body_update_before (adopted : NativeAdoptedNext returned germ) :
    (source_body_update_data receipt adopted).before = source_body_at receipt adopted := rfl

theorem source_body_update_middle (adopted : NativeAdoptedNext returned germ) :
    (source_body_update_data receipt adopted).middle = body_next receipt (source_body_at receipt adopted) := rfl

theorem source_body_update_next (adopted : NativeAdoptedNext returned germ) :
    (source_body_update_data receipt adopted).next =
      body_next receipt (body_next receipt (source_body_at receipt adopted)) := rfl

end Body

section Source
variable {frame : CPS1Recycling.Frame} {origin : CPS1ReactiveNuclear.SourceCursor frame}
  {water : Nat} {material : List RawSupply} {path : CPS1Recycling.SplitSite}
  {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
  {physical : PhysicalRaw} {depth : Nat}
  (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
  (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
  (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
  (repaired : repairWhole whole supply = .repaired receipt)
  {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  (source : Common before step raw) {current : NativeCurrent source}
  (paid : SourceGeneratedPaidReturn source current) (continuation : CPNativeContinuation paid)

def source_prepared_data : NativePrepareNext paid continuation := by
  let occurrence := source_native_occurrence whole supply profile receipt repaired source paid continuation
  have actual := NativeFunctionalNextProbe.next_cp_only_exact whole supply profile receipt repaired paid.parent
  have requested : (NativePaidEvent.nextCursor paid.parent).pending = pendingTail :=
    congrArg CPS1Deformation.Source.Cursor.pending actual
  exact ⟨occurrence,requested,runPrepare (startCursor occurrence (NativePaidEvent.nextCursor paid.parent)),rfl,
    advancePrepare (startCursor occurrence (NativePaidEvent.nextCursor paid.parent)),rfl⟩

def GeneratedBodyAt : Type :=
  let returned := source_prepared_data whole supply profile receipt repaired source paid continuation
  BodyAt receipt returned (native_origin_germ returned.occurrence)

def source_generated_body_at : GeneratedBodyAt whole supply profile receipt repaired source paid continuation :=
  let returned := source_prepared_data whole supply profile receipt repaired source paid continuation
  let germ := native_origin_germ returned.occurrence
  source_body_at receipt (source_adopted_data returned germ)

def source_generated_body_next
    (body : GeneratedBodyAt whole supply profile receipt repaired source paid continuation) :
    GeneratedBodyAt whole supply profile receipt repaired source paid continuation := body_next receipt body

theorem generated_body_next_kernel
    (body : GeneratedBodyAt whole supply profile receipt repaired source paid continuation) :
    (source_generated_body_next whole supply profile receipt repaired source paid continuation body).current =
      advanceSource body.current := body_next_kernel receipt body

theorem generated_body_next_not_initial
    (body : GeneratedBodyAt whole supply profile receipt repaired source paid continuation) :
    (source_generated_body_next whole supply profile receipt repaired source paid continuation body).current.state ≠
      body.current.state := body_next_strict receipt body

end Source
end
end CPS1MaterialIncidence.NativeRootDataProbe
