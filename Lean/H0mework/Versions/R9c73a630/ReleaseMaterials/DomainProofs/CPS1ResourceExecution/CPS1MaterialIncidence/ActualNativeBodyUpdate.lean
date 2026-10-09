import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeBiologicalBody
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeBodyGenome

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeBodyProbe
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate
open NativePaidEvent NativeAmmoniaDynamics NativeCPContinuationProbe NativePrepareNextProbe NativePrepareBinding
open NativeResumableProbe NativeAdoptionProbe NativeBodyGenomeProbe

variable {oldBody : CPS1BiologicalUpdate.Body} (receipt : LocalRepairReceipt oldBody)
  {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}
  (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)

theorem receipt_full_length : readProteinDamage receipt.nextBody.current.2.native.current = .fullLength := by
  rcases receipt.invariant.2.1 with ⟨_sample,_selected,_current,full,_missing,_birth⟩
  exact full

theorem receipt_origin : receipt.nextBody.origin = oldBody.origin := by
  rcases receipt.reopened with ⟨_update,_residual,_damage,_renewal,origin,_pending⟩
  exact origin

theorem receipt_pending : receipt.nextBody.pending = oldBody.pending := by
  rcases receipt.reopened with ⟨_update,_residual,_damage,_renewal,_origin,pending⟩
  exact pending

structure BodyInvariant (body : NativeBody receipt returned germ) : Prop where
  legacy : body.legacyRestriction = receipt.nextBody
  dna : native_dna body.current = CPS1Deamination.ExecutionReadout.readDNA
    (CPS1LiveEditing.liveResources receipt.nextBody.current.2.native.current)
  coding : native_coding body.current = CPS1LiveEditing.readCoding
    (CPS1LiveEditing.liveResources receipt.nextBody.current.2.native.current)
  peptide : native_peptide body.current = actualGenePeptide receipt.nextBody.current.2.native.current
  fullLength : native_damage body.current = .fullLength
  whole : body.current.stock.filterMap (NativeAdoptionProbe.Species.physical? returned germ) = [body.current.state] ∧
    body.current.charged = paid.parent.products.serial.after ∧
    body.current.charged.spent = paid.parent.products.serial.after.spent ∧
    body.current.stock.filterMap (NativeAdoptionProbe.Species.live? returned germ) = current.remaining
  fields : CPS1ElectronicEvolution.fields (rawField current) body.current.state.rawC =
    CPS1ElectronicEvolution.fields (basis current) body.current.state.occupied
  electrons : Matrix.trace (body.current.state.occupied * body.current.state.occupied.conjTranspose) =
    (electronCount source.nodes : ℂ)
  account : body.current.state.energy + body.current.state.reserve =
    returned.occurrence.physical.energy + returned.occurrence.physical.reserve
  origin : body.origin = oldBody.origin
  lastNative : body.lastNative = receipt.nextBody.lastNative
  reopened : body.reopened = receipt.nextBody.reopened
  pending : body.pending = oldBody.pending

theorem body_invariant (body : NativeBody receipt returned germ) : BodyInvariant receipt returned germ body :=
  ⟨body.legacy_actual,native_dna_source body.current,native_coding_source body.current,
    native_peptide_source body.current,(native_damage_source body.current).trans (receipt_full_length receipt),
    body.whole,body.fields,body.electrons,body.full_account,receipt_origin receipt,rfl,rfl,receipt_pending receipt⟩

def bodyEvent (body : NativeBody receipt returned germ) : NativeWrite returned germ body.current :=
  ⟨advanceNative body.current.state,rfl,runPulse body.current,rfl,advanceSource body.current,rfl⟩

def bodyWrite (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    NativeBody receipt returned germ :=
  ⟨event.next,body.history ++ [.written body.current event],germ.sourceActual⟩

theorem write_current (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    (bodyWrite receipt returned germ body event).current = advanceSource body.current := event.nextActual

theorem write_stock (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    (bodyWrite receipt returned germ body event).current.stock = event.execution.stock := by
  change event.next.stock = event.execution.stock
  rw [event.nextActual,event.executionActual]
  rfl

theorem write_state (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    (bodyWrite receipt returned germ body event).current.state = event.result.next := by
  change event.next.state = event.result.next
  rw [event.nextActual,advance_state,event.resultActual]

theorem write_pending (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    (bodyWrite receipt returned germ body event).current.pending = body.current.pending := by
  rw [write_current,advance_pending]

theorem write_cut (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    (bodyWrite receipt returned germ body event).current.cut = none := by
  rw [write_current,advance_cut]

theorem write_history (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    (bodyWrite receipt returned germ body event).history = body.history ++ [.written body.current event] := rfl

theorem write_account (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    (bodyWrite receipt returned germ body event).current.state.energy +
        (bodyWrite receipt returned germ body event).current.state.reserve =
      body.current.state.energy + body.current.state.reserve := by
  rw [write_state]
  exact native_result_account event.result

theorem write_strict (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    (bodyWrite receipt returned germ body event).current.state ≠ body.current.state := by
  intro same
  have identical : event.result.next = body.current.state := (write_state receipt returned germ body event).symm.trans same
  rcases native_result_progress event.result with advanced | refined
  · rw [identical] at advanced
    exact (lt_irrefl _ advanced)
  · have index := refined.2.1
    rw [identical] at index
    omega

theorem write_current_ne (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    (bodyWrite receipt returned germ body event).current ≠ body.current := by
  intro same
  exact write_strict receipt returned germ body event
    (congrArg (fun live : NativeSourceCurrent returned germ => live.state) same)

theorem write_genome (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    native_dna (bodyWrite receipt returned germ body event).current = native_dna body.current ∧
    native_coding (bodyWrite receipt returned germ body event).current = native_coding body.current ∧
    native_peptide (bodyWrite receipt returned germ body event).current = native_peptide body.current ∧
    native_damage (bodyWrite receipt returned germ body event).current = native_damage body.current := by
  rw [write_current]
  exact ⟨native_dna_advance _,native_coding_advance _,native_peptide_advance _,native_damage_advance _⟩

structure BodyUpdate (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current)
    (next : NativeBody receipt returned germ) : Prop where
  actual : next = bodyWrite receipt returned germ body event
  stock : next.current.stock = event.execution.stock
  state : next.current.state = event.result.next
  nativePending : next.current.pending = body.current.pending
  cut : next.current.cut = none
  history : next.history = body.history ++ [.written body.current event]
  account : next.current.state.energy + next.current.state.reserve = body.current.state.energy + body.current.state.reserve
  strict : next.current.state ≠ body.current.state

theorem body_write_law (body : NativeBody receipt returned germ) (event : NativeWrite returned germ body.current) :
    BodyUpdate receipt returned germ body event (bodyWrite receipt returned germ body event) :=
  ⟨rfl,write_stock receipt returned germ body event,write_state receipt returned germ body event,
    write_pending receipt returned germ body event,write_cut receipt returned germ body event,
    write_history receipt returned germ body event,write_account receipt returned germ body event,
    write_strict receipt returned germ body event⟩

/-- This court governs the native writer. The original repair court remains
the genomic restriction of this same body occurrence. -/
structure NativeBodyCourt where
  EventAt : NativeBody receipt returned germ → Type
  sourceEvent : (body : NativeBody receipt returned germ) → EventAt body
  write : (body : NativeBody receipt returned germ) → EventAt body → NativeBody receipt returned germ
  UpdateAt : (body : NativeBody receipt returned germ) → EventAt body → NativeBody receipt returned germ → Prop
  InvariantAt : NativeBody receipt returned germ → Prop
  updateLaw : ∀ body event, UpdateAt body event (write body event)
  invariantLaw : ∀ body, InvariantAt body

def native_body_court : NativeBodyCourt receipt returned germ :=
  ⟨fun body => NativeWrite returned germ body.current,bodyEvent receipt returned germ,
    bodyWrite receipt returned germ,BodyUpdate receipt returned germ,BodyInvariant receipt returned germ,
    body_write_law receipt returned germ,body_invariant receipt returned germ⟩

variable {returned germ}

structure NativeBodyUpdate (adopted : NativeAdoptedNext returned germ) where
  before : NativeBody receipt returned germ
  admissionActual : before = admit_body receipt returned germ adopted
  first : NativeWrite returned germ before.current
  firstActual : first = bodyEvent receipt returned germ before
  middle : NativeBody receipt returned germ
  firstWrite : middle = bodyWrite receipt returned germ before first
  firstLaw : BodyUpdate receipt returned germ before first middle
  middleInvariant : BodyInvariant receipt returned germ middle
  second : NativeWrite returned germ middle.current
  secondActual : second = bodyEvent receipt returned germ middle
  next : NativeBody receipt returned germ
  secondWrite : next = bodyWrite receipt returned germ middle second
  secondLaw : BodyUpdate receipt returned germ middle second next
  nextInvariant : BodyInvariant receipt returned germ next

namespace NativeBodyUpdate
variable {receipt} {adopted : NativeAdoptedNext returned germ}
  (update : NativeBodyUpdate receipt adopted)

theorem admitted_current : update.before.current = adopted.next := by
  rw [update.admissionActual,admission_current]

theorem first_kernel : update.middle.current = advanceSource update.before.current := by
  rw [update.firstWrite,write_current]

theorem second_kernel : update.next.current = advanceSource update.middle.current := by
  rw [update.secondWrite,write_current]

theorem two_kernel : update.next.current = advanceSource (advanceSource adopted.next) := by
  rw [update.second_kernel,update.first_kernel,update.admitted_current]

theorem pending_empty : update.next.current.pending = [] := by
  rw [update.two_kernel,advance_pending,advance_pending]
  exact adopted.next_pending

theorem history_exact : update.next.history =
    (update.before.history ++ [.written update.before.current update.first]) ++
      [.written update.middle.current update.second] := by
  rw [update.secondLaw.history,update.firstLaw.history]

theorem no_stale_first_current : update.middle.current ≠ update.before.current := by
  intro same
  exact update.firstLaw.strict (congrArg (fun live : NativeSourceCurrent returned germ => live.state) same)

theorem no_stale_second_current : update.next.current ≠ update.middle.current := by
  intro same
  exact update.secondLaw.strict (congrArg (fun live : NativeSourceCurrent returned germ => live.state) same)

end NativeBodyUpdate

theorem source_generated_native_body_update (adopted : NativeAdoptedNext returned germ) :
    Nonempty (NativeBodyUpdate receipt adopted) := by
  let before := admit_body receipt returned germ adopted
  let first := bodyEvent receipt returned germ before
  let middle := bodyWrite receipt returned germ before first
  let second := bodyEvent receipt returned germ middle
  let next := bodyWrite receipt returned germ middle second
  exact ⟨⟨before,rfl,first,rfl,middle,rfl,body_write_law receipt returned germ before first,
    body_invariant receipt returned germ middle,second,rfl,next,rfl,
    body_write_law receipt returned germ middle second,body_invariant receipt returned germ next⟩⟩

end
end CPS1MaterialIncidence.NativeBodyProbe
