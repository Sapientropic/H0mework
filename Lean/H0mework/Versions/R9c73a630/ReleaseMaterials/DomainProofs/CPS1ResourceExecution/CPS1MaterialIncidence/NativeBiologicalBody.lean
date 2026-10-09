import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativeAdoptedNext

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeBodyProbe
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate
open NativePaidEvent NativeAmmoniaDynamics NativeCPContinuationProbe NativePrepareNextProbe NativePrepareBinding
open NativeResumableProbe NativeAdoptionProbe

section Native
variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}
  (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)

structure NativeWrite (before : NativeSourceCurrent returned germ) where
  result : NativePhysicalResult before.state
  resultActual : result = advanceNative before.state
  execution : NativeAdoptionProbe.Execution returned germ
  executionActual : execution = runPulse before
  next : NativeSourceCurrent returned germ
  nextActual : next = advanceSource before

inductive BodyStage
  | admission (adopted : NativeAdoptedNext returned germ)
  | written (before : NativeSourceCurrent returned germ) (event : NativeWrite returned germ before)

end Native

section Body
variable {oldBody : CPS1BiologicalUpdate.Body} (receipt : LocalRepairReceipt oldBody)
  {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}
  (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)

/-- The current is the native physical/resource authority. The legacy source
point is recovered from this same current and the actual repair receipt. -/
structure NativeBody where
  current : NativeSourceCurrent returned germ
  history : List (BodyStage returned germ)
  sourceActual : current.sourceRestriction = receipt.nextBody.current.2

def NativeBody.sourcePoint (body : NativeBody receipt returned germ) : SourcePoint :=
  ⟨receipt.nextBody.current.1,body.current.sourceRestriction⟩

def NativeBody.origin (_body : NativeBody receipt returned germ) : SourcePoint := receipt.nextBody.origin
def NativeBody.lastNative (_body : NativeBody receipt returned germ) : Option NativeSample := receipt.nextBody.lastNative
def NativeBody.reopened (_body : NativeBody receipt returned germ) : Option RenewalSample := receipt.nextBody.reopened
def NativeBody.pending (_body : NativeBody receipt returned germ) : List IndependentDuty := receipt.nextBody.pending

def NativeBody.legacyRestriction (body : NativeBody receipt returned germ) : CPS1BiologicalUpdate.Body :=
  ⟨body.origin,body.sourcePoint,body.lastNative,body.reopened,body.pending⟩

theorem NativeBody.source_point_actual (body : NativeBody receipt returned germ) :
    body.sourcePoint = receipt.nextBody.current := by
  change (⟨receipt.nextBody.current.1,body.current.sourceRestriction⟩ : SourcePoint) = receipt.nextBody.current
  rw [body.sourceActual]

theorem NativeBody.legacy_actual (body : NativeBody receipt returned germ) :
    body.legacyRestriction = receipt.nextBody := by
  change (⟨receipt.nextBody.origin,body.sourcePoint,receipt.nextBody.lastNative,
    receipt.nextBody.reopened,receipt.nextBody.pending⟩ : CPS1BiologicalUpdate.Body) = receipt.nextBody
  rw [body.source_point_actual]

def admit_body (adopted : NativeAdoptedNext returned germ) : NativeBody receipt returned germ :=
  ⟨adopted.next,[.admission adopted],germ.sourceActual⟩

theorem admission_current (adopted : NativeAdoptedNext returned germ) :
    (admit_body receipt returned germ adopted).current = adopted.next := rfl

theorem admission_history (adopted : NativeAdoptedNext returned germ) :
    (admit_body receipt returned germ adopted).history = [.admission adopted] := rfl

theorem NativeBody.whole (body : NativeBody receipt returned germ) :
    body.current.stock.filterMap (NativeAdoptionProbe.Species.physical? returned germ) = [body.current.state] ∧
    body.current.charged = paid.parent.products.serial.after ∧
    body.current.charged.spent = paid.parent.products.serial.after.spent ∧
    body.current.stock.filterMap (NativeAdoptionProbe.Species.live? returned germ) = current.remaining :=
  ⟨source_physical body.current,source_full_inventory body.current⟩

theorem NativeBody.fields (body : NativeBody receipt returned germ) :
    CPS1ElectronicEvolution.fields (rawField current) body.current.state.rawC =
      CPS1ElectronicEvolution.fields (basis current) body.current.state.occupied := source_field body.current

theorem NativeBody.electrons (body : NativeBody receipt returned germ) :
    Matrix.trace (body.current.state.occupied * body.current.state.occupied.conjTranspose) =
      (electronCount source.nodes : ℂ) := source_electrons body.current

theorem NativeBody.full_account (body : NativeBody receipt returned germ) :
    body.current.state.energy + body.current.state.reserve =
      returned.occurrence.physical.energy + returned.occurrence.physical.reserve := body.current.account

end Body
end
end CPS1MaterialIncidence.NativeBodyProbe
