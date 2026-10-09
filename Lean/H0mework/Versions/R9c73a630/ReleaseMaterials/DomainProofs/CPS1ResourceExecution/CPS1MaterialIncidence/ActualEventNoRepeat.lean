import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualEventContinuation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : CPS1SameEventFunction.Classical.Raw}
  {before : CPS1SameEventFunction.Classical.Current cursor priorRaw}
  {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
  {raw : Raw} {source : Common before step raw}

theorem native_incidence_after_reuse_guard (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current)
    (actual : nativeIncidence? source current = .ok trace) :
    ¬ (∀ bond ∈ trace.selection.token.debits, bond ∉ trace.after.spent) := by
  intro unused
  have continuation := native_incidence_actual_event_continuation current trace actual
  have debitHeld : trace.selection.bond.debit ∈ trace.selection.token.debits := by
    simp [IncidenceSelection.token, ChargedToken.debits]
  have spentHeld : trace.selection.bond.debit ∈ trace.after.spent := by
    rw [continuation.1]
    exact debitHeld
  exact unused trace.selection.bond.debit debitHeld spentHeld

end
end CPS1MaterialIncidence
