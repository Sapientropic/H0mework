import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualEventTrace

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

theorem native_incidence_actual_event_continuation (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current)
    (actual : nativeIncidence? source current = .ok trace) :
    trace.after.spent = trace.selection.token.debits ∧
      trace.after.graph = applyChargedToken trace.before.graph trace.selection.token ∧
      trace.whole.1 = current ∧
      trace.whole.1.nodes = current.nodes ∧
      trace.whole.1.occupied = current.occupied ∧
      trace.whole.1.materializedRaw = current.materializedRaw ∧
      trace.remaining = current.remaining ∧
      ((finiteSourceCARWord current).map (fun term =>
        term.phaseTerm • configurationSlater current term.after)).sum =
        CPS1ElectronicEvolution.slater
          (CPS1ElectronicEvolution.fields (addressedBasis current)
            (atomUpdatedOccupation current raw.time)) := by
  have starts := native_incidence_starts_full source current trace actual
  have spent := charged_record_spent trace.before trace.selection.token
  have spentActual : trace.after.spent = trace.selection.token.debits := by
    simpa only [NativeIncidenceTrace.after, starts.2, List.nil_append] using spent
  rcases native_incidence_actual_update_event current trace actual with
    ⟨_, _, graph, wholeCurrent, wholeNodes, wholeOccupied, wholeRaw, wholeRemaining, update⟩
  exact ⟨spentActual, graph, wholeCurrent, wholeNodes, wholeOccupied, wholeRaw,
    wholeRemaining, update⟩

end
end CPS1MaterialIncidence
