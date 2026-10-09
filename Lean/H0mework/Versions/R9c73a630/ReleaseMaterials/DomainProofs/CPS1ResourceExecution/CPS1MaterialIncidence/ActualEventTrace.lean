import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualUpdateWholeStock

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

theorem native_incidence_actual_update_event (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current)
    (actual : nativeIncidence? source current = .ok trace) :
    trace.before.graph = sourceGraph source ∧
      trace.before.spent = [] ∧
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
  rcases native_incidence_starts_full source current trace actual with ⟨beforeGraph, beforeSpent⟩
  have graph := native_incidence_graph trace
  rcases native_incidence_whole trace with
    ⟨wholeCurrent, wholeNodes, wholeOccupied, wholeRaw, wholeRemaining⟩
  exact ⟨beforeGraph, beforeSpent, graph, wholeCurrent, wholeNodes, wholeOccupied,
    wholeRaw, wholeRemaining, finite_car_actual_update current⟩

end
end CPS1MaterialIncidence
