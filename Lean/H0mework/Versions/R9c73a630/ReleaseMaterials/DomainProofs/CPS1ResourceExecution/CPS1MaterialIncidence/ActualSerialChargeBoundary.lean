import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualSerialProductRead

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

theorem native_incidence_material_charge_boundary (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current)
    (actual : nativeIncidence? source current = .ok trace)
    (seed : AtomOrigin cursor)
    (element : CPS1LocalChemicalExecution.PeptideMaterial.Element) :
    ∃ event : SourceMaterialStep source current,
      event.token = trace.selection.bond ∧
      stepSource? source current (materialInitial source current) = .ok event ∧
      componentFormula event.after.graph seed element =
        componentFormula trace.after.graph seed element ∧
      event.after.graph.formalCharge = trace.before.graph.formalCharge ∧
      trace.after.graph.formalCharge =
        trace.before.graph.formalCharge + trace.selection.token.delta ∧
      stepSource? source current event.after =
        .error (.reusedBond event.token.debit) := by
  obtain ⟨event, tokenEq, actualStep, incidenceEq, noRepeat⟩ :=
    native_incidence_material_serial_continuation current trace actual
  refine ⟨event, tokenEq, actualStep, ?_, ?_, ?_, noRepeat⟩
  · have compEq := component_incidence_congr event.after.graph trace.after.graph incidenceEq seed
    unfold componentFormula componentAtoms
    rw [compEq]
  · have starts := native_incidence_starts_full source current trace actual
    have eventBefore := step_source_before source current
      (materialInitial source current) event actualStep
    have beforeEq : event.before.graph = trace.before.graph := by
      rw [eventBefore]
      simp [materialInitial, MaterialState.graph, foldTokens, starts.1]
    calc
      event.after.graph.formalCharge = event.before.graph.formalCharge := step_charge event
      _ = trace.before.graph.formalCharge := congrArg OriginGraph.formalCharge beforeEq
  · rw [native_incidence_graph]
    rfl

end
end CPS1MaterialIncidence
