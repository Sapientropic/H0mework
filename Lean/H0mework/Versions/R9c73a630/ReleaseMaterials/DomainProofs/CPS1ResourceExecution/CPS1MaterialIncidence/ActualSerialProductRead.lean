import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualSerialContinuation

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

theorem component_incidence_congr {atoms : List (Atom cursor)}
    (left right : OriginGraph atoms) (incidence : left.incidence = right.incidence)
    (seed : AtomOrigin cursor) : component left seed = component right seed := by
  cases left with
  | mk leftInc leftCharge =>
    cases right with
    | mk rightInc rightCharge =>
      change leftInc = rightInc at incidence
      subst rightInc
      rfl

theorem native_incidence_material_component_formula (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current)
    (actual : nativeIncidence? source current = .ok trace)
    (seed : AtomOrigin cursor)
    (element : CPS1LocalChemicalExecution.PeptideMaterial.Element) :
    ∃ event : SourceMaterialStep source current,
      event.token = trace.selection.bond ∧
      stepSource? source current (materialInitial source current) = .ok event ∧
      componentFormula event.after.graph seed element =
        componentFormula trace.after.graph seed element ∧
      stepSource? source current event.after =
        .error (.reusedBond event.token.debit) := by
  obtain ⟨event, tokenEq, actualStep, incidenceEq, noRepeat⟩ :=
    native_incidence_material_serial_continuation current trace actual
  refine ⟨event, tokenEq, actualStep, ?_, noRepeat⟩
  have compEq := component_incidence_congr event.after.graph trace.after.graph incidenceEq seed
  unfold componentFormula componentAtoms
  rw [compEq]

end
end CPS1MaterialIncidence
