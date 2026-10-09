import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualLiteralWholeNext

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

theorem native_incidence_material_step (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current)
    (actual : nativeIncidence? source current = .ok trace) :
    ∃ event : SourceMaterialStep source current,
      event.token = trace.selection.bond ∧
      stepSource? source current (materialInitial source current) = .ok event := by
  classical
  have starts := native_incidence_starts_full source current trace actual
  have debitHeld : trace.selection.bond.debit ∈ trace.selection.token.debits := by
    simp [IncidenceSelection.token, ChargedToken.debits]
  have creditHeld : trace.selection.bond.credit ∈ trace.selection.token.credits := by
    simp [IncidenceSelection.token, ChargedToken.credits]
  let event : SourceMaterialStep source current :=
    { before := materialInitial source current
      token := trace.selection.bond
      sourceActual := trace.selection.bondActual
      unused := by simp [materialInitial, MaterialState.spent]
      debitPaid := by
        simpa [materialInitial, MaterialState.graph, foldTokens, starts.1] using
          trace.debitPaid trace.selection.bond.debit debitHeld
      creditFree := by
        simpa [materialInitial, MaterialState.graph, foldTokens, starts.1] using
          trace.creditFree trace.selection.bond.credit creditHeld }
  have token_eq {token : BondToken cursor} (held : sourceToken? source current = some token) :
      token = trace.selection.bond :=
    Option.some.inj (held.symm.trans trace.selection.bondActual)
  refine ⟨event, rfl, ?_⟩
  unfold stepSource?
  split
  · rename_i selected
    have impossible : (none : Option (BondToken cursor)) =
        some trace.selection.bond := selected.symm.trans trace.selection.bondActual
    cases impossible
  · rename_i token selected
    have same := token_eq selected
    subst token
    split
    · rename_i spent
      exfalso
      change trace.selection.bond.debit ∈ ([] : List (SourceBond cursor)) at spent
      exact List.not_mem_nil spent
    · split
      · rename_i paid
        split
        · rename_i empty
          simp [event, materialInitial]
        · rename_i empty
          exfalso
          apply empty
          simpa [materialInitial, MaterialState.graph, foldTokens, starts.1] using
            trace.creditFree trace.selection.bond.credit creditHeld
      · rename_i paid
        exfalso
        apply paid
        simpa [materialInitial, MaterialState.graph, foldTokens, starts.1] using
          trace.debitPaid trace.selection.bond.debit debitHeld

theorem native_incidence_material_serial_continuation (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current)
    (actual : nativeIncidence? source current = .ok trace) :
    ∃ event : SourceMaterialStep source current,
      event.token = trace.selection.bond ∧
      stepSource? source current (materialInitial source current) = .ok event ∧
      event.after.graph.incidence = trace.after.graph.incidence ∧
      stepSource? source current event.after =
        .error (.reusedBond event.token.debit) := by
  obtain ⟨event, tokenEq, actualStep⟩ := native_incidence_material_step current trace actual
  refine ⟨event, tokenEq, actualStep, ?_, step_cannot_repeat event⟩
  have starts := native_incidence_starts_full source current trace actual
  have eventBefore := step_source_before source current
    (materialInitial source current) event actualStep
  have beforeEq : event.before.graph = trace.before.graph := by
    rw [eventBefore]
    simp [materialInitial, MaterialState.graph, foldTokens, starts.1]
  rw [step_graph event, native_incidence_graph, beforeEq, tokenEq]
  simp only [applyToken, applyChargedToken]
  rw [selected_incidence_delta]

end
end CPS1MaterialIncidence
