import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNormalTrace

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

theorem finite_car_actual_update (current : NativeCurrent source) :
    ((finiteSourceCARWord current).map (fun term =>
      term.phaseTerm • configurationSlater current term.after)).sum =
      CPS1ElectronicEvolution.slater
        (CPS1ElectronicEvolution.fields (addressedBasis current)
          (atomUpdatedOccupation current raw.time)) := by
  calc
    ((finiteSourceCARWord current).map (fun term =>
        term.phaseTerm • configurationSlater current term.after)).sum =
        ((finiteSourceCARWord current).map FiniteCARMonomial.operator).sum
          (actualSourceSlater current) := by
      symm
      induction finiteSourceCARWord current with
      | nil => rfl
      | cons term rest ih =>
        simp only [List.map_cons, List.sum_cons, LinearMap.add_apply]
        rw [finite_monomial_actual_slater_action current term, ih]
    _ = CPS1ElectronicEvolution.slater
        (CPS1ElectronicEvolution.fields (addressedBasis current)
          (atomUpdatedOccupation current raw.time)) :=
      finite_car_actual_slater current

theorem finite_car_actual_update_whole_stock_consumer (current : NativeCurrent source) :
    ((finiteSourceCARWord current).map (fun term =>
      term.phaseTerm • configurationSlater current term.after)).sum =
        CPS1ElectronicEvolution.slater
          (CPS1ElectronicEvolution.fields (addressedBasis current)
            (atomUpdatedOccupation current raw.time)) ∧
      (finiteCARTrace source current).stockCalculations =
        (finiteCARTrace source current).word.map FiniteCARMonomial.stock ∧
      ∀ term : FiniteCARMonomial current,
        term.stock.state.whole.1 = current ∧
          term.stock.state.whole.1.occupied = current.occupied ∧
          term.stock.state.whole.1.remaining = current.remaining := by
  refine ⟨finite_car_actual_update current, (finiteCARTrace source current).stockActual, ?_⟩
  intro term
  exact finite_monomial_stock_whole term

end
end CPS1MaterialIncidence
