import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NormalSlaterAction
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

theorem finite_monomial_actual_slater_action (current : NativeCurrent source)
    (term : FiniteCARMonomial current) :
    term.operator (actualSourceSlater current) =
      term.phaseTerm • configurationSlater current term.after := by
  unfold FiniteCARMonomial.operator
  change term.coefficient •
    (normalCAROperator current term.after term.previous (actualSourceSlater current)) = _
  rw [normal_car_actual_slater_action]
  simp only [smul_smul]
  unfold FiniteCARMonomial.phaseTerm
  rw [mul_comm]

theorem finite_monomial_actual_slater_stock_consumer (current : NativeCurrent source)
    (term : FiniteCARMonomial current) :
    term.operator (actualSourceSlater current) =
        term.phaseTerm • configurationSlater current term.after ∧
      term.stock.state.whole.1 = current ∧
      term.stock.state.whole.1.occupied = current.occupied ∧
      term.stock.state.whole.1.remaining = current.remaining := by
  exact ⟨finite_monomial_actual_slater_action current term,
    finite_monomial_stock_whole term⟩
end
end CPS1MaterialIncidence
