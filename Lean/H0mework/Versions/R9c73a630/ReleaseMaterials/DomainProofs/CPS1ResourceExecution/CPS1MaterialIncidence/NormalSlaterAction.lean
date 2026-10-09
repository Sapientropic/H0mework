import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.CommonModeContraction
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
theorem normal_car_actual_slater_action (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    normalCAROperator current after previous (actualSourceSlater current) =
      ((atomNumberBasis current).repr
        (finiteNumberState current (atomOccupation current)) previous) •
        configurationSlater current after := by
  classical
  let state : AtomNumberSpace current :=
    finiteNumberState current (atomOccupation current)
  have expansion := (atomNumberBasis current).sum_repr state
  have synthesized := congrArg (atomNumberSynthesis current) expansion
  have actual : atomNumberSynthesis current state = actualSourceSlater current := by
    have h := finite_number_synthesis current (atomOccupation current)
    rw [atom_occupation_wave] at h
    simpa [state, actualSourceSlater, CPS1ElectronicEvolution.slater] using h
  rw [actual] at synthesized
  have acted := congrArg (normalCAROperator current after previous) synthesized
  simp only [map_sum, map_smul, atom_number_basis_physical] at acted
  simp only [normal_car_configuration] at acted
  simpa [state, Finset.sum_eq_single previous] using acted.symm
end
end CPS1MaterialIncidence

namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : CPS1SameEventFunction.Classical.Raw}
  {before : CPS1SameEventFunction.Classical.Current cursor priorRaw}
  {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
  {raw : Raw} {source : Common before step raw}

theorem normal_car_actual_slater_residual_consumer (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    commonCAROperator current previous after
        (changedGroupedOperator current previous after (actualSourceSlater current)) +
      normalOperatorResidual current previous after (actualSourceSlater current) =
      ((atomNumberBasis current).repr
        (finiteNumberState current (atomOccupation current)) previous) •
        configurationSlater current after := by
  have decomposition := congrArg
    (fun operator : Module.End ℂ SourceFermion => operator (actualSourceSlater current))
    (normal_operator_residual_decomposition current previous after)
  calc
    commonCAROperator current previous after
          (changedGroupedOperator current previous after (actualSourceSlater current)) +
        normalOperatorResidual current previous after (actualSourceSlater current) =
        canonicalNormalOperator current previous after (actualSourceSlater current) := by
          simpa [LinearMap.add_apply,LinearMap.comp_apply,canonicalNormalOperator] using decomposition.symm
    _ = ((atomNumberBasis current).repr
        (finiteNumberState current (atomOccupation current)) previous) •
        configurationSlater current after :=
      normal_car_actual_slater_action current previous after

theorem common_mode_empty_actual_slater_consumer (current : NativeCurrent source)
    (previous after : AtomConfiguration current)
    (empty : previous.val ∩ after.val = ∅) :
    commonCAROperator current previous after (actualSourceSlater current) =
      actualSourceSlater current := by
  rw [common_carrier_empty_consumer current previous after empty]
  rfl

end
end CPS1MaterialIncidence
