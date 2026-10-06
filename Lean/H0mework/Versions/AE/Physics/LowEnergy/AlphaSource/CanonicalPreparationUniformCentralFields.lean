import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrincipalArrays
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaSourceConsumers

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumUniformFeed
open PreparationVacuumPrincipalBudget PreparationVacuumCentralBudget PreparationVacuumClockBudget
open PreparationVacuumClockJacobian PreparationVacuumClockSymbol PreparationVacuumDAGCoefficient
open PreparationVacuumCanonicalMoyal PreparationVacuumEngineBudget PreparationVacuumArenaRows
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev ArrayBound := PreparationVacuumCentralBudget.ArrayBound

-- The source coefficient payer is the only unresolved principal input.
def actualCentralInputs (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (coefficients : CoefficientInputs (z,WithLp.toLp 2 u) N) :
    PrimitiveInputs (z,WithLp.toLp 2 u) N := by
  let x : Phase:=(z,WithLp.toLp 2 u)
  have hx : x∈poleDomain:=sourceUnit_admitted z u zbox ubox unit
  let generated:=generatedClockInputs x hx zbox unit N coefficients
  have cb : FiniteBound actualC N (cArray generated) x:=
    actual_C_budget z u zbox ubox unit N generated
  have sb:=actual_S_budget x hx zbox unit N coefficients
  have snonnegative : ∀ m,0 ≤ sArray m:=by
    intro m
    have t:=principal_arrays_nonnegative.2.1 m
    change 0 ≤ 3*sArray m at t
    linarith
  have fields : ∀ i,FiniteBound (fieldFunction i) N
      (fieldArrays (cArray generated) sArray i) x := by
    intro i
    fin_cases i
    · change FiniteBound actualC N (cArray generated) x
      exact cb
    · change FiniteBound actualT N tArray x
      exact actual_T_budget x hx zbox unit N coefficients
    all_goals
      change FiniteBound (fun y=>actualS y _ _) N sArray x
      intro m hm w
      exact rect_entry (sb m hm w) _ _
  refine {
    clock := cArray generated
    spatial := sArray
    clock_nonnegative := cArray_nonnegative generated
    spatial_nonnegative := snonnegative
    fields := fields
    A0 := aArray 0
    actualA_zero := ?_
  }
  have ab:=actual_A_budget x hx zbox unit N coefficients 0 (Nat.zero_le N) (fun i=>Fin.elim0 i)
  exact (le_abs_self (actualA x)).trans (by simpa only [jet,iteratedFDeriv_zero_apply] using ab)

end LowEnergy.PreparationVacuumUniformFeed
