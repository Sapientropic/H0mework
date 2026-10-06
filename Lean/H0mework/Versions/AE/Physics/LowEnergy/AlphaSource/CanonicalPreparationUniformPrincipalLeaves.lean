import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationUniformCentralFields

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumUniformFeed
open PreparationVacuumPrincipalBudget PreparationVacuumCentralBudget PreparationVacuumClockBudget
open PreparationVacuumClockJacobian PreparationVacuumClockSymbol PreparationVacuumDAGCoefficient
open PreparationVacuumCanonicalMoyal PreparationVacuumEngineBudget PreparationVacuumArenaRows
open PreparationVacuumEnergyTail
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

def principalLeafArray : Fin 14 → ArrayBound :=
  ![aArray,(fun _=>0),(fun _=>0),(fun _=>0),sArray,sArray,sArray,sArray,sArray,sArray,
    (fun _=>0),(fun _=>0),(fun _=>0),(fun _=>0)]

theorem spatialArray_nonnegative (m : ℕ) : 0 ≤ sArray m := by
  have t:=principal_arrays_nonnegative.2.1 m
  change 0 ≤ 3*sArray m at t
  linarith

theorem principalLeafArray_nonnegative (j : Fin 14) (m : ℕ) : 0 ≤ principalLeafArray j m := by
  fin_cases j <;> first | exact principal_arrays_nonnegative.1 m | exact spatialArray_nonnegative m | exact le_refl 0

-- These are the actual degree2 leaves, before the Engine's C,T normalization.
theorem actual_principalLeaf_budget (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ)
    (coefficients : CoefficientInputs x N) (j : Fin 14) :
    FiniteBound (originalLeaf 2 j) N (principalLeafArray j) x := by
  have ab:=actual_A_budget x hx box unit N coefficients
  have sb:=actual_S_budget x hx box unit N coefficients
  have zero : FiniteBound (fun _ : Phase=>(0 : ℝ)) N (fun _=>0) x := by
    intro m _ w
    cases m <;> simp [jet]
  refine Fin.lastCases ?_ (fun j=>?_) j
  · rw [originalLeaf_Y_zero]
    exact zero
  · have same : originalLeaf 2 (Fin.castSucc j)=
        (fun y=>originalPrincipalLeaves (PreparationActualFactor.nativePhase y).1
          (PreparationActualFactor.nativePhase y).2 j) := funext (originalLeaf_principal j)
    rw [same]
    fin_cases j
    · exact ab
    · exact zero
    · exact zero
    · exact zero
    all_goals
      first
      | exact zero
      | intro m hm w;exact rect_entry (sb m hm w) _ _

end LowEnergy.PreparationVacuumUniformFeed
