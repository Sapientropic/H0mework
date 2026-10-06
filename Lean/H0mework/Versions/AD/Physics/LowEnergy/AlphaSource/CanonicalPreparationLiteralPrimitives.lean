import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralAtoms
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationNumericCompleteArrays

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLiteralFeed
open PreparationVacuumLiteralAdmission PreparationVacuumNumericSource
open PreparationVacuumCentralBudget PreparationVacuumPrincipalBudget PreparationVacuumArenaRows
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumCanonicalMoyal
open PreparationVacuumEngineBudget PreparationVacuumUniformFeed PreparationVacuumPoleCancellation
open PreparationVacuumClockBudget PreparationVacuumLowerAssembly
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators

-- Degree two is an extension for the generic carrier, not a Python source atom.
-- The actual source constructor uses .principal and therefore a central row.
def literalLeafArrays (d : Fin 3) (j : Fin 14) : PreparationVacuumCentralBudget.ArrayBound :=
  Fin.lastCases (principalLeafArray j) (fun e=>literalLowerAtoms e j) d

def literalPrimitiveArrays : PrimitiveArrays 0 where
  leaf:=literalLeafArrays
  clock:=sourcePrimitiveArrays.clock
  central:=sourceCentralArray

theorem literal_leaf_dominates (d : Fin 3) (j : Fin 14) :
    Dominates (sourceLeafArrays d j) (literalLeafArrays d j) := by
  induction d using Fin.lastCases with
  | last => simp only [sourceLeafArrays,literalLeafArrays,Fin.lastCases_last];exact fun _=>le_rfl
  | cast d => simpa only [sourceLeafArrays,literalLeafArrays,Fin.lastCases_castSucc] using lower_arrays_admitted d j

theorem literal_primitive_nonnegative : PrimitiveNonnegative literalPrimitiveArrays where
  leaf d j m := (sourceLeafArrays_nonnegative d j m).trans (literal_leaf_dominates d j m)
  clock := source_primitive_nonnegative.clock
  central := source_primitive_nonnegative.central

theorem literal_primitive_bounds (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) :
    PrimitiveBounds literalPrimitiveArrays N (z,WithLp.toLp 2 u) := by
  have actual:=source_primitive_bounds z u zbox ubox unit N
  refine ⟨?_,actual.clock,actual.central⟩
  intro d j m hm w
  exact (actual.leaf d j m hm w).trans (literal_leaf_dominates d j m)

theorem literal_lower_readback (d : Fin 2) (j : Fin 14) :
    literalPrimitiveArrays.leaf (Fin.castSucc d) j=literalLowerAtoms d j := by
  simp only [literalPrimitiveArrays,literalLeafArrays,Fin.lastCases_castSucc]

theorem literal_central_readback (c : NormalizedCoefficient) :
    literalPrimitiveArrays.central c=sourceCentralArray c := rfl

theorem actual_principal_is_central (j : Fin 13) :
    compilePrimitive (.principal j)=.row (principalCoefficient j) [] := rfl

theorem source_zero_erasure (j : Fin 13) :
    erase (sourceTerm 0 j)=Expression.primitive (.principal j) := rfl

theorem source_first_erasure (j : Fin 13) :
    erase (sourceTerm 1 j)=Expression.primitive (.leaf 1 (Fin.castSucc j)) := rfl

theorem source_later_erasure (n : ℕ) (j : Fin 13) :
    erase (sourceTerm (n+3) j)=Expression.primitive (.literal 0) := rfl

theorem source_second_erasure (j : Fin 13) :
    erase (sourceTerm 2 j)=Expression.addS
      (.primitive (.leaf 0 (Fin.castSucc j)))
      (if j=0 then .primitive (.leaf 0 (Fin.last 13)) else .primitive (.literal 0)) := by
  fin_cases j <;> rfl

end LowEnergy.PreparationVacuumLiteralFeed
