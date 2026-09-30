import H0mework.Chemistry.LAlanineJointNext.ProducerCalculationCommutatorRowsVectors

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.NormCalculation.Commutator

open Lean Elab Term Command Tactic
open Propagation.Interface

noncomputable def calculatedRow (i : Basis) : Nat := rowCalculation (hRows i) (gRows i)
  (List.ofFn hColumns) (List.ofFn gColumns)
def readTotals (values : Array Nat) (i : Basis) : Nat := values[i.val]!

theorem sourceRow_eq_calculated (i : Basis) :
    (∑ j : Basis, (∑ k : Basis,
      (hamiltonianNumerator i k * gammaNumerator k j -
        gammaNumerator i k * hamiltonianNumerator k j)).natAbs) = calculatedRow i := by
  apply (rowCalculation_source hamiltonianNumerator gammaNumerator i).symm.trans
  unfold calculatedRow
  apply congrArg₂ (fun h g => rowCalculation h g (List.ofFn (sourceColumns hamiltonianNumerator))
    (List.ofFn (sourceColumns gammaNumerator))) (hRows_exact i) (gRows_exact i) |>.trans
  exact congrArg₂ (rowCalculation (hRows i) (gRows i))
    (congrArg List.ofFn (funext hColumns_exact)) (congrArg List.ofFn (funext gColumns_exact))

elab "calculateCommutatorRows" : command => liftTermElabM do
  let h ← matrixValues ``hamiltonianNumerator
  let g ← matrixValues ``gammaNumerator
  let mut totals : Array Nat := #[]
  for i in [:98] do
    let mut total := 0
    for j in [:98] do
      let entry := (List.range 98).foldl (fun a k => a +
        ((h[i]!)[k]! * (g[k]!)[j]! - (g[i]!)[k]! * (h[k]!)[j]!)) (0 : Int)
      total := total + entry.natAbs
    totals := totals.push total
    let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 98))
    let index := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 98) (mkNatLit i) inside
    let type ← Meta.mkEq (mkApp (Lean.mkConst ``calculatedRow) index) (toExpr total)
    let value ← instantiateMVars (← Meta.mkDecideProof type)
    let type ← instantiateMVars type
    let name := (← getCurrNamespace) ++ `calculated ++ Name.mkSimple s!"row{i}"
    addDecl (.thmDecl { name, levelParams := [], type, value })
  let value := mkApp (Lean.mkConst ``readTotals) (← Meta.whnf (toExpr totals))
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ `rowTotals
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

calculateCommutatorRows

elab "closeCommutatorCalculations" : tactic => do
  let goals ← getGoals
  unless goals.length == 98 do throwError "Wrong commutator row census"
  for (goal, i) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ `calculated ++ Name.mkSimple s!"row{i}"))
  setGoals []

theorem calculatedRows_exact (i : Basis) : calculatedRow i = rowTotals i := by
  fin_cases i
  closeCommutatorCalculations

theorem total_exact : (∑ i : Basis, calculatedRow i) = 861906379218130454 :=
  (Finset.sum_congr rfl (fun i _ => calculatedRows_exact i)).trans (by decide +kernel)

end LAlanine40K2025.JointNext.NormCalculation.Commutator
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
