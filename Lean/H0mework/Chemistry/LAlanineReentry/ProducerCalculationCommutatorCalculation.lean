import H0mework.Chemistry.LAlanineReentry.ProducerCalculationCommutatorVectors
import H0mework.Chemistry.LAlanineJointNext.ProducerCalculationCommutatorRowsCalculation

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.NormCalculation.Commutator

open Lean Elab Term Command Propagation.Interface
open JointNext.NormCalculation (matrixValues)
open JointNext.NormCalculation.Commutator (sourceRows sourceColumns rowCalculation rowCalculation_source readTotals)

noncomputable def iColumns (j : Basis) : List Int := (iRows j).map Neg.neg

theorem hColumns_exact (j : Basis) : sourceColumns hamiltonianNumerator j = hRows j :=
  (congrArg List.ofFn (funext (fun i => hamiltonian_swap i j))).trans (hRows_exact j)

theorem rColumns_exact (j : Basis) : sourceColumns currentRealNumerator j = rRows j :=
  (congrArg List.ofFn (funext (fun i => currentReal_swap i j))).trans (rRows_exact j)

theorem iColumns_exact (j : Basis) : sourceColumns currentImagNumerator j = iColumns j := by
  calc
    sourceColumns currentImagNumerator j = List.ofFn (fun i => -currentImagNumerator j i) :=
      congrArg List.ofFn (funext (fun i => currentImag_swap i j))
    _ = (sourceRows currentImagNumerator j).map Neg.neg :=
      List.ofFn_comp' (currentImagNumerator j) Neg.neg
    _ = iColumns j := congrArg (List.map Neg.neg) (iRows_exact j)

noncomputable def calculatedRealRow (i : Basis) : Nat :=
  rowCalculation (hRows i) (rRows i) (List.ofFn hRows) (List.ofFn rRows)
noncomputable def calculatedImagRow (i : Basis) : Nat :=
  rowCalculation (hRows i) (iRows i) (List.ofFn hRows) (List.ofFn iColumns)

theorem sourceRealRow_eq_calculated (i : Basis) :
    (∑ j : Basis, (∑ k : Basis,
      (hamiltonianNumerator i k * currentRealNumerator k j -
        currentRealNumerator i k * hamiltonianNumerator k j)).natAbs) = calculatedRealRow i := by
  apply (rowCalculation_source hamiltonianNumerator currentRealNumerator i).symm.trans
  unfold calculatedRealRow
  apply congrArg₂ (fun h g => rowCalculation h g (List.ofFn (sourceColumns hamiltonianNumerator))
    (List.ofFn (sourceColumns currentRealNumerator))) (hRows_exact i) (rRows_exact i) |>.trans
  exact congrArg₂ (rowCalculation (hRows i) (rRows i))
    (congrArg List.ofFn (funext hColumns_exact)) (congrArg List.ofFn (funext rColumns_exact))

theorem sourceImagRow_eq_calculated (i : Basis) :
    (∑ j : Basis, (∑ k : Basis,
      (hamiltonianNumerator i k * currentImagNumerator k j -
        currentImagNumerator i k * hamiltonianNumerator k j)).natAbs) = calculatedImagRow i := by
  apply (rowCalculation_source hamiltonianNumerator currentImagNumerator i).symm.trans
  unfold calculatedImagRow
  apply congrArg₂ (fun h g => rowCalculation h g (List.ofFn (sourceColumns hamiltonianNumerator))
    (List.ofFn (sourceColumns currentImagNumerator))) (hRows_exact i) (iRows_exact i) |>.trans
  exact congrArg₂ (rowCalculation (hRows i) (iRows i))
    (congrArg List.ofFn (funext hColumns_exact)) (congrArg List.ofFn (funext iColumns_exact))

elab "calculateReentryCommutator " channel:ident : command => liftTermElabM do
  let (fn, stored) ← match channel.getId with
    | `real => pure (``calculatedRealRow, ``JointNext.NormCalculation.targetRealNumerator)
    | `imag => pure (``calculatedImagRow, ``JointNext.NormCalculation.targetImagNumerator)
    | _ => throwError "Expected a registered real or imaginary channel"
  let h ← matrixValues ``hamiltonianNumerator
  let g ← matrixValues stored
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
    let type ← Meta.mkEq (mkApp (Lean.mkConst fn) index) (toExpr total)
    let value ← instantiateMVars (← Meta.mkDecideProof type)
    let type ← instantiateMVars type
    let name := (← getCurrNamespace) ++ `calculated ++ Name.mkSimple s!"row{i}"
    addDecl (.thmDecl { name, levelParams := [], type, value })
  let value := mkApp (Lean.mkConst ``readTotals) (← Meta.whnf (toExpr totals))
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ `rowTotals
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

end LAlanine40K2025.Reentry.NormCalculation.Commutator
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
