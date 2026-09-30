import H0mework.Chemistry.LAlanineJointNext.ProducerCalculationCommutatorRowsAlgebra

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.NormCalculation.Commutator

open Lean Elab Term Command Tactic
open Propagation.Interface

def readVectors (vectors : Array (List Int)) (i : Basis) : List Int := vectors[i.val]!

elab "generateCommutatorVectors" : command => liftTermElabM do
  let h ← matrixValues ``hamiltonianNumerator
  let g ← matrixValues ``gammaNumerator
  for (family, source, direction, values) in [(`hRows, ``hamiltonianNumerator, ``sourceRows, h),
      (`gRows, ``gammaNumerator, ``sourceRows, g),
      (`hColumns, ``hamiltonianNumerator, ``sourceColumns, h),
      (`gColumns, ``gammaNumerator, ``sourceColumns, g)] do
    let mut references := #[]
    for i in [:98] do
      let vector := if direction == ``sourceRows then values[i]!.toList
        else (List.range 98).map (fun k => (values[k]!)[i]!)
      let name := (← getCurrNamespace) ++ family ++ Name.mkSimple s!"row{i}"
      let value := toExpr vector
      let type ← Meta.inferType value
      addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
      let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 98))
      let index := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 98) (mkNatLit i) inside
      let left := mkApp2 (Lean.mkConst direction) (Lean.mkConst source) index
      let type ← Meta.mkEq left (Lean.mkConst name)
      let value ← instantiateMVars (← Meta.mkEqRefl left)
      let type ← instantiateMVars type
      addDecl (.thmDecl { name := name ++ `exact, levelParams := [], type, value })
      references := references.push (Lean.mkConst name)
    let array ← Meta.mkArrayLit (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Int)) references.toList
    let value := mkApp (Lean.mkConst ``readVectors) (← Meta.whnf array)
    let name := (← getCurrNamespace) ++ family
    let type ← Meta.inferType value
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })

generateCommutatorVectors

elab "closeVectorRows " family:ident : tactic => do
  let goals ← getGoals
  unless goals.length == 98 do throwError "Wrong finite vector census"
  for (goal, i) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ family.getId ++ Name.mkSimple s!"row{i}" ++ `exact))
  setGoals []

theorem hRows_exact (i : Basis) : sourceRows hamiltonianNumerator i = hRows i := by
  fin_cases i
  closeVectorRows hRows

theorem gRows_exact (i : Basis) : sourceRows gammaNumerator i = gRows i := by
  fin_cases i
  closeVectorRows gRows

theorem hColumns_exact (i : Basis) : sourceColumns hamiltonianNumerator i = hColumns i := by
  fin_cases i
  closeVectorRows hColumns

theorem gColumns_exact (i : Basis) : sourceColumns gammaNumerator i = gColumns i := by
  fin_cases i
  closeVectorRows gColumns

end LAlanine40K2025.JointNext.NormCalculation.Commutator
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
