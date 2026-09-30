import H0mework.Chemistry.LAlanineJointNext.ProducerCalculationNormCalculationSharing

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.NormCalculation.Squares

open Lean Elab Term Command Tactic
open Propagation.Interface
noncomputable section

def delta (i j : Basis) : Int := crossNumerator i j - if i = j then 1000000000000000 else 0
def crossRow (i : Basis) : Int := ∑ j : Basis, delta i j ^ 2
def symmetricRow (i : Basis) : Int := ∑ j : Basis, (delta i j + delta j i) ^ 2
def targetRow (i : Basis) : Int := ∑ j : Basis,
  ((targetRealNumerator i j - 1000 * gammaNumerator i j) ^ 2 + targetImagNumerator i j ^ 2)
def readVector (values : Array Int) (i : Basis) : Int := values[i.val]!

elab "generateJointSquaredRows" : command => liftTermElabM do
  let cross ← matrixValues ``crossNumerator
  let realPart ← matrixValues ``targetRealNumerator
  let imaginary ← matrixValues ``targetImagNumerator
  let gamma ← matrixValues ``gammaNumerator
  let delta (i j : Nat) := (cross[i]!)[j]! - if i == j then 1000000000000000 else 0
  for (family, fn, calculate) in [(`cross, ``crossRow, fun i j => (delta i j) ^ 2),
      (`symmetric, ``symmetricRow, fun i j => (delta i j + delta j i) ^ 2),
      (`target, ``targetRow, fun i j =>
        ((realPart[i]!)[j]! - 1000 * (gamma[i]!)[j]!) ^ 2 + (imaginary[i]!)[j]! ^ 2)] do
    let mut values : Array Int := #[]
    for i in [:98] do
      let total := (List.range 98).foldl (fun a j => a + calculate i j) 0
      values := values.push total
      let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 98))
      let index := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 98) (mkNatLit i) inside
      let type ← Meta.mkEq (mkApp (Lean.mkConst fn) index) (toExpr total)
      let value ← instantiateMVars (← Meta.mkDecideProof type)
      let type ← instantiateMVars type
      let name := (← getCurrNamespace) ++ family ++ Name.mkSimple s!"row{i}"
      addDecl (.thmDecl { name, levelParams := [], type, value })
    let name := (← getCurrNamespace) ++ Name.mkSimple s!"{family}Values"
    let array ← Meta.whnf (toExpr values)
    let value := mkApp (Lean.mkConst ``readVector) array
    let type ← Meta.inferType value
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
    modifyEnv (addNoncomputable · name)

generateJointSquaredRows

elab "closeCalculatedRows " family:ident : tactic => do
  let goals ← getGoals
  unless goals.length == 98 do throwError "Wrong finite row census"
  for (goal, i) in goals.zipIdx do
    goal.assign (Lean.mkConst ((← getCurrNamespace) ++ family.getId ++ Name.mkSimple s!"row{i}"))
  setGoals []

theorem crossRows_exact (i : Basis) : crossRow i = crossValues i := by
  fin_cases i
  closeCalculatedRows cross

theorem symmetricRows_exact (i : Basis) : symmetricRow i = symmetricValues i := by
  fin_cases i
  closeCalculatedRows symmetric

theorem targetRows_exact (i : Basis) : targetRow i = targetValues i := by
  fin_cases i
  closeCalculatedRows target

end
end LAlanine40K2025.JointNext.NormCalculation.Squares
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
