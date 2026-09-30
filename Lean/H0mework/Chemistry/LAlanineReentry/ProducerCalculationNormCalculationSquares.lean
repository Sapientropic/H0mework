import H0mework.Chemistry.LAlanineReentry.ProducerCalculationNormCalculationSharing
import H0mework.Chemistry.LAlanineJointNext.ProducerCalculationNormCalculationSquares

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.NormCalculation.Squares

open Lean Elab Term Command Propagation.Interface
open JointNext.NormCalculation (matrixValues)
noncomputable section

def delta (i j : Basis) : Int := crossNumerator i j - if i = j then 1000000000000000 else 0
def crossRow (i : Basis) : Int := ∑ j : Basis, delta i j ^ 2
def symmetricRow (i : Basis) : Int := ∑ j : Basis, (delta i j + delta j i) ^ 2
def targetRow (i : Basis) : Int := ∑ j : Basis,
  ((targetRealNumerator i j - currentRealNumerator i j) ^ 2 +
    (targetImagNumerator i j - currentImagNumerator i j) ^ 2)

elab "calculateReentrySquaredRows" : command => liftTermElabM do
  let cross ← matrixValues ``crossNumerator
  let targetReal ← matrixValues ``targetRealNumerator
  let targetImag ← matrixValues ``targetImagNumerator
  let currentReal ← matrixValues ``JointNext.NormCalculation.targetRealNumerator
  let currentImag ← matrixValues ``JointNext.NormCalculation.targetImagNumerator
  let d (i j : Nat) := (cross[i]!)[j]! - if i == j then 1000000000000000 else 0
  for (family, fn, calculate) in [(`cross, ``crossRow, fun i j => d i j ^ 2),
      (`symmetric, ``symmetricRow, fun i j => (d i j + d j i) ^ 2),
      (`target, ``targetRow, fun i j =>
        ((targetReal[i]!)[j]! - (currentReal[i]!)[j]!) ^ 2 +
          ((targetImag[i]!)[j]! - (currentImag[i]!)[j]!) ^ 2)] do
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
    let value := mkApp (Lean.mkConst ``JointNext.NormCalculation.Squares.readVector) (← Meta.whnf (toExpr values))
    let type ← Meta.inferType value
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
    modifyEnv (addNoncomputable · name)

calculateReentrySquaredRows

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
end LAlanine40K2025.Reentry.NormCalculation.Squares
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
