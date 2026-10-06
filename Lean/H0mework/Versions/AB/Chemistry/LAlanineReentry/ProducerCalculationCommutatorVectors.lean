import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerCalculationNormCalculationSharing
import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerCalculationCommutatorRowsVectors

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.NormCalculation.Commutator

open Lean Elab Term Command Propagation.Interface
open JointNext.NormCalculation (matrixValues)
open JointNext.NormCalculation.Commutator (sourceRows readVectors)

elab "generateReentryCommutatorVectors" : command => liftTermElabM do
  for (family, source, stored) in [(`hRows, ``hamiltonianNumerator, ``hamiltonianNumerator),
      (`rRows, ``currentRealNumerator, ``JointNext.NormCalculation.targetRealNumerator),
      (`iRows, ``currentImagNumerator, ``JointNext.NormCalculation.targetImagNumerator)] do
    let values ← matrixValues stored
    let mut references := #[]
    for i in [:98] do
      let name := (← getCurrNamespace) ++ family ++ Name.mkSimple s!"row{i}"
      let value := toExpr values[i]!.toList
      let type ← Meta.inferType value
      addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
      let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 98))
      let index := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 98) (mkNatLit i) inside
      let left := mkApp2 (Lean.mkConst ``sourceRows) (Lean.mkConst source) index
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

generateReentryCommutatorVectors

theorem hRows_exact (i : Basis) : sourceRows hamiltonianNumerator i = hRows i := by
  fin_cases i
  closeVectorRows hRows

theorem rRows_exact (i : Basis) : sourceRows currentRealNumerator i = rRows i := by
  fin_cases i
  closeVectorRows rRows

theorem iRows_exact (i : Basis) : sourceRows currentImagNumerator i = iRows i := by
  fin_cases i
  closeVectorRows iRows

end LAlanine40K2025.Reentry.NormCalculation.Commutator
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
