import H0mework.Chemistry.LAlanineReentry.SourceSourceBoundReentry
import H0mework.Chemistry.LAlanineJointNext.ProducerCalculationNormCalculationSharing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.NormCalculation

open Lean Elab Term Command Propagation.Interface
open JointNext.NormCalculation (listEntries)

private def declareShared (name : Name) (value : Expr) : TermElabM Unit := do
  let type ← Meta.inferType value
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

elab "shareReentrySourceRows" : command => liftTermElabM do
  for (source, suffix) in [(``Source.hamiltonianNumerator, `hamiltonianNumerator),
      (``Source.crossNumerator, `crossNumerator), (``Source.targetRealNumerator, `targetRealNumerator),
      (``Source.targetImagNumerator, `targetImagNumerator)] do
    let original := (← getConstInfo source).value!
    let array ← Meta.whnf original.appArg!
    unless array.isAppOfArity ``Array.mk 2 do throwError "Nonliteral source array"
    let some rows := listEntries (array.getArg! 1) | throwError "Nonliteral source rows"
    unless rows.size == 98 do throwError "Source row census changed"
    let name := (← getCurrNamespace) ++ suffix
    let mut references := #[]
    for i in [:98] do
      let rowName := name ++ Name.mkSimple s!"row{i}"
      declareShared rowName (← Meta.whnf rows[i]!)
      references := references.push (Lean.mkConst rowName)
    let sharedRows ← Meta.mkArrayLit (← Meta.inferType rows[0]!) references.toList
    declareShared name (mkApp original.appFn! (← Meta.whnf sharedRows))
    let type ← Meta.mkEq (Lean.mkConst source) (Lean.mkConst name)
    let value ← Meta.mkEqRefl (Lean.mkConst source)
    let name := (← getCurrNamespace) ++ Name.mkSimple s!"{suffix}_eq"
    addDecl (.thmDecl { name, levelParams := [], type, value })

set_option maxRecDepth 2048 in
shareReentrySourceRows

noncomputable def currentRealNumerator : Matrix Basis Basis Int := JointNext.NormCalculation.targetRealNumerator
noncomputable def currentImagNumerator : Matrix Basis Basis Int := JointNext.NormCalculation.targetImagNumerator

theorem currentRealNumerator_eq : Source.currentRealNumerator = currentRealNumerator :=
  JointNext.NormCalculation.targetRealNumerator_eq

theorem currentImagNumerator_eq : Source.currentImagNumerator = currentImagNumerator :=
  JointNext.NormCalculation.targetImagNumerator_eq

theorem hamiltonian_swap (i j : Basis) : hamiltonianNumerator i j = hamiltonianNumerator j i := by
  change JointNext.SourceReification.symmetricRead _ i j = JointNext.SourceReification.symmetricRead _ j i
  exact JointNext.SourceReification.symmetricRead_swap _ i j

theorem currentReal_swap (i j : Basis) : currentRealNumerator i j = currentRealNumerator j i := by
  change JointNext.SourceReification.symmetricRead _ i j = JointNext.SourceReification.symmetricRead _ j i
  exact JointNext.SourceReification.symmetricRead_swap _ i j

theorem currentImag_swap (i j : Basis) : currentImagNumerator i j = -currentImagNumerator j i := by
  change JointNext.SourceReification.antisymmetricRead _ i j = -JointNext.SourceReification.antisymmetricRead _ j i
  exact JointNext.SourceReification.antisymmetricRead_swap _ i j

end LAlanine40K2025.Reentry.NormCalculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
