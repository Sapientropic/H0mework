import H0mework.Chemistry.LAlanineReentry.SourceReification

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Source

open Lean Elab Term Command Propagation.Interface Inertia.SourceParsing

private def declareReadout (suffix : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

elab "generateReentryReadouts" : command => liftTermElabM do
  let value ← SourceParsing.verifiedPacket
  let electronic ← field value "electronic"
  let nuclear ← field value "nuclear"
  declareReadout `nuclearReadout (← SourceReification.nuclearExpr nuclear)
  for (name, key, symmetry) in [(`hamiltonianNumerator, "hamiltonian_rows", (1 : Int)),
      (`crossNumerator, "cross_rows", 0), (`targetRealNumerator, "target_gamma_real_rows", 1),
      (`targetImagNumerator, "target_gamma_imag_rows", -1)] do
    declareReadout name (← JointNext.SourceReification.matrixExpr electronic key symmetry)
  let energy ← field nuclear "energy_account"
  for (name, key) in [(`recordedEnergyChange, "total_change_hartree"),
      (`engineEnergyChange, "raw_engine_exact_operand_change_hartree"),
      (`engineAccountingResidual, "engine_vs_recorded_change_residual_hartree")] do
    declareReadout name (← rationalExpr (← field energy key))

set_option maxRecDepth 2048 in
generateReentryReadouts

noncomputable def currentRealNumerator : Matrix Basis Basis Int := JointNext.Source.targetRealNumerator
noncomputable def currentImagNumerator : Matrix Basis Basis Int := JointNext.Source.targetImagNumerator
noncomputable def currentRealized : Matrix Basis Basis ℂ := Runtime.reentryParentRealization.1

noncomputable def stepReadout : JointNext.Interface.JointStepReadout where
  nuclear := nuclearReadout
  frozenHamiltonianNumerator := hamiltonianNumerator
  crossNumerator := crossNumerator
  targetDensityRealNumerator := targetRealNumerator
  targetDensityImagNumerator := targetImagNumerator

noncomputable def hamiltonian : Matrix Basis Basis ℂ := stepReadout.frozenHamiltonian
noncomputable def crossMatrix : Matrix Basis Basis ℂ := stepReadout.crossMatrix
noncomputable def targetRealized : Matrix Basis Basis ℂ := stepReadout.targetRealized

theorem currentFrame_eq_parent : stepReadout.nuclear.current = Runtime.reentryParentFrame := rfl
theorem currentLedger_eq_parent : stepReadout.nuclear.currentLedger = Runtime.reentryParentLedger := rfl
theorem masses_eq_parent : stepReadout.nuclear.masses = Runtime.reentryParentMasses := rfl
theorem duration_eq_original : stepReadout.nuclear.duration = Continuation.duration := rfl
theorem currentRealized_eq_parent : currentRealized = JointNext.Source.targetRealized := rfl
theorem currentRealized_channels (i j : Basis) : currentRealized i j =
    ((currentRealNumerator i j : ℂ) + Complex.I * (currentImagNumerator i j : ℂ)) / 1000000000000000 := rfl

end LAlanine40K2025.Reentry.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
