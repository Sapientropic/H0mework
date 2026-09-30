import H0mework.Chemistry.LAlanineHeldForce.SourceHeldForceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Source

open Lean Elab Term Command
open Propagation.Interface Inertia.SourceParsing SourceParsing

private def declareReadout (suffix : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl {
    name
    levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

/-- Verify the whole source once; each independent readout remains a separate kernel-checked definition. -/
elab "generateHeldForceReadouts" : command => liftTermElabM do
  let value ← verifiedPacket
  let response ← field value "response"
  let force ← field response "force"
  let raw ← field value "raw_readouts"
  declareReadout `gammaNumerator (← gammaExpr value)
  declareReadout `energyLedger (← Energy.Source.reifyMolecularEnergyLedger (← field response "energy_ledger"))
  declareReadout `gradientComponentsReadout (← gradientComponents force)
  for (name, key) in [(`gradientPicohartree, "gradient_picohartree_per_bohr"),
      (`forcePicohartree, "force_picohartree_per_bohr"),
      (`gradientResidual, "component_rounding_residual_picohartree_per_bohr")] do
    declareReadout name (← integerCoordinateExpr (← field force key))
  declareReadout `stationaryCorrection (← integerCoordinateExpr
    (← field (← field response "stationary_formula_correction") "picohartree_per_bohr"))
  declareReadout `rawGradient (← coordinates (← field raw "gradient_au"))
  declareReadout `rawEnergy (← rationalExpr (← field raw "energy_hartree"))

set_option maxRecDepth 2048 in
generateHeldForceReadouts

noncomputable def realizedHeld : Matrix Basis Basis ℂ := fun i j => (gammaNumerator i j : ℂ) / 1000000000000

end LAlanine40K2025.HeldForce.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
