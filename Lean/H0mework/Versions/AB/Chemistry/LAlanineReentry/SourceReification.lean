import H0mework.Versions.AB.Chemistry.LAlanineReentry.SourceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.SourceReification

open Lean Elab Term Inertia.SourceParsing

def nuclearExpr (nuclear : Json) : TermElabM Expr := do
  let frames ← decode (Array Json) (← field nuclear "frames")
  let current := frames[0]!
  let target := frames[1]!
  let currentLedger ← field nuclear "current_energy_ledger"
  let targetLedger ← field nuclear "target_energy_ledger"
  let (currentNuclei, currentPositions) ← nuclearRows (← field currentLedger "nuclei")
  let (targetNuclei, targetPositions) ← nuclearRows (← field targetLedger "nuclei")
  let currentForce ← field current "force"
  let targetForce ← field target "force"
  let refinement ← field nuclear "native_refinement"
  Meta.mkAppM ``Inertia.Interface.InertialStepReadout.mk
    #[mkConst ``Runtime.reentryParentMasses, mkConst ``Continuation.duration,
      mkConst ``Runtime.reentryParentFrame, ← frame target,
      ← coordinates (← field refinement "position_residual_bohr"),
      ← coordinates (← field refinement "momentum_residual_au"),
      mkConst ``Runtime.reentryParentLedger, ← Energy.Source.reifyMolecularEnergyLedger targetLedger,
      currentNuclei, targetNuclei, currentPositions, targetPositions,
      ← gradientComponents currentForce, ← gradientComponents targetForce,
      ← integerCoordinateExpr (← field currentForce "component_rounding_residual_picohartree_per_bohr"),
      ← integerCoordinateExpr (← field targetForce "component_rounding_residual_picohartree_per_bohr"),
      ← integerCoordinateExpr (← field currentForce "gradient_picohartree_per_bohr"),
      ← integerCoordinateExpr (← field targetForce "gradient_picohartree_per_bohr")]

end LAlanine40K2025.Reentry.SourceReification
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
