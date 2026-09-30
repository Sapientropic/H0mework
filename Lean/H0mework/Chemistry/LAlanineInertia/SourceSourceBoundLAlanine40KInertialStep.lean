import H0mework.Chemistry.LAlanineInertia.SourceInertialStepParsing
import H0mework.Chemistry.LAlaninePropagation.GeneratedNativeClock

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Source

open Lean Elab Term SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String :=
  "cb290011475c3d8bdc0f64949b8522c925f17658fd80055309468599ccaac1c6"

private def sourceText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/source/lalanine40k-inertial-next.json"

private def parentText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/force/source/lalanine40k-force-material-next.json"

private def checkFrameJoin (frame ledger : Json) : TermElabM Unit := do
  let force ← field frame "force"
  unless (← field force "source_nuclei") == (← field ledger "nuclei") do
    throwError "Force/energy nuclear incidence mismatch"
  let forceMethod ← field force "method"
  let energyMethod ← field ledger "method"
  let density ← field frame "density_matrix_sha256"
  unless density == (← field forceMethod "density_matrix_sha256") &&
      density == (← field energyMethod "density_matrix_sha256") do
    throwError "Different densities supplied force and energy"

elab "lalanineInertialStep%" : term => do
  unless Sha256.hex sourceText == sourceArtifactSha256 do throwError "Inertial source changed"
  unless Sha256.hex parentText == Force.Source.sourceArtifactSha256 do throwError "Force parent changed"
  let value ← parse sourceText
  let parent ← parse parentText
  unless (← decode String (← field value "schema")) == "lalanine40k-source-generated-inertial-next/v1" do
    throwError "Unexpected inertial schema"
  let frames ← decode (Array Json) (← field value "frames")
  unless frames.size == 2 do throwError "Expected initialization and exactly one generated frame"
  let current := frames[0]!
  let target := frames[1]!
  unless (← decode Nat (← field current "index")) == 0 &&
      (← decode Nat (← field target "index")) == 1 do throwError "Changed frame address"
  unless !(← decode Bool (← field current "scf_at_new_geometry")) &&
      (← decode Bool (← field target "scf_at_new_geometry")) do throwError "SCF occurrence mismatch"
  let parentTarget ← field parent "target"
  let parentGeometry ← field parentTarget "geometry"
  unless (← field current "geometry") == parentGeometry do throwError "Changed parent geometry"
  let currentLedger ← field parentTarget "energy_ledger"
  let targetLedger ← field value "target_energy_ledger"
  checkFrameJoin current currentLedger
  checkFrameJoin target targetLedger
  let preparation ← field value "preparation"
  let duration ← field preparation "duration"
  unless (← rationalPair (← field current "time")) == (0, 1) &&
      (← field target "time") == duration do throwError "Changed native clock incidence"
  let sourceJoin ← field preparation "source_join"
  unless (← decode String (← field sourceJoin "force_artifact_sha256")) == Force.Source.sourceArtifactSha256 do
    throwError "Clock/force parent mismatch"
  let (currentNuclei, currentPositions) ← nuclearRows (← field currentLedger "nuclei")
  let (targetNuclei, targetPositions) ← nuclearRows (← field targetLedger "nuclei")
  let refinement ← field value "native_refinement"
  let currentForce ← field current "force"
  let targetForce ← field target "force"
  let currentLedgerExpr ← Meta.mkAppM ``Force.Interface.NuclearUpdateReadout.targetEnergyLedger
    #[mkConst ``Force.Source.updateReadout]
  let targetLedgerExpr ← Energy.Source.reifyMolecularEnergyLedger targetLedger
  Meta.mkAppM ``Interface.InertialStepReadout.mk
    #[← masses (← field value "mass_electron_units_dyadic"), ← rationalExpr duration,
      ← frame current, ← frame target,
      ← coordinates (← field refinement "position_residual_bohr"),
      ← coordinates (← field refinement "momentum_residual_au"),
      currentLedgerExpr, targetLedgerExpr, currentNuclei, targetNuclei, currentPositions, targetPositions,
      ← gradientComponents currentForce, ← gradientComponents targetForce,
      ← integerCoordinateExpr (← field currentForce "component_rounding_residual_picohartree_per_bohr"),
      ← integerCoordinateExpr (← field targetForce "component_rounding_residual_picohartree_per_bohr"),
      ← integerCoordinateExpr (← field currentForce "gradient_picohartree_per_bohr"),
      ← integerCoordinateExpr (← field targetForce "gradient_picohartree_per_bohr")]

noncomputable def stepReadout : Interface.InertialStepReadout := lalanineInertialStep%

end LAlanine40K2025.Inertia.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
