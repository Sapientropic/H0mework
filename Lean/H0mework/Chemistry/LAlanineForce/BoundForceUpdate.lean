import Lean.Elab.Term
import Lean.Meta.AppBuilder
import Lean.ToExpr
import Lean.Data.Json
import H0mework.Cognition.Empirical.Sha256
import H0mework.Chemistry.LAlanineForce.NativeNuclearUpdate
import H0mework.Chemistry.LAlanineEnergy.BoundEnergyLedger

/-! # Bound source-generated force and material next -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Force.Source

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Force.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String :=
  "4949a7f925127e4303d8df70b3520828aebee3ad5483131f95c98415cdd42a70"

private def sourceText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/force/source/lalanine40k-force-material-next.json"

private def predecessorText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/energy/source/lalanine40k-same-computation-energy.json"

private def field (value : Lean.Json) (key : String) : Lean.Elab.TermElabM Lean.Json :=
  match value.getObjVal? key with
  | .ok value => pure value
  | .error error => throwError "Force source field {key}: {error}"

private def decode (α : Type) [Lean.FromJson α] (value : Lean.Json) : Lean.Elab.TermElabM α :=
  match Lean.fromJson? value with
  | .ok value => pure value
  | .error error => throwError "Force source decoder: {error}"

private def parse (text : String) : Lean.Elab.TermElabM Lean.Json :=
  match Lean.Json.parse text with
  | .ok value => pure value
  | .error error => throwError "Force source JSON: {error}"

private def coordinates (value : Lean.Json) : Lean.Elab.TermElabM (Array (Array Int)) := do
  let rows ← decode (Array (Array Int)) value
  unless rows.size == 13 && rows.all (fun row => row.size == 3) do
    throwError "Nuclear coordinate incidence is not 13 × 3"
  pure rows

def coordinateRead (rows : Array (Array Int)) : NuclearCoordinates :=
  fun atom axis => rows[atom.val]![axis.val]!

private def coordinateExpr (rows : Array (Array Int)) : Lean.Elab.TermElabM Lean.Expr :=
  Lean.Meta.mkAppM ``coordinateRead #[Lean.toExpr rows]

private def nuclei (rows : Array Lean.Json) : Lean.Elab.TermElabM (Array (String × Nat)) := do
  unless rows.size == 13 do throwError "Source nuclear inventory changed"
  let mut result := #[]
  for index in [:rows.size] do
    let row := rows[index]!
    let address ← decode Nat (← field row "atom_index")
    unless address == index do throwError "Source nuclear address changed"
    let label ← decode String (← field row "label")
    let charge ← decode Nat (← field row "charge")
    result := result.push (label, charge)
  pure result

private def graphFromCensus (census : Lean.Json) : Lean.Elab.TermElabM (Array (List String × Nat)) := do
  let raw ← decode (Array Lean.Json) (← field census "pair_rows")
  unless raw.size == 15 do throwError "Registered heavy-pair graph changed"
  let mut result := #[]
  for row in raw do
    let labels ← decode (List String) (← field row "address")
    unless labels.length == 2 do throwError "Graph edge address changed"
    let count ← decode Nat (← field row "bcp_count")
    result := result.push (labels, count)
  pure result

elab "lalanineForceUpdate%" : term => do
  unless Sha256.hex sourceText == sourceArtifactSha256 do
    throwError "Force source artifact SHA-256 changed"
  unless Sha256.hex predecessorText == LAlanine40K2025.Energy.Source.sourceArtifactSha256 do
    throwError "Prior energy source artifact changed"
  let value ← parse sourceText
  let currentJoint ← field value "current_joint"
  unless currentJoint == (← parse predecessorText) do
    throwError "Force and original energy are not the same current"
  let force ← field value "force"
  let step ← field value "generated_step"
  let sourcePositions ← coordinates (← field step "source_positions_picobohr")
  let gradient ← coordinates (← field force "gradient_picohartree_per_bohr")
  unless gradient == (← coordinates (← field step "gradient_picohartree_per_bohr")) do
    throwError "Step used a different gradient"
  let residual ← coordinates (← field force "component_rounding_residual_picohartree_per_bohr")
  let components ← field force "gradient_components_picohartree_per_bohr"
  let mut componentRows : Array (Array (Array Int)) := #[]
  for name in ["one_electron", "coulomb", "xc_basis", "pulay", "xc_grid_response", "nuclear_repulsion"] do
    componentRows := componentRows.push (← coordinates (← field components name))
  let targetPositions ← coordinates (← field step "target_positions_picobohr")
  let sourceAtoms ← decode (Array Lean.Json) (← field force "source_nuclei")
  for index in [:13] do
    let row ← decode (Array Int) (← field sourceAtoms[index]! "position_picobohr")
    unless row == sourcePositions[index]! do
      throwError "Step used a different source position"
  let sourceNuclei ← nuclei sourceAtoms
  let target ← field value "target"
  let targetLedger ← field target "energy_ledger"
  let targetAtoms ← decode (Array Lean.Json) (← field targetLedger "nuclei")
  let targetNuclei ← nuclei targetAtoms
  for index in [:13] do
    let row ← decode (Array Int) (← field targetAtoms[index]! "position_picobohr")
    unless row == targetPositions[index]! do
      throwError "Target energy used a different nuclear position"
  let currentDensity ← field currentJoint "density_projection"
  let currentCensus ← field currentDensity "calculation"
  let currentMethod ← field currentCensus "method"
  let currentEnergy ← decode Int (← field currentMethod "scf_energy_nanohartree")
  let targetCensus ← field target "density_census"
  let targetMethod ← field targetCensus "method"
  let targetEnergy ← decode Int (← field targetMethod "scf_energy_nanohartree")
  let closure ← field targetLedger "closure"
  let recordedTargetEnergy ← decode Int (← field closure "reported_scf_nanohartree")
  unless targetEnergy == recordedTargetEnergy do
    throwError "Target energy consumer belongs to another SCF"
  let currentGraph ← graphFromCensus currentCensus
  let targetGraph ← graphFromCensus targetCensus
  let targetLedgerExpression ← LAlanine40K2025.Energy.Source.reifyMolecularEnergyLedger targetLedger
  Lean.Meta.mkAppM ``NuclearUpdateReadout.mk
    #[← coordinateExpr sourcePositions, ← coordinateExpr gradient,
      Lean.toExpr componentRows, ← coordinateExpr residual,
      ← coordinateExpr targetPositions, Lean.toExpr currentEnergy, Lean.toExpr targetEnergy,
      Lean.toExpr currentGraph, Lean.toExpr targetGraph,
      Lean.toExpr sourceNuclei, Lean.toExpr targetNuclei, targetLedgerExpression]

noncomputable def updateReadout : NuclearUpdateReadout := lalanineForceUpdate%

end LAlanine40K2025.Force.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
