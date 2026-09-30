import H0mework.Chemistry.LAlanineJointNext.InterfaceJointStep
import H0mework.Chemistry.LAlanineHeldForce.SourceHeldForceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.SourceParsing

open Lean Elab Term
open Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String := "34e31dd42fe56752526a26f9d9e219305f98c5d0cc4320d96c467b4b9f4645e1"
private def sourceText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/joint_step/source/joint-step.json"
private def inertiaText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/source/lalanine40k-inertial-next.json"

private def rationalEqual (left right : Json) : TermElabM Bool := do
  let (ln, ld) ← rationalPair left
  let (rn, rd) ← rationalPair right
  pure (ln * (rd : Int) == rn * (ld : Int))

private def checkFrame (value ledger : Json) : TermElabM Unit := do
  let force ← field value "force"
  unless (← field force "source_nuclei") == (← field ledger "nuclei") do throwError "Joint nuclear incidence differs"
  let density ← field value "density_matrix_sha256"
  unless density == (← field (← field force "method") "density_matrix_sha256") &&
      density == (← field (← field ledger "method") "density_matrix_sha256") do throwError "Joint energy/force density differs"
  let kinetic ← rationalPair (← field value "nuclear_kinetic_hartree")
  let potential ← rationalPair (← field value "potential_hartree")
  let total ← rationalPair (← field value "total_energy_hartree")
  unless rationalRead kinetic + rationalRead potential == rationalRead total do throwError "Joint exact K+U differs"
  unless (← decode Bool (← field value "scf_at_new_geometry")) == false do throwError "SCF reset in joint event"

def verifiedPacket : TermElabM Json := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do throwError "Joint source changed"
  unless Sha256.hex inertiaText == Inertia.Source.sourceArtifactSha256 do throwError "Inertial history changed"
  let value ← parse sourceText
  let held ← HeldForce.SourceParsing.verifiedPacket
  let original ← parse inertiaText
  let priorFrames ← decode (Array Json) (← field original "frames")
  let join ← field value "source_join"
  let heldJoin ← field held "source_join"
  unless (← decode String (← field value "schema")) == "lalanine40k-source-generated-joint-next/v1" &&
      (← decode String (← field join "held_force_artifact_sha256")) == HeldForce.SourceParsing.sourceArtifactSha256 do
    throwError "Wrong joint root occurrence"
  for key in ["electronic_frame_sha256", "inertial_artifact_sha256", "original_electronic_artifact_sha256",
      "current_geometry_sha256", "nuclear_inventory", "atomic_orbital_addresses"] do
    unless (← field join key) == (← field heldJoin key) do throwError "Joint source join changed: {key}"
  let nuclear ← field value "nuclear"
  let frames ← decode (Array Json) (← field nuclear "frames")
  unless frames.size == 2 && priorFrames.size == 2 do throwError "Joint frame census changed"
  let first := frames[0]!
  let target := frames[1]!
  for key in ["positions_bohr", "momenta_au", "nuclear_kinetic_hartree", "geometry"] do
    unless (← field first key) == (← field priorFrames[1]! key) do throwError "Joint initial material changed: {key}"
  let rawHeld ← field held "raw_readouts"
  unless (← field first "gradient_au") == (← field rawHeld "gradient_au") &&
      (← field first "potential_hartree") == (← field rawHeld "energy_hartree") do throwError "Joint initial response changed"
  let heldResponse ← field held "response"
  unless (← field first "force") == (← field heldResponse "force") &&
      (← field nuclear "current_energy_ledger") == (← field heldResponse "energy_ledger") do throwError "Joint inherited ledger changed"
  unless (← field nuclear "mass_electron_units_dyadic") == (← field original "mass_electron_units_dyadic") do
    throwError "Joint mass changed"
  let duration ← field nuclear "duration"
  unless (← rationalEqual duration (← field held "physical_time")) &&
      (← rationalEqual (← field first "time") duration) do throwError "Joint original q changed"
  let (qn, qd) ← rationalPair duration
  let (tn, td) ← rationalPair (← field target "time")
  unless tn * (qd : Int) == 2 * qn * (td : Int) do throwError "Joint target clock is not 2q"
  checkFrame first (← field nuclear "current_energy_ledger")
  checkFrame target (← field nuclear "target_energy_ledger")
  let electronic ← field value "electronic"
  let clocks ← field electronic "same_elapsed_time"
  for key in ["electronic", "nuclear", "physical"] do
    unless (← rationalEqual (← field clocks key) duration) do throwError "Joint substage clock differs"
  unless (← rationalPair (← field clocks "frame_reexpression_extra")).1 == 0 do throwError "Extra frame time"
  unless (← field electronic "source_gamma_rows") == (← field (← field held "held_realization") "gamma_rows") do
    throwError "Joint source matrix changed"
  for (key, expected) in [("hamiltonian_scale", 1000000000000), ("cross_scale", 1000000000000000),
      ("source_gamma_scale", 1000000000000), ("target_gamma_scale", 1000000000000000)] do
    unless (← decode Nat (← field electronic key)) == expected do throwError "Joint scale changed: {key}"
  unless (← decode Bool (← field electronic "new_scf_performed")) == false do throwError "New joint SCF"
  pure value

def matrixRows (value : Json) (key : String) : TermElabM (Array (Array Int)) := do
  let rows ← decode (Array (Array Int)) (← field value key)
  unless rows.size == 98 && rows.all (fun row => row.size == 98) do throwError "Joint matrix census changed: {key}"
  pure rows

end LAlanine40K2025.JointNext.SourceParsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
