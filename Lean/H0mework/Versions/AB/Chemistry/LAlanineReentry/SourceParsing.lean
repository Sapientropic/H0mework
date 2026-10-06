import H0mework.Versions.AB.Chemistry.LAlanineReentry.DynamicsResidualTransport
import H0mework.Versions.AB.Chemistry.LAlanineJointNext.SourceReification

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.SourceParsing

open Lean Elab Term Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String := "0ad604b1b69b3542055a663c8996ecc6f6906b5076fa8aa9ec6aa1074543bfa4"
def sourceRawArchiveSha256 : String := "e2529442350d15b0e35468eff0972000f701a0a58f5efcbe7ec7152d74bf2145"
def parentRawArchiveSha256 : String := "54a3b26c023587727d8caf4c47912ce99d45fd268ffade76b4d7b9123c9d8790"
private def sourceText : String := include_str "../../../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/reentry/source/reentry.json"

private def rationalValue (value : Json) : TermElabM ℚ := return rationalRead (← rationalPair value)

private def nuclearIdentity (value : Json) : TermElabM (Array (Nat × Nat × String)) := do
  let rows ← decode (Array Json) value
  rows.mapM fun row => return (← decode Nat (← field row "atom_index"),
    ← decode Nat (← field row "charge"), ← decode String (← field row "label"))

private def checkFrame (value ledger : Json) : TermElabM Unit := do
  let force ← field value "force"
  unless (← field force "source_nuclei") == (← field ledger "nuclei") do throwError "Reentry force/energy incidence"
  let density ← field value "density_matrix_sha256"
  unless density == (← field (← field force "method") "density_matrix_sha256") &&
      density == (← field (← field ledger "method") "density_matrix_sha256") do throwError "Reentry same-density join"
  unless (← rationalValue (← field value "nuclear_kinetic_hartree")) +
      (← rationalValue (← field value "potential_hartree")) == (← rationalValue (← field value "total_energy_hartree")) do
    throwError "Reentry exact K+U"
  unless (← decode Bool (← field value "scf_at_new_geometry")) == false do throwError "Reentry SCF reset"

def verifiedPacket : TermElabM Json := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do throwError "Reentry source changed"
  let value ← parse sourceText
  let parent ← JointNext.SourceParsing.verifiedPacket
  let join ← field value "source_join"
  unless (← decode String (← field value "schema")) == "lalanine40k-source-generated-joint-reentry/v1" &&
      (← decode String (← field join "parent_packet_sha256")) == JointNext.SourceParsing.sourceArtifactSha256 &&
      (← decode String (← field join "parent_raw_archive_sha256")) == parentRawArchiveSha256 do throwError "Reentry parent source"
  unless (← field join "parent_source_join") == (← field parent "source_join") do throwError "Reentry parent history"
  unless (← decode String (← field join "parent_runtime_current")) == "LAlanine40K2025.JointNext.Runtime.jointRuntimeAfterFirst" &&
      (← decode String (← field join "whole_ledger_row")) == "bondDensityIncidenceAdjudication" &&
      (← decode String (← field join "claim")) == "registeredExperimentalGeometryModelBondTopology" do throwError "Reentry root row"
  let nuclear ← field value "nuclear"
  let parentNuclear ← field parent "nuclear"
  let frames ← decode (Array Json) (← field nuclear "frames")
  let parentFrames ← decode (Array Json) (← field parentNuclear "frames")
  unless frames.size == 2 && parentFrames.size == 2 do throwError "Reentry frame census"
  let current := frames[0]!
  let target := frames[1]!
  let previous := parentFrames[1]!
  for key in ["time", "positions_bohr", "momenta_au", "nuclear_kinetic_hartree", "potential_hartree",
      "total_energy_hartree", "geometry", "gradient_au", "force", "density_matrix_sha256"] do
    unless (← field current key) == (← field previous key) do throwError "Reentry current changed: {key}"
  unless (← field nuclear "current_energy_ledger") == (← field parentNuclear "target_energy_ledger") &&
      (← field nuclear "mass_electron_units_dyadic") == (← field parentNuclear "mass_electron_units_dyadic") do
    throwError "Reentry current ledger/masses"
  let currentLedger ← field nuclear "current_energy_ledger"
  let targetLedger ← field nuclear "target_energy_ledger"
  unless (← field join "nuclear_inventory") == (← field currentLedger "nuclei") do throwError "Reentry current M2 incidence"
  unless (← nuclearIdentity (← field targetLedger "nuclei")) == (← nuclearIdentity (← field currentLedger "nuclei")) do
    throwError "Reentry nuclear identity changed"
  unless (← field join "atomic_orbital_addresses") == (← field (← field parent "source_join") "atomic_orbital_addresses") do
    throwError "Reentry AO incidence"
  let q ← rationalValue (← field nuclear "duration")
  unless q == (← rationalValue (← field parentNuclear "duration")) && q > 0 &&
      (← rationalValue (← field current "time")) == 2*q && (← rationalValue (← field target "time")) == 3*q do
    throwError "Reentry 2q-to-3q clock"
  checkFrame current currentLedger
  checkFrame target targetLedger
  let parentResiduals ← field nuclear "parent_nuclear_residuals"
  for key in ["native_refinement", "engine_binding", "energy_account"] do
    unless (← field parentResiduals key) == (← field parentNuclear key) do throwError "Reentry discarded parent residual: {key}"
  let electronic ← field value "electronic"
  let parentElectronic ← field parent "electronic"
  for (currentKey, priorKey) in [("source_gamma_real_rows", "target_gamma_real_rows"), ("source_gamma_imag_rows", "target_gamma_imag_rows")] do
    unless (← field electronic currentKey) == (← field parentElectronic priorKey) do throwError "Reentry complex source channel: {currentKey}"
  for (key, expected) in [("hamiltonian_scale", 1000000000000), ("cross_scale", 1000000000000000),
      ("source_gamma_scale", 1000000000000000), ("target_gamma_scale", 1000000000000000)] do
    unless (← decode Nat (← field electronic key)) == expected do throwError "Reentry scale: {key}"
  let clocks ← field electronic "same_elapsed_time"
  for key in ["electronic", "nuclear", "physical"] do
    unless (← rationalValue (← field clocks key)) == q do throwError "Reentry substage clock"
  unless (← rationalValue (← field clocks "frame_reexpression_extra")) == 0 do throwError "Reentry extra frame clock"
  let lineage ← field electronic "error_lineage"
  unless (← decode String (← field lineage "parent_packet_sha256")) == JointNext.SourceParsing.sourceArtifactSha256 &&
      (← decode String (← field lineage "parent_raw_archive_sha256")) == parentRawArchiveSha256 do throwError "Reentry error provenance"
  let runtime ← field value "runtime"
  for key in ["seed_replayed", "new_current_scf_performed", "target_scf_performed"] do
    unless (← decode Bool (← field runtime key)) == false do throwError "Reentry replay/reset: {key}"
  unless (← decode Bool (← field electronic "new_scf_performed")) == false do throwError "Reentry electronic reset"
  pure value

end LAlanine40K2025.Reentry.SourceParsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
