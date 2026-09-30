import H0mework.Chemistry.LAlanineChargeIdentity.SourceReification

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.SourceParsing

open Lean Elab Term Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String := "38f7bd7d0a795570179b7fe78171a2a1410a46c1a21d6358f9d0b12bf184a6eb"
def sourceText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/charge_identity/source/charge-identity.json"

def verifiedPacket : TermElabM Json := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do throwError "Charge source changed"
  let value ← parse sourceText
  let parent ← BondReadout.SourceParsing.verifiedPacket
  let join ← field value "source_join"
  let parentJoin ← field parent "source_join"
  unless (← decode String (← field value "schema")) == "lalanine40k-source-generated-charge-identity/v1" &&
      (← decode String (← field join "bond_packet_sha256")) == BondReadout.SourceParsing.sourceArtifactSha256 &&
      (← decode String (← field join "reentry_packet_sha256")) == Reentry.SourceParsing.sourceArtifactSha256 &&
      (← decode String (← field join "reentry_raw_archive_sha256")) == Reentry.SourceParsing.sourceRawArchiveSha256 do
    throwError "Charge parent source"
  unless (← decode String (← field join "parent_runtime_current")) == "LAlanine40K2025.BondReadout.Runtime.bondRuntimeAfterFirst" do
    throwError "Charge wrong root current"
  for key in ["whole_ledger_row", "claim", "time", "geometry_sha256", "energy_ledger_sha256",
      "density_matrix_sha256", "atomic_orbital_addresses"] do
    unless (← field join key) == (← field parentJoin key) do throwError "Charge same-occurrence join: {key}"
  unless (← field join "full_state_references") == (← field parentJoin "array_references") &&
      (← decode Nat (← field join "V_column")) == 6 &&
      (← decode (Array String) (← field join "V_source_path")) == #["nuclear", "target_energy_ledger", "ao_pair_rows"] do
    throwError "Charge original total-field read"
  let protocol ← field value "protocol"
  for (key, expected) in [("unit_column_scale", 1000000000000000), ("total_field_scale", 1000000000000),
      ("field_row_count", 4851), ("block_rows", 128)] do
    unless (← decode Nat (← field protocol key)) == expected do throwError "Charge source-fixed convention: {key}"
  unless rationalRead (← rationalPair (← field protocol "absolute_channel_epsilon_hartree")) == 1 / 1000000000 &&
      (← decode Bool (← field protocol "epsilon_is_source_fixed_before_total_field_read")) == true do
    throwError "Charge changed compatibility convention"
  let recovery ← field value "recovery"
  let selection ← field recovery "selection"
  let selected ← decode (Array Nat) (← field selection "pivot_rows")
  let addresses ← decode (Array (Array Nat)) (← field selection "pivot_AO_addresses")
  let mut original : Array (Array Nat) := #[]
  for i in [:98] do
    for j in [i:98] do original := original.push #[i, j]
  unless addresses == selected.map (fun i => original[i]!) do throwError "Charge pivot AO incidence"
  let runtime ← field value "runtime"
  for key in ["molecular_scf_performed", "md_step_performed", "energy_recalculated"] do
    unless (← decode Bool (← field runtime key)) == false do throwError "Charge source replay: {key}"
  unless (← decode Bool (← field runtime "physical_time_unchanged")) == true &&
      rationalRead (← rationalPair (← field runtime "physical_elapsed_time")) == 0 do throwError "Charge extra physical step"
  pure value

end LAlanine40K2025.ChargeIdentity.SourceParsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
