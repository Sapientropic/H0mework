import H0mework.Versions.AB.Chemistry.LAlanineBasinPartition.SourceReification

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.SourceChecks

open Lean Elab Term Inertia.SourceParsing

def verify (value parent ledger : Json) : TermElabM Unit := do
  let join ← field value "source_join"
  let parentJoin ← field parent "source_join"
  unless (← decode String (← field value "schema")) == "lalanine40k-source-generated-density-basin-partition/v1" &&
      (← decode String (← field join "charge_packet_sha256")) == ChargeIdentity.SourceParsing.sourceArtifactSha256 &&
      (← field join "parent_source_join") == parentJoin do throwError "Basin identity parent"
  unless (← decode String (← field join "parent_runtime_current")) == "LAlanine40K2025.ChargeIdentity.Runtime.chargeRuntimeAfterFirst" do
    throwError "Basin wrong actual current"
  for key in ["whole_ledger_row", "claim", "time"] do
    unless (← field join key) == (← field parentJoin key) do throwError "Basin source join: {key}"
  unless (← field join "nuclear_charges") == (← field (← field parent "recovery") "decoded_Z") do
    throwError "Basin replaced recovered nuclear identity"
  unless (← field join "original_grid_sha256") == (← field (← field ledger "method") "grid_sha256") &&
      (← decode Nat (← field join "source_grid_rows")) == 233656 do throwError "Basin original grid"
  unless rationalRead (← rationalPair (← field join "physical_elapsed_time")) == 0 do throwError "Basin extra MD clock"
  unless (← decode (Array String) (← field value "field_names")) == SourceData.fieldNames do
    throwError "Basin field meaning changed"
  let protocol ← field value "protocol"
  for (key, expected) in [("field_scale", 1000000000000), ("block_rows", 1024)] do
    unless (← decode Nat (← field protocol key)) == expected do throwError "Basin field convention"
  for key in ["finite_flow_receipts_not_continuum_zero_flux", "flow_parameter_is_not_physical_time"] do
    unless (← decode Bool (← field protocol key)) == true do throwError "Basin flow scope"
  let attractors ← decode (Array Json) (← field value "attractors")
  unless attractors.size == 13 do throwError "Basin actual attractor census"
  for i in [:13] do
    unless (← decode Nat (← field attractors[i]! "atom")) == i do throwError "Basin nuclear incidence"
  let account ← field value "accounting"
  let blocks ← decode (Array Json) (← field account "blocks")
  let original ← decode (Array Json) (← field ledger "xc_grid_blocks")
  unless blocks.size == 229 && original.size == 229 &&
      (← decode (Array Nat) (← field account "old_xc_field_indices")) == #[0, 6, 7] do throwError "Basin original block census"
  for i in [:229] do
    let old ← decode (Array Int) original[i]!
    unless (← decode Int (← field blocks[i]! "first_row")) == old[0]! &&
        (← decode Int (← field blocks[i]! "row_count")) == old[1]! do throwError "Basin block incidence"
  let mapped ← decode (Array Json) (← field (← field account "old_ledger_account") "mapped_fields")
  let expected : Array Nat := #[0, 1, 2, 4, 5, 6, 7]
  unless mapped.size == 7 do throwError "Basin old-ledger field scope"
  for i in [:7] do
    unless (← decode Nat (← field mapped[i]! "field_index")) == expected[i]! do throwError "Basin old-ledger field index"
  let runtime ← field value "runtime"
  for key in ["new_scf_or_md", "grid_owner_used_for_assignment", "nearest_nucleus_used_for_assignment"] do
    unless (← decode Bool (← field runtime key)) == false do throwError "Basin source shortcut"
  for key in ["original_grid_preserved", "full_complex_state_retained_in_parent", "every_point_retained_in_raw", "unresolved_never_deleted"] do
    unless (← decode Bool (← field runtime key)) == true do throwError "Basin source loss"

end LAlanine40K2025.BasinPartition.SourceChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
