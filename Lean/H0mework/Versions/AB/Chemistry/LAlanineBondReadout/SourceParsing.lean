import H0mework.Versions.AB.Chemistry.LAlanineBondReadout.SourceSearchParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.SourceParsing

open Lean Elab Term Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String := "27c9d1c85e4d4112134657623050bbbbb6e51d66b95ea5b1bd12f692d8fb83eb"
def sourceText : String := include_str "../../../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/bond_readout/source/bond-readout.json"

def verifiedPacket : TermElabM Json := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do throwError "Bond source changed"
  let value ← parse sourceText
  let parent ← Reentry.SourceParsing.verifiedPacket
  let join ← field value "source_join"
  unless (← decode String (← field value "schema")) == "lalanine40k-source-generated-bond-readout/v1" &&
      (← decode String (← field join "parent_packet_sha256")) == Reentry.SourceParsing.sourceArtifactSha256 &&
      (← decode String (← field join "parent_raw_archive_sha256")) == Reentry.SourceParsing.sourceRawArchiveSha256 do
    throwError "Bond parent source"
  unless (← decode String (← field join "parent_runtime_current")) == "LAlanine40K2025.Reentry.Runtime.reentryRuntimeAfterFirst" &&
      (← decode String (← field join "whole_ledger_row")) == "bondDensityIncidenceAdjudication" &&
      (← decode String (← field join "claim")) == "registeredExperimentalGeometryModelBondTopology" do throwError "Bond root row"
  let nuclear ← field parent "nuclear"
  let parentJoin ← field parent "source_join"
  let frames ← decode (Array Json) (← field nuclear "frames")
  let physical ← field value "physical"
  let frame ← field physical "frame"
  unless frame == frames[1]! do throwError "Bond changed actual M3 frame"
  for (key, parentKey) in [("geometry_sha256", "target_geometry_sha256"),
      ("energy_ledger_sha256", "target_energy_ledger_sha256"), ("force_receipt_sha256", "target_force_receipt_sha256"),
      ("density_matrix_sha256", "target_density_matrix_sha256"), ("atomic_orbital_addresses", "atomic_orbital_addresses")] do
    unless (← field join key) == (← field parentJoin parentKey) do throwError "Bond source join: {key}"
  let ledger ← field nuclear "target_energy_ledger"
  unless (← field join "nuclear_inventory") == (← field ledger "nuclei") &&
      (← field join "density_matrix_sha256") == (← field frame "density_matrix_sha256") do throwError "Bond same-D/nuclei"
  let ledgerRef ← field physical "whole_energy_ledger_reference"
  unless (← decode String (← field ledgerRef "packet_sha256")) == Reentry.SourceParsing.sourceArtifactSha256 &&
      (← decode (Array String) (← field ledgerRef "json_path")) == #["nuclear", "target_energy_ledger"] do throwError "Bond whole ledger"
  let raw ← field physical "full_state_archive_reference"
  unless (← decode String (← field raw "sha256")) == Reentry.SourceParsing.sourceRawArchiveSha256 &&
      (← decode Nat (← field raw "array_count")) == 95 &&
      (← decode Nat (← field raw "element_count")) == 2961720 do throwError "Bond full-state archive"
  let electronic ← field parent "electronic"
  unless (← field physical "gamma_scale") == (← field electronic "target_gamma_scale") &&
      (← field physical "gamma_imaginary_nonzero_entries") == (← field electronic "target_imaginary_nonzero_entries") do
    throwError "Bond omitted complex source channel"
  unless (← field join "time") == (← field frame "time") &&
      (← field physical "generated_target_time") == (← field frame "time") &&
      rationalRead (← rationalPair (← field physical "physical_elapsed_time")) == 0 do throwError "Bond extra physical clock"
  let calculation ← field value "calculation"
  SearchParsing.verifySearch (← field calculation "finite_search_disposition")
  SearchParsing.verifySearch (← field (← field calculation "independent_atom_comparison") "finite_search_disposition")
  SearchParsing.verifyPairs calculation (← decode (Array Json) (← field ledger "nuclei"))
  let runtime ← field value "runtime"
  for key in ["new_molecular_scf_performed", "seed_replayed", "md_step_performed", "published_bond_table_consumed"] do
    unless (← decode Bool (← field runtime key)) == false do throwError "Bond source reset: {key}"
  for key in ["full_complex_state_retained", "independent_atom_reference_is_not_actual_state", "physical_time_unchanged"] do
    unless (← decode Bool (← field runtime key)) == true do throwError "Bond occurrence boundary: {key}"
  pure value

end LAlanine40K2025.BondReadout.SourceParsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
