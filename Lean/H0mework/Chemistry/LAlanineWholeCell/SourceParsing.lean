import H0mework.Chemistry.LAlanineWholeCell.SourceGrouped
import H0mework.Chemistry.LAlanineWholeCell.PartitionSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellSource

open Lean Elab Term Command
open Inertia.SourceParsing

def packetText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/whole_cell/source.json"
def packetSha256 : String := "599442b28c2624f1a5d07d5f7a01daeba8f139113257aecc2a494322209fe3de"

def sourceArray (value : Json) (count : Nat) : TermElabM (Array Json) := do
  let entries ← decode (Array Json) value
  unless entries.size == count do throwError "whole-cell source census {count}"
  pure entries

def sourceInterval (value : Json) : TermElabM (Int × Int) := do
  let entries ← decode (Array Int) value
  unless entries.size == 2 && entries[0]! ≤ entries[1]! do throwError "whole-cell ordered source interval"
  pure (entries[0]!, entries[1]!)

def sourceReduction (value : Json) : TermElabM (Nat × Nat) := do
  let entries ← decode (Array Nat) value
  unless entries.size == 2 do throwError "whole-cell reduction endpoints"
  pure (entries[0]!, entries[1]!)

def sourceRational (value : Json) : TermElabM (Int × Nat) := do
  let entries ← sourceArray value 2
  let numerator ← decode Int entries[0]!
  let denominator ← decode Nat entries[1]!
  unless denominator > 0 do throwError "whole-cell positive denominator"
  pure (numerator, denominator)

def verifiedPacket : TermElabM Json := do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash packetText == packetSha256 do throwError "whole-cell source changed"
  let packet ← parse packetText
  unless (← decode String (← field packet "schema")) ==
      "lalanine40k-source-generated-whole-cell-spatial-compact/v1" do throwError "whole-cell source schema"
  let gaussian ← parse SourceFiniteData.sourceText
  unless (← field packet "source_join") == (← field (← field gaussian "source") "parent_join") do
    throwError "whole-cell original physical occurrence"
  unless (← decode String (← field packet "parent_current")) ==
      "LAlanine40K2025.BasinRefinement.SpatialRuntime.spatialRuntimeAfterFirst" do
    throwError "whole-cell installed parent current"
  let protocol ← field packet "protocol"
  for (key, expected) in [("cell", 16), ("source_segment", 4), ("source_subsegment", 0), ("rk4_steps", 4)] do
    unless (← decode Nat (← field protocol key)) == expected do throwError "whole-cell source address {key}"
  unless rationalRead (← sourceRational (← field protocol "physical_elapsed_time")) == 0 do
    throwError "whole-cell does not advance physical time"
  let arithmetic ← field packet "arithmetic"
  for (key, expected) in [("scale_bits", 160), ("taylor_terms", 16), ("order", 2),
      ("ao_count", 98), ("term_count", 208), ("gaussian_group_count", 94)] do
    unless (← decode Nat (← field arithmetic key)) == expected do throwError "whole-cell arithmetic {key}"
  let originalJets ← decode (Array Json) (← field (← field gaussian "generated_bounds") "multiindices")
  unless (← decode (Array Json) (← field arithmetic "multiindices")) == originalJets.extract 0 10 do
    throwError "same original low-jet addresses"
  let fields ← sourceArray (← field packet "fields") 65
  for f in [:65] do
    unless (← decode Nat (← field fields[f]! "index")) == f do throwError "whole-cell field index"
  let leaves ← sourceArray (← field packet "leaves") 4
  for q in [:4] do
    let address := #["00", "01", "10", "11"][q]!
    unless (← decode String (← field leaves[q]! "address")) == address do throwError "source binary leaf address"
    let calls ← decode (Array Nat) (← field leaves[q]! "field_indices")
    unless calls.size == 17 && calls.all (· < 65) do throwError "complete source field-call census"
    for call in [:17] do
      let occurrences ← decode (Array Json) (← field fields[calls[call]!]! "raw_occurrences")
      let registered ← occurrences.anyM fun occurrence => do
        return (← decode String (← field occurrence "node")) == address &&
          (← decode Nat (← field occurrence "call")) == call
      unless registered do throwError "actual leaf occurrence does not select source field"
  pure packet

def declareSource (suffix : Name) (value : Expr) : TermElabM Unit := do
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

end LAlanine40K2025.BasinRefinement.WholeCellSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
