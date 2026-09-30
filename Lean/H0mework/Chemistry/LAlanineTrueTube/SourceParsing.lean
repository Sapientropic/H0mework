import H0mework.Chemistry.LAlanineWholeCell.SourceData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeSource

open Lean Elab Term SourceRectangle SourceFields WholeCellSource
open Inertia.SourceParsing

def packetText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/true_tube/source.json"
def packetSha256 : String := "be6ad841a6dced9d6402125c5d669ba646d097420ad38abd25d16d4e8ad9c8be"

def verifiedPacket : TermElabM Json := do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash packetText == packetSha256 do throwError "exact true-tube packet"
  let packet ← parse packetText
  unless (← decode String (← field packet "schema")) == "lalanine40k-actual-cell16-true-tube-source/v1" do
    throwError "true-tube schema"
  let gaussian ← parse SourceFiniteData.sourceText
  unless (← field packet "source_join") == (← field (← field gaussian "source") "parent_join") do
    throwError "same actual M3 source"
  unless (← decode String (← field packet "parent_current")) ==
      "LAlanine40K2025.BasinRefinement.BoundaryRuntime.boundaryRuntimeAfterFirst" do
    throwError "fixed current root"
  let protocol ← field packet "protocol"
  for (key, expected) in [("cell",16), ("source_segment",4), ("source_subsegment",0),
      ("directions",2), ("steps_per_direction",16)] do
    unless (← decode Nat (← field protocol key)) == expected do throwError "true-tube address {key}"
  unless rationalRead (← sourceRational (← field protocol "step")) == 1/32 do throwError "original step"
  unless rationalRead (← sourceRational (← field protocol "physical_elapsed_time")) == 0 &&
      (← decode String (← field protocol "physical_time")) == "3q" do throwError "physical clock"
  let arithmetic ← field packet "arithmetic"
  for (key, expected) in [("scale_bits",160), ("taylor_terms",16), ("order",2),
      ("ao_count",98), ("term_count",208), ("gaussian_group_count",94)] do
    unless (← decode Nat (← field arithmetic key)) == expected do throwError "true-tube arithmetic {key}"
  let jets ← decode (Array Json) (← field (← field gaussian "generated_bounds") "multiindices")
  unless (← decode (Array Json) (← field arithmetic "multiindices")) == jets.extract 0 10 do
    throwError "same original low-jet order"
  let calls ← sourceArray (← field packet "calls") 64
  for c in [:64] do
    unless (← decode Nat (← field calls[c]! "index")) == c &&
        (← decode Nat (← field calls[c]! "original_call")) == 1024+c do throwError "source call index"
  let rows ← sourceArray (← field packet "rows") 32
  for r in [:32] do
    for (key, expected) in [("index",r), ("original_row",512+r), ("direction",r/16), ("step",r%16),
        ("initial_call",1024+2*r), ("tube_call",1025+2*r)] do
      unless (← decode Nat (← field rows[r]! key)) == expected do throwError "actual row incidence {key}"
    unless (← decode Int (← field rows[r]! "sign")) == (if r < 16 then -1 else 1) do
      throwError "source direction"
    unless (← field rows[r]! "initial_integer_box") == (← field calls[2*r]! "coordinate_integer_box") &&
        (← field rows[r]! "tube_integer_box") == (← field calls[2*r+1]! "coordinate_integer_box") do
      throwError "row/call rectangle incidence"
    if r%16 > 0 then
      unless (← field rows[r]! "initial_integer_box") == (← field rows[r-1]! "endpoint_integer_box") do
        throwError "literal target/current continuity"
  let fields ← sourceArray (← field packet "fields") 3
  for f in [:3] do
    unless (← decode Nat (← field fields[f]! "index")) == f do throwError "first-field index"
    let c := #[0,1,33][f]!
    unless (← field fields[f]! "coordinate_integer_box") == (← field calls[c]! "coordinate_integer_box") &&
        (← field fields[f]! "range_reduction_by_group") == (← field calls[c]! "range_reduction_by_group") do
      throwError "actual first-field source call"
  unless (← field rows[0]! "initial_integer_box") == (← field rows[16]! "initial_integer_box") do
    throwError "common actual initial occurrence"
  pure packet

end LAlanine40K2025.BasinRefinement.TrueTubeSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
