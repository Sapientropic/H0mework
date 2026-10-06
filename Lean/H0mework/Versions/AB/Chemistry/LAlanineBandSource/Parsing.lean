import H0mework.Versions.AB.Chemistry.LAlanineTrueTubeWhole.SourceData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSource

open Lean Elab Term WholeCellSource SourceFields SourceRectangle Inertia.SourceParsing

def packetText : String := include_str "../../../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/whole_band/source.json"
def packetSha256 : String := "7dda20015b407afdd42a30019289b272f67e8798523267aa5a63ce715448e60e"
def originalFlowSha256 : String := "84522680aa3d0fc296fcf2a4754a63d2851612de190e1fa325f581e800a85936"
def originalCircuitSha256 : String := "8ecd634d8a43b2b62f0cfc7b55f46d971677547e7fe95cec0e0f690a0468aafe"

def verifiedPacket : TermElabM Json := do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash packetText == packetSha256 do throwError "whole-band source hash"
  let packet ← parse packetText
  unless (← decode String (← field packet "schema")) == "lalanine40k-whole-band-original-source/v1" &&
      (← decode String (← field packet "parent_current")) ==
        "LAlanine40K2025.BasinRefinement.TrueFlowQuantitativeRuntime.quantitativeRuntimeAfterFirst" do
    throwError "fixed quantitative parent"
  let gaussian ← parse SourceFiniteData.sourceText
  unless (← field packet "source_join") == (← field (← field gaussian "source") "parent_join") do
    throwError "same original M3 and full parent join"
  let inputs ← field packet "source_inputs"
  unless (← decode String (← field inputs "/tmp/lalanine-continuous-patch.LX7xoM/flow-16-v4-fixed-cellNone.json")) ==
      originalFlowSha256 &&
      (← decode String (← field inputs "/tmp/lalanine-continuous-patch.LX7xoM/fixed-circuits-16-v4-cellNone.jsonl.gz")) ==
      originalCircuitSha256 do throwError "original complete source archives"
  let protocol ← field packet "protocol"
  for (key, expected) in [("cells",32), ("directions",2), ("steps_per_direction",16), ("call_roles",2),
      ("calls",2048), ("rows",1024), ("segments",8), ("subsegments",4)] do
    unless (← decode Nat (← field protocol key)) == expected do throwError "whole-band census {key}"
  unless rationalRead (← sourceRational (← field protocol "step")) == 1/32 &&
      rationalRead (← sourceRational (← field protocol "physical_elapsed_time")) == 0 &&
      (← decode String (← field protocol "physical_time")) == "3q" do throwError "same source clocks"
  let arithmetic ← field packet "arithmetic"
  for (key, expected) in [("scale_bits",160), ("taylor_terms",16), ("order",2),
      ("ao_count",98), ("term_count",208), ("gaussian_group_count",94)] do
    unless (← decode Nat (← field arithmetic key)) == expected do throwError "original arithmetic {key}"
  let jets ← decode (Array Json) (← field (← field gaussian "generated_bounds") "multiindices")
  unless (← decode (Array Json) (← field arithmetic "multiindices")) == jets.extract 0 10 do
    throwError "original LowJet prefix"
  let cells ← sourceArray (← field packet "cells") 32
  for c in [:32] do
    for (key, expected) in [("index",c), ("segment",c/4), ("subsegment",c%4)] do
      unless (← decode Nat (← field cells[c]! key)) == expected do throwError "original cell incidence"
  let calls ← sourceArray (← field packet "calls") 2048
  for c in [:2048] do
    unless (← decode Nat (← field calls[c]! "index")) == c do throwError "original call incidence"
  let rows ← sourceArray (← field packet "rows") 1024
  for r in [:1024] do
    for (key, expected) in [("index",r), ("cell",r/32), ("direction",r%32/16), ("step",r%16),
        ("initial_call",2*r), ("tube_call",2*r+1)] do
      unless (← decode Nat (← field rows[r]! key)) == expected do throwError "original row incidence"
    unless (← decode Int (← field rows[r]! "sign")) == (if r%32 < 16 then -1 else 1) do
      throwError "original direction"
    unless (← field rows[r]! "initial_integer_box") == (← field calls[2*r]! "coordinate_integer_box") &&
        (← field rows[r]! "tube_integer_box") == (← field calls[2*r+1]! "coordinate_integer_box") do
      throwError "source row/call box join"
    if r%16 > 0 then
      unless (← field rows[r]! "initial_integer_box") == (← field rows[r-1]! "endpoint_integer_box") do
        throwError "literal original endpoint/initial join"
  pure packet

end LAlanine40K2025.BasinRefinement.WholeBandSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
