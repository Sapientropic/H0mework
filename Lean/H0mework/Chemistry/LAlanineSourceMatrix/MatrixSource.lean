import H0mework.Chemistry.LAlanineSourceField01.CacheComplete
import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerDataComplete

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix

open Lean Elab Term Command SourceRectangle SourceIntegerGrid SourceFiniteData SourceFields
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing

def fieldAOText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/source/field1-ao-cache.json"

private def intervals (value : Json) (rowSize : Nat) : TermElabM (List Interval) := do
  let entries ← decode (Array (Array Int)) value
  unless entries.size == rowSize && entries.all (fun e => e.size == 2 && e[0]! ≤ e[1]!) do
    throwError "field1 integer interval census or ordering"
  pure (entries.map fun e => (e[0]!, e[1]!)).toList

private def declareRows (stem : String) (rows : Array (List Interval)) : TermElabM Unit := do
  for i in [:rows.size] do
    let value := toExpr rows[i]!
    let type ← Meta.inferType value
    let name := (← getCurrNamespace) ++ Name.mkSimple (stem ++ toString i)
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
    modifyEnv (addNoncomputable · name)

elab "generateField1Matrix" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash fieldAOText == "a391e18639dc08d5b29fbf2d8c4f1ca9f01fc2b175f51684181b088f8a2cf75e" &&
      hash SourceIntegerMatrix.integerText == "59f1d909c8b2cab628b60ad19aacd80e37b887285c9c7d21718c25a6fcd5a0aa" do
    throwError "actual field1 AO or original D3 cache changed"
  let aoPacket ← parse fieldAOText
  let densityPacket ← parse SourceIntegerMatrix.integerText
  unless (← decode Nat (← field aoPacket "field")) == 1 &&
      (← decode Nat (← field aoPacket "jet_count")) == 10 &&
      (← decode Nat (← field aoPacket "scale_bits")) == 160 &&
      (← decode String (← field aoPacket "source_sha256")) == hash SourceFiniteData.sourceText &&
      (← decode String (← field aoPacket "field_packet_sha256")) == hash SourceRectangle.fieldText &&
      (← decode String (← field densityPacket "gaussian_source_sha256")) == hash SourceFiniteData.sourceText do
    throwError "same original Gaussian, field1 and S160 arithmetic"
  let fields ← decode (Array Json) (← field (← parse SourceRectangle.fieldText) "source_fields")
  unless (← field aoPacket "box") == (← field fields[1]! "box_integer_intervals") do
    throwError "same actual field1 rectangle"
  let aoRows ← decode (Array Json) (← field aoPacket "computed_ao")
  let densityRows ← decode (Array Json) (← field densityPacket "density_columns")
  unless aoRows.size == 10 && densityRows.size == 98 do throwError "complete low-jet/D3 census"
  let ao ← aoRows.mapM (intervals · 98)
  let columns ← densityRows.mapM (intervals · 98)
  let first := ao.map fun row => (columns.map fun column => dotList row column).toList
  let bilinear := first.map fun row => (ao.map fun right => dotList row right).toList
  declareRows "ao" ao
  declareRows "first" first
  declareRows "bilinear" bilinear

generateField1Matrix

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix
