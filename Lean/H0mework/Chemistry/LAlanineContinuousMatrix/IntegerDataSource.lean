import H0mework.Chemistry.LAlanineContinuousMatrix.IntegerLists
import H0mework.Chemistry.LAlanineContinuousChecks.AOCalculatedData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix

open Lean Elab Term Command SourceRectangle SourceIntegerGrid SourceFiniteData
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing

def integerText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/source/field0-integer-matrix.json"
def aoText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/source/field0-ao-cache.json"

private def intervals (value : Json) (width : Nat) : TermElabM (List Interval) := do
  let entries ← decode (Array (Array Int)) value
  unless entries.size == width && entries.all (fun e => e.size == 2 && e[0]! ≤ e[1]!) do
    throwError "integer interval census or ordering"
  pure (entries.map fun entry => (entry[0]!, entry[1]!)).toList

private def declareRows (stem : String) (rows : Array (List Interval)) : TermElabM Unit := do
  for i in [:rows.size] do
    let value := toExpr rows[i]!
    let type ← Meta.inferType value
    let name := (← getCurrNamespace) ++ Name.mkSimple (stem ++ toString i)
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
    modifyEnv (addNoncomputable · name)

elab "generateSourceIntegerMatrix" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash integerText == "59f1d909c8b2cab628b60ad19aacd80e37b887285c9c7d21718c25a6fcd5a0aa" &&
      hash aoText == "c90a34819cd8854b8fc4f7ab22ab19b493683b2e9523b154627bf2684fb743fd" &&
      hash SourceFiniteData.sourceText == "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" do
    throwError "fixed integer matrix source"
  let packet ← parse integerText
  let originalAO ← parse aoText
  let gaussian ← parse SourceFiniteData.sourceText
  unless (← decode Nat (← field packet "scale_bits")) == 160 &&
      (← decode Nat (← field packet "source_field")) == 0 &&
      (← decode String (← field packet "ao_source_sha256")) == hash aoText &&
      (← decode String (← field packet "gaussian_source_sha256")) == hash SourceFiniteData.sourceText do
    throwError "source matrix arithmetic or occurrence"
  let gaussianJoin ← field gaussian "source"
  unless (← field packet "same_original_parent_join") == (← field gaussianJoin "parent_join") &&
      (← field packet "physical_raw_sha256") == (← field gaussianJoin "reentry_raw_sha256") do
    throwError "same actual M3 and whole-ledger join"
  let aoRaw ← decode (Array Json) (← field originalAO "computed_ao")
  unless aoRaw.size == 20 do throwError "source AO derivative census"
  let ao ← aoRaw.mapM (intervals · 98)
  let density ← decode (Array (Array Json)) (← field (← field gaussian "gaussian_source") "density_matrix")
  unless density.size == 98 && density.all (fun row => row.size == 98) do
    throwError "original D3 complete census"
  let mut columns : Array (List Interval) := #[]
  for column in [:98] do
    let mut values : Array Interval := #[]
    for row in [:98] do
      let rational ← decode (Array Json) (density[row]!)[column]!
      unless rational.size == 2 do throwError "original D3 rational"
      let numerator ← decode Int rational[0]!
      let divisor ← decode Nat rational[1]!
      unless divisor > 0 do throwError "original D3 denominator"
      let scaled := numerator * (SourceIntegerGrid.denominator : Int)
      values := values.push (scaled / divisor, -((-scaled) / divisor))
    columns := columns.push values.toList
  -- Computation reads only source AO/D3; the packet rows are checked afterward.
  let first := ao.map fun row => (columns.map fun column => dotList row column).toList
  let bilinear := first.map fun row => (ao.map fun right => dotList row right).toList
  for (key, actual, width) in [("ao_rows", ao, 98), ("density_columns", columns, 98),
      ("first_rows", first, 98), ("bilinear_rows", bilinear, 20)] do
    let expected ← decode (Array Json) (← field packet key)
    unless expected.size == actual.size do throwError "integer source row census"
    let expected ← expected.mapM (intervals · width)
    unless actual == expected do throwError "source integer computation changed {key}"
  declareRows "ao" ao
  declareRows "density" columns
  declareRows "first" first
  declareRows "bilinear" bilinear

generateSourceIntegerMatrix

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceIntegerMatrix
