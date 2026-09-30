import H0mework.Chemistry.LAlanineRefinementDensity.LaplaceIntegers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceRowData

open Lean Elab Term Command
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing
open SourceFiniteData

abbrev Direction := Fin 6

def innerAxis : Direction → Fin 3 := ![0, 0, 0, 1, 1, 2]
def outerAxis : Direction → Fin 3 := ![0, 1, 2, 1, 2, 2]

def sourceText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/source/jet-contractions.json"
def jetText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/source/gaussian-jets.json"

def rowRead (rows : Array (Array Nat)) (direction : Direction) (basis : Basis) : Nat :=
  (rows[direction.val]!)[basis.val]!

def sumRead (rows : Array Nat) (direction : Direction) : Nat := rows[direction.val]!

elab "generateContractionRows" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash sourceText == "a148a9ff86752a80c0907e5f6976ed7ae4fc62d74eaf7cffbb399894f751b5dc" &&
      hash jetText == "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" do
    throwError "Contraction source changed"
  let packet ← parse sourceText
  let jet ← parse jetText
  let existing ← parse SourceFiniteData.sourceText
  unless (← decode String (← field packet "schema")) == "lalanine40k-source-generated-fourth-density-row-trace/v1" do
    throwError "Contraction schema"
  let join ← field packet "source_join"
  unless (← decode String (← field join "jet_packet_sha256")) == hash jetText &&
      (← field join "parent_source") == (← field jet "source") &&
      (← decode Nat (← field join "ao_count")) == 98 &&
      (← decode Nat (← field join "source_denominator")) == 10^30 do throwError "Contraction root incidence"
  let current ← field existing "source"
  unless (← field (← field jet "source") "parent_join") == (← field current "parent_join") do
    throwError "Contraction changed physical occurrence"
  for key in ["orbital_integer_bounds", "density_matrix_absolute_integer_bounds", "multiindices"] do
    unless (← field (← field jet "generated_bounds") key) == (← field (← field existing "generated_bounds") key) do
      throwError "Contraction changed source table: {key}"
  for key in ["centre", "radius"] do
    unless (← field (← field jet "geometry") key) == (← field (← field existing "geometry") key) do
      throwError "Contraction changed source cube"
  let directions ← decode (Array Json) (← field packet "directions")
  let expected : Array (Array Nat) := #[#[4,0,0], #[2,2,0], #[2,0,2], #[0,4,0], #[0,2,2], #[0,0,4]]
  unless directions.size == 6 do throwError "Contraction direction census"
  let mut rows : Array (Array Nat) := #[]
  let mut sums : Array Nat := #[]
  for i in [:6] do
    unless (← decode (Array Nat) (← field directions[i]! "multiindex")) == expected[i]! do
      throwError "Contraction derivative incidence"
    let row ← decode (Array Nat) (← field directions[i]! "ao_rows")
    unless row.size == 98 do throwError "Contraction AO row census"
    rows := rows.push row
    sums := sums.push (← decode Nat (← field directions[i]! "whole_integer_sum"))
  for (name, value) in [(`sourceRow, ← Meta.mkAppM ``rowRead #[toExpr rows]),
      (`sourceSum, ← Meta.mkAppM ``sumRead #[toExpr sums])] do
    let name := (← getCurrNamespace) ++ name
    let type ← Meta.inferType value
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
    modifyEnv (addNoncomputable · name)

generateContractionRows

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLaplaceRowData
