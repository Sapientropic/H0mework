import H0mework.Chemistry.LAlanineInertia.SourceSourceBoundLAlanine40KInertialStep
import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.SourceParsing

open Lean Elab Term
open LAlanine40K2025.Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String :=
  "4fef4ec2e7e0a692dafa0c169f0f744f898669213df1d66dc23d4c44f09e80d5"

private def sourceText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/electronic_frame/source/electronic-frame.json"
private def inertiaText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/source/lalanine40k-inertial-next.json"
private def electronicText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/propagation/source/lalanine40k-frozen-electronic-propagation.json"

/-- The geometry hash uses the producer's sorted, two-space, newline-terminated JSON. -/
private partial def indentedJSON (indent : Nat) : Json → String
  | .arr values =>
    if values.isEmpty then "[]" else
      "[\n" ++ String.intercalate ",\n" (values.toList.map fun value =>
        String.ofList (List.replicate (indent + 2) ' ') ++ indentedJSON (indent + 2) value) ++
        "\n" ++ String.ofList (List.replicate indent ' ') ++ "]"
  | .obj values =>
    if values.isEmpty then "{}" else
      "{\n" ++ String.intercalate ",\n" (values.toArray.toList.map fun (key, value) =>
        String.ofList (List.replicate (indent + 2) ' ') ++ (Json.str key).compress ++ ": " ++
          indentedJSON (indent + 2) value) ++ "\n" ++ String.ofList (List.replicate indent ' ') ++ "}"
  | value => value.compress

def verifiedPacket : TermElabM Json := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do throwError "Electronic-frame source changed"
  unless Sha256.hex inertiaText == Inertia.Source.sourceArtifactSha256 do throwError "Inertial parent changed"
  unless Sha256.hex electronicText == Propagation.Source.sourceArtifactSha256 do throwError "Original electronic parent changed"
  let value ← parse sourceText
  let parent ← parse inertiaText
  let electronic ← parse electronicText
  unless (← decode String (← field value "schema")) == "lalanine40k-inertial-electronic-frame/v1" do
    throwError "Electronic-frame schema changed"
  let join ← field value "source_join"
  unless (← decode String (← field join "inertial_artifact_sha256")) == Inertia.Source.sourceArtifactSha256 &&
      (← decode String (← field join "original_electronic_artifact_sha256")) == Propagation.Source.sourceArtifactSha256 do
    throwError "Electronic frame belongs to another occurrence"
  let frames ← decode (Array Json) (← field parent "frames")
  let geometryHashes ← decode (Array String) (← field join "frame_geometry_sha256")
  let densityHashes ← decode (Array Json) (← field join "frame_density_sha256")
  let ledgerHashes ← decode (Array Json) (← field join "frame_energy_ledger_sha256")
  unless frames.size == 2 && geometryHashes.size == 2 && densityHashes.size == 2 && ledgerHashes.size == 2 do
    throwError "Changed frame incidence"
  for index in [:2] do
    unless Sha256.hex (indentedJSON 0 (← field frames[index]! "geometry") ++ "\n") == geometryHashes[index]! do
      throwError "Electronic-frame geometry digest changed"
    unless densityHashes[index]! == (← field frames[index]! "density_matrix_sha256") &&
        ledgerHashes[index]! == (← field frames[index]! "energy_ledger_sha256") do
      throwError "Electronic-frame density or energy occurrence changed"
  let previousJoin ← field electronic "source_join"
  unless (← field frames[0]! "geometry") == (← field previousJoin "target_geometry") &&
      geometryHashes[0]! == (← decode String (← field previousJoin "target_geometry_sha256")) do
    throwError "Original electronic geometry changed"
  let ledger ← field parent "target_energy_ledger"
  let inventory ← field join "nuclear_inventory"
  let addresses ← field join "atomic_orbital_addresses"
  unless inventory == (← field ledger "nuclei") && addresses == (← field ledger "ao_addresses") do
    throwError "Nuclear/AO incidence changed"
  unless (← decode (Array Json) inventory).size == 13 && (← decode (Array Json) addresses).size == 98 do
    throwError "Nuclear/AO carrier changed"
  pure value

def matrixRead (rows : Array (Array Int)) : Matrix Propagation.Interface.Basis Propagation.Interface.Basis Int :=
  fun left right => (rows[left.val]!)[right.val]!

def crossRows (value : Json) : TermElabM (Array (Array Int)) := do
  let pairing ← field value "cross_pairing"
  unless (← decode Nat (← field pairing "scale")) == 1000000000000000 &&
      (← decode String (← field pairing "orientation")) == "target bra / source ket" do
    throwError "Cross-pairing scale or direction changed"
  let rows ← decode (Array (Array Int)) (← field pairing "rows")
  unless rows.size == 98 && rows.all (fun row => row.size == 98) do throwError "Cross-pairing matrix is not 98 by 98"
  pure rows

private def upperBlocks (values : Array Int) : Array (Array Int) :=
  ((List.range ((values.size + 63) / 64)).map fun block =>
    values.extract (64 * block) (min values.size (64 * (block + 1)))).toArray

def targetSourceExpr (value : Json) : TermElabM Expr := do
  let target ← field value "target_electronic_frame"
  unless (← decode Nat (← field target "scale")) == 1000000000000 &&
      (← decode (Array String) (← field target "columns")) ==
        #["left", "right", "H0_picohartree", "Z_picobohr", "SCF_density_pico"] do
    throwError "Target electronic columns changed"
  let rows ← decode (Array (Array Int)) (← field target "upper_rows")
  unless rows.size == 4851 && rows.all (fun row => row.size == 5) do throwError "Target upper triangle changed"
  let mut index := 0
  for left in [:98] do
    for right in [left:98] do
      unless (rows[index]!)[0]! == Int.ofNat left && (rows[index]!)[1]! == Int.ofNat right do
        throwError "Target electronic address changed"
      index := index + 1
  let columns ← #[2, 3, 4].mapM fun column =>
    Meta.mkAppM ``Propagation.Source.upperRead
      #[toExpr (upperBlocks (rows.map fun row => row[column]!))]
  Meta.mkAppM ``Propagation.Interface.ElectronicPropagationSource.mk columns

end LAlanine40K2025.ElectronicFrame.SourceParsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
