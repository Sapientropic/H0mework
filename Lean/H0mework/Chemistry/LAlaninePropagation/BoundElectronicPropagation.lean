import Lean.Elab.Term
import Lean.Meta.AppBuilder
import Lean.ToExpr
import Lean.Data.Json
import H0mework.Cognition.Empirical.Sha256
import H0mework.Chemistry.LAlanineForce.BoundForceUpdate
import H0mework.Chemistry.LAlaninePropagation.NativeElectronicPropagation

/-! # Same-target source matrices, with no evolution or target premise -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Source

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String :=
  "1bc55ed9898a673ba14acffaaea6ba816fb9eddcbb234d0958c02a63ad5b0867"

private def sourceText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/propagation/source/lalanine40k-frozen-electronic-propagation.json"

private def predecessorText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/force/source/lalanine40k-force-material-next.json"

private def field (value : Lean.Json) (key : String) : Lean.Elab.TermElabM Lean.Json :=
  match value.getObjVal? key with
  | .ok result => pure result
  | .error error => throwError "Electronic source field {key}: {error}"

private def decode (α : Type) [Lean.FromJson α] (value : Lean.Json) : Lean.Elab.TermElabM α :=
  match Lean.fromJson? value with
  | .ok result => pure result
  | .error error => throwError "Electronic source decoder: {error}"

private def parse (text : String) : Lean.Elab.TermElabM Lean.Json :=
  match Lean.Json.parse text with
  | .ok result => pure result
  | .error error => throwError "Electronic source JSON: {error}"

private def sourcePropagation : Lean.Elab.TermElabM Lean.Json := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do
    throwError "Electronic source artifact SHA-256 changed"
  unless Sha256.hex predecessorText == Force.Source.sourceArtifactSha256 do
    throwError "Material predecessor changed"
  let source ← parse sourceText
  let previous ← parse predecessorText
  let join ← field source "source_join"
  let sourceKey ← decode String (← field join "force_artifact_sha256")
  unless sourceKey == Force.Source.sourceArtifactSha256 do
    throwError "Electronic source has another material occurrence"
  let previousTarget ← field previous "target"
  unless (← field join "target_geometry") == (← field previousTarget "geometry") do
    throwError "Electronic source has another target geometry"
  let previousStep ← field previous "generated_step"
  unless (← field join "predecessor_target_positions_picobohr") ==
      (← field previousStep "target_positions_picobohr") do
    throwError "Electronic source is not the integer-generated target"
  let previousLedger ← field previousTarget "energy_ledger"
  let previousMethod ← field previousLedger "method"
  for (localKey, previousKey) in
      [("target_density_matrix_sha256", "density_matrix_sha256"),
       ("target_grid_sha256", "grid_sha256"),
       ("target_grid_point_count", "grid_point_count")] do
    unless (← field join localKey) == (← field previousMethod previousKey) do
      throwError "Electronic source changed same-target {localKey}"
  let propagation ← field source "propagation"
  let count ← decode Nat (← field propagation "ao_dimension")
  let scale ← decode Nat (← field propagation "matrix_scale")
  let hamiltonianScale ← decode Nat (← field propagation "hamiltonian_scale")
  unless count == 98 && scale == 1000000000000 && hamiltonianScale == 1000000000000000 do
    throwError "Electronic basis or quantization changed"
  let pulse ← field propagation "pulse"
  for (key, expected) in [("field_numerator", 1), ("field_denominator", 1000), ("duration", 1)] do
    let actual ← decode Nat (← field pulse key)
    unless actual == expected do throwError "Source-fixed pulse {key} changed"
  pure propagation

/-- Reification checks the actual row incidence; target columns are not inputs to the source law. -/
def sourceMatrixRows : Lean.Elab.TermElabM (Array (Array Int)) := do
  let propagation ← sourcePropagation
  let columns ← decode (Array String) (← field propagation "matrix_columns")
  unless columns == #["left_basis", "right_basis", "overlap_pico", "inverse_sqrt_overlap_pico",
      "sqrt_overlap_pico", "field_free_hamiltonian_picohartree", "position_x_picobohr",
      "position_y_picobohr", "position_z_picobohr", "initial_density_pico",
      "active_hamiltonian_femtohartree", "propagator_real_pico", "propagator_imaginary_pico",
      "next_density_real_pico", "next_density_imaginary_pico"] do
    throwError "Electronic row semantics changed"
  let rows ← decode (Array (Array Int)) (← field propagation "matrix_rows")
  unless rows.size == 4851 && rows.all (fun row => row.size == 15) do
    throwError "Electronic upper-triangle incidence changed"
  let mut index := 0
  for left in [:98] do
    for right in [left:98] do
      let row := rows[index]!
      unless row[0]! == Int.ofNat left && row[1]! == Int.ofNat right do
        throwError "Electronic source row {index} changed address"
      unless row[10]! == 1000 * row[5]! + row[8]! do
        throwError "Electronic source used another Hamiltonian"
      index := index + 1
  pure rows

/-- Small blocks preserve every row while bounding kernel reduction depth. -/
def upperRead (blocks : Array (Array Int)) : UpperTriangle :=
  fun index => (blocks[index.val / 64]!)[index.val % 64]!

private def upperBlocks (values : Array Int) : Array (Array Int) :=
  ((List.range ((values.size + 63) / 64)).map fun block =>
    values.extract (64 * block) (min values.size (64 * (block + 1)))).toArray

elab "lalanineElectronicInput%" : term => do
  let rows ← sourceMatrixRows
  let columns ← #[5, 8, 9].mapM fun column =>
    Lean.Meta.mkAppM ``upperRead
      #[Lean.toExpr (upperBlocks ((rows.toList.map fun row => row[column]!).toArray))]
  Lean.Meta.mkAppM ``ElectronicPropagationSource.mk columns

noncomputable def electronicSource : ElectronicPropagationSource := lalanineElectronicInput%

end LAlanine40K2025.Propagation.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
