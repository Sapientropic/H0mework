import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source.SourceBoundLAlanineThermalOccurrence
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Literals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Lean Elab Term

def originalFrameText : String := include_str "../../../../../../../../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/lalanine40k-target-erased-quantum-bond-density/thermal/source/lalanine40k-partial-swap-thermal-collision.json"

private def field (value : Json) (key : String) : TermElabM Json :=
  match value.getObjVal? key with
  | .ok value => pure value
  | .error error => throwError "Energy frame source {key}: {error}"

private def decode (α : Type) [FromJson α] (value : Json) : TermElabM α :=
  match fromJson? value with
  | .ok value => pure value
  | .error error => throwError "Energy frame source decode: {error}"

elab "originalEnergyFrame%" : term => do
  unless SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex originalFrameText ==
      Thermal.Source.thermalArtifactSha256 do throwError "Original energy frame source changed"
  let packet ← match Json.parse originalFrameText with
    | .ok p => pure p
    | .error e => throwError "Energy frame JSON: {e}"
  let join ← field packet "source_join"
  unless (← decode String (← field join "native_frame_sha256")) == Propagation.Source.nativeFrameArtifactSha256 do
    throwError "Energy frame original current join"
  let frame ← field (← field packet "collision") "energy_basis"
  unless (← decode Nat (← field frame "vector_scale")) == 1000000000000000 do
    throwError "Original vector scale"
  let rows ← decode (List (List Int)) (← field frame "vector_rows")
  unless rows.length == 98 && rows.all (fun row => row.length == 98) do
    throwError "Original full98x98 energy frame"
  return toExpr rows

set_option maxRecDepth 16384 in
noncomputable def originalRows : List (List Int) := originalEnergyFrame%

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
