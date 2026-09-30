import H0mework.Chemistry.LAlanineElectronicFrame.SourceElectronicFrameParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.SourceParsing

open Lean Elab Term
open Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String := "0d4ead67192b1965c224a723ded0273599e714ad2dd1a467a932ad8a41ebacad"

private def sourceText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/held_force/source/held-force.json"
private def parentText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/source/lalanine40k-inertial-next.json"

def verifiedPacket : TermElabM Json := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do throwError "Held-force source changed"
  unless Sha256.hex parentText == Inertia.Source.sourceArtifactSha256 do throwError "Inertial current changed"
  let value ← parse sourceText
  let frame ← ElectronicFrame.SourceParsing.verifiedPacket
  let parent ← parse parentText
  let frames ← decode (Array Json) (← field parent "frames")
  unless frames.size == 2 do throwError "Inertial frame census changed"
  unless (← decode String (← field value "schema")) == "lalanine40k-held-electronic-force/v1" do
    throwError "Held-force schema changed"
  let join ← field value "source_join"
  let frameJoin ← field frame "source_join"
  unless (← decode String (← field join "electronic_frame_sha256")) == ElectronicFrame.SourceParsing.sourceArtifactSha256 do
    throwError "Held force belongs to another electronic frame"
  for key in ["inertial_artifact_sha256", "original_electronic_artifact_sha256", "nuclear_inventory", "atomic_orbital_addresses"] do
    unless (← field join key) == (← field frameJoin key) do throwError "Held-force parent join changed: {key}"
  unless (← field value "geometry") == (← field frames[1]! "geometry") &&
      (← field value "physical_time") == (← field frames[1]! "time") do throwError "Held force changed the actual material/time"
  let geometryHashes ← decode (Array Json) (← field frameJoin "frame_geometry_sha256")
  unless (← field join "current_geometry_sha256") == geometryHashes[1]! do throwError "Geometry digest changed"
  let response ← field value "response"
  let force ← field response "force"
  let ledger ← field response "energy_ledger"
  unless (← field force "source_nuclei") == (← field join "nuclear_inventory") &&
      (← field ledger "nuclei") == (← field join "nuclear_inventory") &&
      (← field ledger "ao_addresses") == (← field join "atomic_orbital_addresses") do
    throwError "Held response lost nuclear/AO incidence"
  let forceMethod ← field force "method"
  let ledgerMethod ← field ledger "method"
  unless (← field forceMethod "density_matrix_sha256") == (← field ledgerMethod "density_matrix_sha256") do
    throwError "Energy and force use different densities"
  unless (← decode String (← field forceMethod "energy_weighted_density")) ==
      "Qframe = D F(D) S^(-1), generally nonsymmetric; dD = -S^(-1) dB^T D - D dB S^(-1)" do
    throwError "Stationary force replaced the frame derivative"
  let runtime ← field value "runtime"
  unless (← decode Bool (← field runtime "held_scf_performed")) == false do throwError "Held-state SCF reset"
  let realization ← field value "held_realization"
  unless (← decode Nat (← field realization "gamma_scale")) == 1000000000000 &&
      (← decode Bool (← field realization "additional_scf_performed")) == false do throwError "Held realization changed"
  pure value

def gammaExpr (value : Json) : TermElabM Expr := do
  let realization ← field value "held_realization"
  let rows ← decode (Array (Array Int)) (← field realization "gamma_rows")
  unless rows.size == 98 && rows.all (fun row => row.size == 98) do throwError "Held matrix census changed"
  for left in [:98] do
    for right in [:98] do
      unless (rows[left]!)[right]! == (rows[right]!)[left]! do throwError "Held matrix symmetry changed"
  Meta.mkAppM ``ElectronicFrame.SourceParsing.matrixRead #[toExpr rows]

end LAlanine40K2025.HeldForce.SourceParsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
