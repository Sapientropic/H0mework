import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Reifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.SourceReifier
open Lean Elab Term Command
open Inertia.SourceParsing

def recordedText : String := include_str "../../../../../../../../../../../../../../../evidence/biomedical/lalanine40k-ao-metric-packet.json"

elab "generateRecordedMetric" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash recordedText == "bba2a493933f05026b03b352fa1a8961b3ab63ae5e858213bdecf22452d604d0" do
    throwError "original recorded metric packet"
  let packet ← parse recordedText
  let source ← field packet "source"
  unless (← decode String (← field source "reentry_raw_sha256")) ==
      "e2529442350d15b0e35468eff0972000f701a0a58f5efcbe7ec7152d74bf2145" do
    throwError "original Reentry archive"
  let arrays ← field packet "arrays"
  for (key,name) in [("target_overlap",`recordedOverlapRows),("target_inverse_root",`recordedInverseRows)] do
    let rows ← decode (Array (Array Json)) (← field arrays key)
    unless rows.size == 98 && rows.all (fun row => row.size == 98) do
      throwError "original full AO matrix"
    let rows ← rows.mapM (·.mapM rational)
    discard <| declare name (toExpr rows)

end LAlanine40K2025.UnifiedOrbitals.SourceReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
