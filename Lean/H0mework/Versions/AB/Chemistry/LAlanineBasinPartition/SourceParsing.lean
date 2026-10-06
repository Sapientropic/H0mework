import H0mework.Versions.AB.Chemistry.LAlanineBasinPartition.SourceChecks

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.SourceParsing

open Lean Elab Term Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String := "f70bf04a3deea6a0221baef8fe9a6aefdae988f2a57ba1cd785d2477c2eabd69"
def sourceRawArchiveSha256 : String := "d4a6b6f194a940a31fd81b453c9261503bffeff47fb07aa1601e6eb96a60f957"
def sourceText : String := include_str "../../../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_partition/source/basin-partition.json"

def verifiedData : TermElabM (Json × Json) := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do throwError "Basin source changed"
  let packet ← parse sourceText
  unless Sha256.hex ChargeIdentity.SourceParsing.sourceText == ChargeIdentity.SourceParsing.sourceArtifactSha256 do
    throwError "Basin identity source changed"
  let parent ← parse ChargeIdentity.SourceParsing.sourceText
  let reentry ← Reentry.SourceParsing.verifiedPacket
  let ledger ← field (← field reentry "nuclear") "target_energy_ledger"
  SourceChecks.verify packet parent ledger
  pure (packet, ledger)

end LAlanine40K2025.BasinPartition.SourceParsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
