import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Source
import H0mework.Chemistry.LAlanineEntropy.JointEnergyReadout

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Reentry.TargetFock.Reifier
open Lean Elab Term Command Inertia.SourceParsing Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator

def sourceText : String := include_str "../../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/lalanine40k-m3-fock/source/packet.json"

elab "generateOriginalM3Fock" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash sourceText == "ef42e5ae04dfb428ebe89b3abf419dc0c564ab9265427a83930190c678ca0b8d" do
    throwError "registered M3 Fock packet"
  let packet ← parse sourceText
  let source ← field packet "source"
  unless (← decode String (← field source "reentry_packet_sha256")) == Reentry.SourceParsing.sourceArtifactSha256 &&
      (← decode String (← field source "reentry_raw_sha256")) == Reentry.SourceParsing.sourceRawArchiveSha256 do
    throwError "original M3 occurrence"
  let references ← field source "array_references"
  let fock ← field references "fock_matrix"
  unless (← decode String (← field fock "sha256")) ==
      "d160aed634c04f738467e527fcb5dec1398a7ab1f716d3779724d06e4ca1ac43" do
    throwError "original M3 Fock array"
  let rows ← decode (Array (Array Json)) (← field packet "fock_upper_dyadic")
  unless rows.size == 98 do throwError "source Fock row census"
  let mut out : Array (Array (Int × Nat)) := #[]
  for i in [:98] do
    unless rows[i]!.size == 98-i do throwError "source Fock upper row census"
    let row ← rows[i]!.mapM fun item => do
      let pair ← decode (Array Json) item
      unless pair.size == 2 do throwError "source Fock dyadic"
      let n ← decode Int pair[0]!
      let d ← decode Nat pair[1]!
      unless d > 0 do throwError "source Fock denominator"
      pure (n,d)
    out := out.push row
  let name := (← getCurrNamespace) ++ `upperRows
  let value := toExpr out
  let type ← Meta.inferType value
  addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe})
  modifyEnv (addNoncomputable · name)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Reentry.TargetFock.Reifier
