import H0mework.Versions.AB.Chemistry.LAlanineReentry.SourceSourceBoundReentry
import Mathlib.Data.Matrix.Mul
import Lean

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped Matrix

abbrev OccupiedSlot := Fin 24

end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor

namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Reification
open Lean Elab Term Command Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
private def sourceText : String := include_str "../../../../../../../../../../../../../../../../../evidence/biomedical/lalanine40k-orbitals-occupation-factor.json"
private def originalText : String := include_str "../../../../../../../../../../../../../../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/reentry/source/reentry.json"

private def declareReadout (suffix : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

private def verifiedPacket : TermElabM (Array (Array Int) × Array (Array Int) × Nat × String) := do
  unless Sha256.hex originalText == LAlanine40K2025.Reentry.SourceParsing.sourceArtifactSha256 do
    throwError "original reentry packet changed"
  let original ← parse originalText
  let targetLedger ← field (← field original "nuclear") "target_energy_ledger"
  let sourceElectronCount ← decode Nat (← field (← field targetLedger "electron_balance")
    "source_electron_count")
  let densityInterpretation ← decode String (← field (← field targetLedger "method")
    "density_matrix")
  unless sourceElectronCount == 48 && densityInterpretation ==
    "closed-shell spin-summed D; D_alpha = D_beta = D / 2" do
      throwError "original source spin and electron-count identity"
  let packet ← parse sourceText
  unless (← decode String (← field packet "schema")) == "lalanine40k-source-gamma-24-plane-candidate-v1" &&
    (← decode String (← field packet "source_sha256")) == LAlanine40K2025.Reentry.SourceParsing.sourceArtifactSha256 &&
    (← decode Nat (← field packet "gamma_scale")) == 1000000000000000 &&
    (← decode Nat (← field packet "factor_scale")) == 1000000000000 &&
    (← decode Nat (← field packet "basis_count")) == 98 &&
    (← decode Nat (← field packet "column_count")) == 24 do
      throwError "occupation factor source identity"
  let real ← decode (Array (Array Int)) (← field packet "real_rows")
  let imag ← decode (Array (Array Int)) (← field packet "imag_rows")
  unless real.size == 98 && imag.size == 98 &&
    real.all (fun row => row.size == 24) && imag.all (fun row => row.size == 24) do
      throwError "occupation factor dimensions"
  pure (real,imag,sourceElectronCount,densityInterpretation)

elab "generateOccupationFactor" : command => liftTermElabM do
  let (real,imag,sourceElectronCount,densityInterpretation) ← verifiedPacket
  declareReadout `realRows (toExpr real)
  declareReadout `imagRows (toExpr imag)
  declareReadout `sourceElectronCount (toExpr sourceElectronCount)
  declareReadout `densityInterpretation (toExpr densityInterpretation)

generateOccupationFactor

end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Reification

namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped Matrix

noncomputable def realNumerator : Matrix Basis OccupiedSlot Int :=
  fun i j => (Reification.realRows[i.val]!)[j.val]!
noncomputable def imagNumerator : Matrix Basis OccupiedSlot Int :=
  fun i j => (Reification.imagRows[i.val]!)[j.val]!

theorem source_electron_count : Reification.sourceElectronCount =
    2 * Fintype.card OccupiedSlot := by decide

end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
