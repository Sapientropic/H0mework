import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedThermalInputs
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Source.SourceBoundLAlanine40KNativeDurationFrame

/-!
# Numerical receipt of the registered collision

Only the exact setup is identified with the analytic producer here. The full
quantized matrix rows remain recorded readouts, with their independent residuals.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Source

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Preparation

def thermalArtifactSha256 : String :=
  "bf3274c886bc4aa781c51e2c00807a14127af28623e9c385226f932c8e13a5ee"

private def artifactText : String :=
  include_str "../../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/lalanine40k-target-erased-quantum-bond-density/thermal/source/lalanine40k-partial-swap-thermal-collision.json"

private def atKey (value : Lean.Json) (key : String) : Lean.Elab.TermElabM Lean.Json :=
  match value.getObjVal? key with
  | .ok result => pure result
  | .error error => throwError "Thermal occurrence {key}: {error}"

private def decode (α : Type) [Lean.FromJson α] (value : Lean.Json) : Lean.Elab.TermElabM α :=
  match Lean.fromJson? value with
  | .ok result => pure result
  | .error error => throwError "Thermal occurrence decoder: {error}"

structure RecordedThermalOccurrence where
  currentNumerator : Nat
  currentDenominator : Nat
  betaNumerator : Nat
  betaDenominator : Nat
  cosineNumerator : Nat
  cosineDenominator : Nat
  sineNumerator : Nat
  sineDenominator : Nat
  matrixRows : Array (Array Int)

def RecordedThermalOccurrence.currentTime (recorded : RecordedThermalOccurrence) : ℚ :=
  (recorded.currentNumerator : ℚ) / recorded.currentDenominator

elab "lalanineThermalOccurrence%" : term => do
  unless Sha256.hex artifactText == thermalArtifactSha256 do
    throwError "Thermal occurrence changed"
  let value ← match Lean.Json.parse artifactText with
    | .ok parsed => pure parsed
    | .error error => throwError "Thermal occurrence JSON: {error}"
  let join ← atKey value "source_join"
  let parent ← decode String (← atKey join "native_frame_sha256")
  unless parent == Propagation.Source.nativeFrameArtifactSha256 do
    throwError "Thermal occurrence is not the same native current"
  let current ← atKey join "current_clock"
  let currentNumerator ← decode Nat (← atKey current "numerator")
  let currentDenominator ← decode Nat (← atKey current "denominator")
  let collision ← atKey value "collision"
  let dimension ← decode Nat (← atKey collision "dimension")
  unless dimension == 98 do throwError "Thermal basis incidence changed"
  let beta ← atKey (← atKey collision "bath") "beta"
  let betaNumerator ← decode Nat (← atKey beta "numerator")
  let betaDenominator ← decode Nat (← atKey beta "denominator")
  let joint ← atKey collision "joint"
  let cosine ← atKey joint "cosine"
  let sine ← atKey joint "sine"
  let cosineNumerator ← decode Nat (← atKey cosine "numerator")
  let cosineDenominator ← decode Nat (← atKey cosine "denominator")
  let sineNumerator ← decode Nat (← atKey sine "numerator")
  let sineDenominator ← decode Nat (← atKey sine "denominator")
  let columns ← decode (Array String) (← atKey collision "matrix_columns")
  unless columns == #["left_basis", "right_basis", "current_amplitude_real", "current_amplitude_imaginary",
      "prepared_system_real", "prepared_system_imaginary", "gibbs_bath_real", "gibbs_bath_imaginary",
      "system_after_real", "system_after_imaginary", "bath_after_real", "bath_after_imaginary"] do
    throwError "Thermal matrix readout semantics changed"
  let rows ← decode (Array (Array Int)) (← atKey collision "matrix_rows")
  unless rows.size == 4851 && rows.all (fun row => row.size == 12) do
    throwError "Thermal readout lacks the complete registered carrier"
  let mut index : Nat := 0
  for left in [:98] do
    for right in [left:98] do
      unless (rows[index]!)[0]! == Int.ofNat left && (rows[index]!)[1]! == Int.ofNat right do
        throwError "Thermal matrix row {index} changed occurrence address"
      index := index + 1
  Lean.Meta.mkAppM ``RecordedThermalOccurrence.mk #[Lean.toExpr currentNumerator,
    Lean.toExpr currentDenominator, Lean.toExpr betaNumerator, Lean.toExpr betaDenominator,
    Lean.toExpr cosineNumerator, Lean.toExpr cosineDenominator, Lean.toExpr sineNumerator,
    Lean.toExpr sineDenominator, Lean.toExpr rows]

noncomputable def recordedThermalOccurrence : RecordedThermalOccurrence := lalanineThermalOccurrence%

theorem recordedThermalCurrent_commutes : recordedThermalOccurrence.currentTime = collisionCurrentTime := by
  rw [collisionCurrentTime_exact]
  rfl

theorem recordedThermalParameters_commute :
    (recordedThermalOccurrence.betaNumerator : ℝ) / recordedThermalOccurrence.betaDenominator = inverseTemperature ∧
    (recordedThermalOccurrence.cosineNumerator : ℝ) / recordedThermalOccurrence.cosineDenominator = exchangeCosine ∧
    (recordedThermalOccurrence.sineNumerator : ℝ) / recordedThermalOccurrence.sineDenominator = exchangeSine := by
  rw [show recordedThermalOccurrence.betaNumerator = 1 from rfl,
    show recordedThermalOccurrence.betaDenominator = 1 from rfl,
    show recordedThermalOccurrence.cosineNumerator = 3 from rfl,
    show recordedThermalOccurrence.cosineDenominator = 5 from rfl,
    show recordedThermalOccurrence.sineNumerator = 4 from rfl,
    show recordedThermalOccurrence.sineDenominator = 5 from rfl]
  norm_num [inverseTemperature, exchangeCosine, exchangeSine]

end LAlanine40K2025.Thermal.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
