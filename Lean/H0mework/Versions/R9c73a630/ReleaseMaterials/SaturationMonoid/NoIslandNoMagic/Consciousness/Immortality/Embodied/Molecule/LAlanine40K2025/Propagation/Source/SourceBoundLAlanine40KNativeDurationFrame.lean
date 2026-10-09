import H0mework.Chemistry.LAlaninePropagation.GeneratedNativeClock

/-! # Recorded numerical frame indexed by the independently generated native clock -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Source

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Producer

def nativeFrameArtifactSha256 : String :=
  "96eebce2da4e4ec94c00d747b428131a333b41852ee563c2b9909950f960b1f8"

private def frameText : String :=
  include_str "../../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/lalanine40k-target-erased-quantum-bond-density/propagation/source/native-duration-frame.json"

private def valueAt (value : Lean.Json) (key : String) : Lean.Elab.TermElabM Lean.Json :=
  match value.getObjVal? key with
  | .ok result => pure result
  | .error error => throwError "Native frame field {key}: {error}"

private def fromValue (α : Type) [Lean.FromJson α] (value : Lean.Json) : Lean.Elab.TermElabM α :=
  match Lean.fromJson? value with
  | .ok result => pure result
  | .error error => throwError "Native frame decoder: {error}"

structure RecordedNativeFrame where
  durationNumerator : Nat
  durationDenominator : Nat
  nextTimeNumerator : Nat
  nextTimeDenominator : Nat
  rows : Array (Array Int)

def RecordedNativeFrame.duration (frame : RecordedNativeFrame) : ℚ :=
  (frame.durationNumerator : ℚ) / frame.durationDenominator

def RecordedNativeFrame.nextTime (frame : RecordedNativeFrame) : ℚ :=
  (frame.nextTimeNumerator : ℚ) / frame.nextTimeDenominator

elab "lalanineNativeFrame%" : term => do
  unless Sha256.hex frameText == nativeFrameArtifactSha256 do
    throwError "Native frame source SHA-256 changed"
  let value ← match Lean.Json.parse frameText with
    | .ok result => pure result
    | .error error => throwError "Native frame JSON: {error}"
  let join ← valueAt value "parent_join"
  let parent ← fromValue String (← valueAt join "parent_sha256")
  unless parent == sourceArtifactSha256 do
    throwError "Native frame belongs to another electronic source"
  let clock ← valueAt value "clock"
  let current ← valueAt clock "current_time"
  let currentNumerator ← fromValue Nat (← valueAt current "numerator")
  let currentDenominator ← fromValue Nat (← valueAt current "denominator")
  unless currentNumerator == 1 && currentDenominator == 1 do
    throwError "Native frame starts from another current"
  let duration ← valueAt clock "duration"
  let durationNumerator ← fromValue Nat (← valueAt duration "numerator")
  let durationDenominator ← fromValue Nat (← valueAt duration "denominator")
  let next ← valueAt clock "next_time"
  let nextNumerator ← fromValue Nat (← valueAt next "numerator")
  let nextDenominator ← fromValue Nat (← valueAt next "denominator")
  let frame ← valueAt value "frame"
  let columns ← fromValue (Array String) (← valueAt frame "columns")
  unless columns == #["left_basis", "right_basis", "propagator_real_pico",
      "propagator_imaginary_pico", "density_real_pico", "density_imaginary_pico"] do
    throwError "Native frame row semantics changed"
  let rows ← fromValue (Array (Array Int)) (← valueAt frame "rows")
  unless rows.size == 4851 && rows.all (fun row => row.size == 6) do
    throwError "Native frame lost complete upper-triangle incidence"
  let mut index : Nat := 0
  for left in [:98] do
    for right in [left:98] do
      unless (rows[index]!)[0]! == Int.ofNat left && (rows[index]!)[1]! == Int.ofNat right do
        throwError "Native frame row {index} changed address"
      index := index + 1
  Lean.Meta.mkAppM ``RecordedNativeFrame.mk #[Lean.toExpr durationNumerator,
    Lean.toExpr durationDenominator, Lean.toExpr nextNumerator, Lean.toExpr nextDenominator,
    Lean.toExpr rows]

noncomputable def recordedNativeFrame : RecordedNativeFrame := lalanineNativeFrame%

theorem recordedDuration_eq_nativeClock : recordedNativeFrame.duration = nativeClockStep := by
  rw [nativeClockStep_exact]
  rfl

theorem recordedNextTime_eq_generated :
    recordedNativeFrame.nextTime = (1 : ℚ) + nativeClockStep := by
  rw [firstNativeClockTarget_exact]
  rfl

theorem recordedDuration_positive : 0 < recordedNativeFrame.duration := by
  rw [recordedDuration_eq_nativeClock]
  exact nativeClockStep_positive

end LAlanine40K2025.Propagation.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
