import H0mework.Fock.SourceHistory.CountedObservation.Table

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedPosterior

variable {Key : Type*} [DecidableEq Key]

def restore (bound stride : Nat) (nonunit : stride ≠ 0)
    (table : SourceCountedObservation.Table Key) (key : Key) : Nat × (Fin (bound + 1) → ℚ) :=
  let entry := SourceCountedObservation.lookup table key
  SourceFibreExactState.restore bound stride nonunit
    (SourceReceivedConditionalStep.completeSamples bound stride
      ((fun position => SourceCountedObservation.coordinate entry.hilbert position.val / (bound + 1 : Nat)),
        entry.mass / (bound + 1 : Nat), entry.clock / (bound + 1 : Nat)))

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

theorem support_coordinates (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (table : SourceCountedObservation.Table Key) (key : Key) :
    let entry := SourceCountedObservation.lookup table key
    SourceStableReceivedCount.support (inventoryBound runtime) index.val nonunit
      (SourceReceivedConditionalStep.completeSamples (inventoryBound runtime) index.val
        ((fun position => SourceCountedObservation.coordinate entry.hilbert position.val / (inventoryBound runtime + 1 : Nat)),
          entry.mass / (inventoryBound runtime + 1 : Nat), entry.clock / (inventoryBound runtime + 1 : Nat))) =
      Finset.univ.filter (fun actor : Fin (inventoryBound runtime + 1) =>
        (1 / 2 : ℚ) < SourceCountedObservation.coordinate entry.hilbert (actor.val + 1)) := by
  dsimp only
  let data : SourceRetainedReceiver.Raw (inventoryBound runtime) index.val :=
    ((fun position => SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert position.val /
      (inventoryBound runtime + 1 : Nat)),
      (SourceCountedObservation.lookup table key).mass / (inventoryBound runtime + 1 : Nat),
      (SourceCountedObservation.lookup table key).clock / (inventoryBound runtime + 1 : Nat))
  have decoded : SourceRationalWindowReadout.decode (inventoryBound runtime) index.val
      (SourceReceivedConditionalStep.completeSamples (inventoryBound runtime) index.val data) = data :=
    SourceReceivedConditionalStep.complete_roundtrip runtime index nonunit 0 data
  have recovered (actor : Fin (inventoryBound runtime + 1)) :
      SourceRationalWindowReadout.recover (inventoryBound runtime) index.val nonunit
        (SourceReceivedConditionalStep.completeSamples (inventoryBound runtime) index.val data) actor =
      SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert (actor.val + 1) /
        (inventoryBound runtime + 1 : Nat) :=
    congrArg (fun raw : SourceRetainedReceiver.Raw (inventoryBound runtime) index.val =>
      raw.1 (SourceRationalWindowReadout.weightAddress (inventoryBound runtime) index.val nonunit actor)) decoded
  rw [SourceStableReceivedCount.support]
  apply Finset.filter_congr
  intro actor _
  rw [show SourceRationalWindowReadout.recover (inventoryBound runtime) index.val nonunit
      (SourceReceivedConditionalStep.completeSamples (inventoryBound runtime) index.val
        ((fun position => SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert position.val /
          (inventoryBound runtime + 1 : Nat)),
          (SourceCountedObservation.lookup table key).mass / (inventoryBound runtime + 1 : Nat),
          (SourceCountedObservation.lookup table key).clock / (inventoryBound runtime + 1 : Nat))) actor = _
      from recovered actor]
  change 1 / (2 * ((inventoryBound runtime + 1 : Nat) : ℚ)) <
      SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert (actor.val + 1) /
        ((inventoryBound runtime + 1 : Nat) : ℚ) ↔ _
  have positive : (0 : ℚ) < ((inventoryBound runtime + 1 : Nat) : ℚ) := by positivity
  rw [lt_div_iff₀ positive]
  have cancelled :
      1 / (2 * ((inventoryBound runtime + 1 : Nat) : ℚ)) * ((inventoryBound runtime + 1 : Nat) : ℚ) =
        (1 / 2 : ℚ) := by
    field_simp
  rw [cancelled]

theorem restore_formula (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (table : SourceCountedObservation.Table Key) (key : Key) :
    let retained := Finset.univ.filter (fun actor : Fin (inventoryBound runtime + 1) =>
      (1 / 2 : ℚ) < SourceCountedObservation.coordinate (SourceCountedObservation.lookup table key).hilbert (actor.val + 1))
    restore (inventoryBound runtime) index.val nonunit table key =
      (retained.card, fun actor => if actor ∈ retained then (retained.card : ℚ)⁻¹ else 0) := by
  simp only [restore, SourceFibreExactState.restore, support_coordinates runtime index nonunit table key]

end SourceCountedPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
