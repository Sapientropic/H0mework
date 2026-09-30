import H0mework.Fock.ReceivedStep.EncodingPairing

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

def timeCoordinate (bound stride : Nat)
    (data : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) (phase position : Nat) : ℚ :=
  if phase ≤ position then coordinateAt bound stride data (position - phase) else 0

def timeResponse (bound stride : Nat)
    (data : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) (phase : Nat) (actor : Fin (bound + 1)) : ℚ :=
  timeCoordinate bound stride data phase ((actor.val + 1) * (stride + 1) - 1) + data.2.1 +
    (((actor.val + 1) * (stride + 1) : Nat) : ℚ) * (data.2.2 + (phase : ℚ) * data.2.1)

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem time_coordinate_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (data : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) (phase position : Nat) :
    (timeCoordinate (inventoryBound runtime + steps) index.val data phase position : ℂ) =
      SourceCopyTimeModel.hilbert (SourceCopyTimeModel.time phase (completeValue runtime index steps data)) position := by
  by_cases included : phase ≤ position
  · rw [timeCoordinate, if_pos included, coordinate_source]
    have actual := SourceCopyTimeModel.time_hilbert_add phase (completeValue runtime index steps data) (position - phase)
    rw [Nat.sub_add_cancel included] at actual
    exact actual.symm
  · rw [timeCoordinate, if_neg included, Rat.cast_zero]
    exact (SourceCopyTimeModel.time_hilbert_before phase (completeValue runtime index steps data) position (by omega)).symm

theorem time_response_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (data : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ)
    (phase : Nat) (actor : Fin (inventoryBound runtime + steps + 1)) :
    (timeResponse (inventoryBound runtime + steps) index.val data phase actor : ℂ) =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
        SourceCopyTimeModel.time phase (completeValue runtime index steps data)⟫_ℂ := by
  rw [SourceCopyCurrentCoordinates.column_pairing, SourceCopyTimeModel.time_mass, SourceCopyTimeModel.time_clock]
  simp only [timeResponse, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, time_coordinate_source,
    SourceCopyProgram.index_source, SourceCopyProgram.scale_source]
  rfl

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
