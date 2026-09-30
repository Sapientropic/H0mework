import H0mework.Versions.X.Fock.RationalWindow.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

def coordinateAt (bound stride : Nat)
    (data : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) (position : Nat) : ℚ :=
  if included : position < (bound + 1) * (stride + 1) then data.1 ⟨position, included⟩ else 0

def completeResponse (bound stride : Nat)
    (data : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) (actor : Fin (bound + 1)) : ℚ :=
  coordinateAt bound stride data ((actor.val + 1) * (stride + 1) - 1) + data.2.1 +
    (((actor.val + 1) * (stride + 1) : Nat) : ℚ) * data.2.2

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def completeValue (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (data : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) : SourceJointClockGraph.Carrier :=
  SourceCopyCurrentCoordinates.realize runtime index steps (SourceRationalWindowReadout.coordinates runtime index steps data)

theorem coordinate_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (data : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) (position : Nat) :
    (coordinateAt (inventoryBound runtime + steps) index.val data position : ℂ) =
      SourceCopyTimeModel.hilbert (completeValue runtime index steps data) position := by
  have bound : cutoff runtime index steps + 1 = (inventoryBound runtime + steps + 1) * (index.val + 1) :=
    (SourceCopyProgram.index_exact (inventoryBound runtime) index (inventoryBound runtime + steps)).trans
      (by rw [SourceCopyProgram.scale_source])
  by_cases included : position < (inventoryBound runtime + steps + 1) * (index.val + 1)
  · rw [coordinateAt, dif_pos included]
    let coordinate : Fin (cutoff runtime index steps + 1) := ⟨position, included.trans_eq bound.symm⟩
    have actual := SourceCopyCurrentCoordinates.hilbert_lift_at runtime index steps
      (SourceRationalWindowReadout.coordinates runtime index steps data).1 coordinate
    exact actual.symm
  · rw [coordinateAt, dif_neg included, Rat.cast_zero]
    exact (SourceCopyCurrentCoordinates.hilbert_lift_outside runtime index steps
      (SourceRationalWindowReadout.coordinates runtime index steps data).1 position (by omega)).symm

theorem complete_response_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (data : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ)
    (actor : Fin (inventoryBound runtime + steps + 1)) :
    (completeResponse (inventoryBound runtime + steps) index.val data actor : ℂ) =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, completeValue runtime index steps data⟫_ℂ := by
  rw [SourceCopyCurrentCoordinates.column_pairing]
  simp only [completeResponse, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, coordinate_source,
    SourceCopyProgram.index_source, SourceCopyProgram.scale_source]
  rfl

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
