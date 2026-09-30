import H0mework.Versions.X.Fock.CopyGraph.RecordedRecurrenceObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureAcquisition

open SourceCopyProgram (Index indexAfter scale)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff hidden)
open SourceGeneratedAcquisitionContinuation SourceSuccessorBoundary
open SourceOwnedObservationHistory.SourceShift (basis)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical InnerProductSpace
noncomputable section

def arrival (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier :=
  time (scale (inventoryBound runtime) index - 1) (hidden runtime index steps)

theorem acquired_coordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    hilbert (arrival runtime index steps)
      (indexAfter (inventoryBound runtime) index (inventoryBound runtime + steps + 1)) = 1 := by
  have address : indexAfter (inventoryBound runtime) index (inventoryBound runtime + steps + 1) =
      cutoff runtime index steps + 1 + (scale (inventoryBound runtime) index - 1) := by
    rw [SourceCopyTimeModel.index_successor]
    change cutoff runtime index steps + scale (inventoryBound runtime) index = _
    have positive := SourceCopyProgram.scale_pos (inventoryBound runtime) index
    omega
  rw [address]
  exact (SourceCopyTimeModel.time_hilbert_add (scale (inventoryBound runtime) index - 1)
    (hidden runtime index steps) (cutoff runtime index steps + 1)).trans
      (SourceCopyRecordedRecurrence.hidden_coordinate runtime index steps)

theorem arrival_mass (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    mass (arrival runtime index steps) = 0 := by
  rw [arrival, SourceCopyRecordedRecurrence.hidden, SourceCopyRecordedRecurrence.difference_time,
    SourceCopyRecordedRecurrence.difference_mass]

theorem arrival_clock (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.clock (arrival runtime index steps) = 0 := by
  rw [arrival, SourceCopyRecordedRecurrence.hidden, SourceCopyRecordedRecurrence.difference_time,
    SourceCopyRecordedRecurrence.difference_clock]

theorem acquired_pairing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1),
      arrival runtime index steps⟫_ℂ = 1 := by
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change (⟪hilbert (SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1)),
      hilbert (arrival runtime index steps)⟫_ℂ +
    ⟪mass (SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1)),
      mass (arrival runtime index steps)⟫_ℂ) +
    ⟪SourceJointClockGraph.clock (SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1)),
      SourceJointClockGraph.clock (arrival runtime index steps)⟫_ℂ = 1
  rw [arrival_mass, arrival_clock, inner_zero_right, inner_zero_right, add_zero, add_zero]
  change ⟪SourceCopyGraph.hilbertAction (inventoryBound runtime) index
      (readWord (Finsupp.single (inventoryBound runtime + steps + 1) (1 : ℂ))), hilbert (arrival runtime index steps)⟫_ℂ = 1
  rw [readWord_single, one_smul, SourceCopyGraph.hilbert_basis]
  simp only [basis, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, acquired_coordinate]

end
end SourceCopyFutureAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
