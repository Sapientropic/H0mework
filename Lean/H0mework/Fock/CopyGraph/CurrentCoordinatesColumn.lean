import H0mework.Fock.CopyGraph.CurrentCoordinatesSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index indexAfter)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation SourceSuccessorBoundary
open SourceOwnedObservationHistory.SourceShift (basis)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem column_pairing (depth : Nat) (index : Index depth) (actor : Nat) (target : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column depth index actor, target⟫_ℂ =
      hilbert target (indexAfter depth index actor) + mass target +
        ((indexAfter depth index actor + 1 : Nat) : ℂ) * SourceJointClockGraph.clock target := by
  rw [SourceColumnForcing.column, SourceCopyGraph.action_source, SourceCopyGraph.complex_single,
    SourceJointClockGraph.read_apply, SourceMassCompletion.jointRead_apply,
    WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change (⟪readWord (Finsupp.single (indexAfter depth index actor) (1 : ℂ)), hilbert target⟫_ℂ +
    ⟪SourceSuccessorBoundary.mass ℂ (Finsupp.single (indexAfter depth index actor) (1 : ℂ)), mass target⟫_ℂ) +
    ⟪SourceClockComplex.clock (Finsupp.single (indexAfter depth index actor) (1 : ℂ)), SourceJointClockGraph.clock target⟫_ℂ = _
  rw [readWord_single, one_smul, mass_single, SourceClockComplex.clock_single, one_mul]
  simp only [basis, lp.inner_single_left, RCLike.inner_apply, SourceClockModel.rawClock,
    Int.cast_add, Int.cast_natCast, Int.cast_one, map_add, map_natCast, map_one, mul_one, Nat.cast_add, Nat.cast_one]
  ring

theorem tail_pairing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat)
    (beyond : cutoff runtime index steps < ticks) (target : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps), time ticks target⟫_ℂ =
      mass target + ((cutoff runtime index steps + 1 : Nat) : ℂ) *
        (SourceJointClockGraph.clock target + (ticks : ℂ) * mass target) := by
  rw [column_pairing]
  change hilbert (time ticks target) (cutoff runtime index steps) + mass (time ticks target) + _ = _
  rw [SourceCopyTimeModel.time_hilbert_before _ _ _ beyond, SourceCopyTimeModel.time_mass,
    SourceCopyTimeModel.time_clock, zero_add]
  rfl

theorem tail_difference (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps),
      time (cutoff runtime index steps + 2) target⟫_ℂ -
    ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps),
      time (cutoff runtime index steps + 1) target⟫_ℂ =
        ((cutoff runtime index steps + 1 : Nat) : ℂ) * mass target := by
  rw [tail_pairing _ _ _ _ (by omega), tail_pairing _ _ _ _ (by omega)]
  push_cast
  ring

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
