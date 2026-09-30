import H0mework.Versions.X.Fock.RationalWindow.Address

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRationalWindowReadout

def hilbert (bound stride : Nat) (samples : Samples bound (stride + 1))
    (coordinate : Fin ((bound + 1) * (stride + 1))) : ℚ :=
  let actor := actorAt bound stride coordinate
  let phase := phaseAt stride coordinate.val
  column bound (stride + 1) samples actor phase.castSucc - mass bound (stride + 1) (second bound) samples -
    (((actor.val + 1) * (stride + 1) : Nat) : ℚ) *
      (clock bound (stride + 1) (second bound) samples + (phase.val : ℚ) * mass bound (stride + 1) (second bound) samples)

def decode (bound stride : Nat) (samples : Samples bound (stride + 1)) :
    (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ :=
  (hilbert bound stride samples, mass bound (stride + 1) (second bound) samples,
    clock bound (stride + 1) (second bound) samples)

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem hilbert_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Samples (inventoryBound runtime + steps) (index.val + 1))
    (coordinate : Fin (cutoff runtime index steps + 1)) :
    (hilbert (inventoryBound runtime + steps) index.val samples (address runtime index steps coordinate) : ℂ) =
      SourceOperatorObservationAcquisition.hilbertRead runtime index nonunit steps coordinate (embed runtime index steps samples) := by
  simp only [hilbert, actor_source, show (address runtime index steps coordinate).val = coordinate.val from rfl,
    phase_source, second_source runtime index nonunit steps, Rat.cast_sub, Rat.cast_mul, Rat.cast_add,
    Rat.cast_natCast, column_source, mass_source, clock_source]
  simp only [SourceOperatorObservationAcquisition.hilbertRead, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul, SourceCopyProgram.index_exact, SourceCopyProgram.scale_source]

def coordinates (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) :
    SourceCopyCurrentCoordinates.Coordinates runtime index steps :=
  (fun coordinate => (value.1 (address runtime index steps coordinate) : ℂ), (value.2.1 : ℂ), (value.2.2 : ℂ))

theorem decode_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Samples (inventoryBound runtime + steps) (index.val + 1)) :
    coordinates runtime index steps (decode (inventoryBound runtime + steps) index.val samples) =
      SourceOperatorObservationAcquisition.decode runtime index nonunit steps (embed runtime index steps samples) := by
  apply Prod.ext
  · funext coordinate
    exact hilbert_source runtime index nonunit steps samples coordinate
  · apply Prod.ext
    · change (mass _ _ (second _) samples : ℂ) = _
      rw [second_source runtime index nonunit steps]
      exact mass_source runtime index nonunit steps samples
    · change (clock _ _ (second _) samples : ℂ) = _
      rw [second_source runtime index nonunit steps]
      exact clock_source runtime index nonunit steps samples

end
end SourceRationalWindowReadout
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
