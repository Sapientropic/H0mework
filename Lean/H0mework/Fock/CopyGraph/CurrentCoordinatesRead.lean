import H0mework.Fock.CopyGraph.CurrentCoordinatesWindow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff windowBound)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def coordinatePhase (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index steps + 1)) : Fin (windowBound runtime index steps + 1) :=
  ⟨cutoff runtime index steps - coordinate.val, by unfold windowBound; omega⟩

def hilbertRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index steps + 1)) : Window runtime index steps →ₗ[ℂ] ℂ :=
  response runtime index steps (coordinatePhase runtime index steps coordinate) - massRead runtime index steps -
    ((cutoff runtime index steps + 1 : Nat) : ℂ) •
      (clockRead runtime index steps + ((coordinatePhase runtime index steps coordinate).val : ℂ) • massRead runtime index steps)

theorem hilbert_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index steps + 1)) (target : SourceJointClockGraph.Carrier) :
    hilbertRead runtime index steps coordinate
        (recordedPrefix runtime index steps (windowBound runtime index steps) target) = hilbert target coordinate.val := by
  have address : coordinate.val + (coordinatePhase runtime index steps coordinate).val = cutoff runtime index steps := by
    change coordinate.val + (cutoff runtime index steps - coordinate.val) = cutoff runtime index steps
    omega
  have moved := SourceCopyTimeModel.time_hilbert_add (coordinatePhase runtime index steps coordinate).val target coordinate.val
  rw [address] at moved
  simp only [hilbertRead, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
    response_source, mass_source, clock_source, smul_eq_mul]
  rw [column_pairing, SourceCopyTimeModel.time_mass, SourceCopyTimeModel.time_clock]
  change hilbert (time (coordinatePhase runtime index steps coordinate).val target) (cutoff runtime index steps) +
    mass target + ((cutoff runtime index steps + 1 : Nat) : ℂ) *
      (SourceJointClockGraph.clock target + ((coordinatePhase runtime index steps coordinate).val : ℂ) * mass target) -
    mass target - ((cutoff runtime index steps + 1 : Nat) : ℂ) *
      (SourceJointClockGraph.clock target + ((coordinatePhase runtime index steps coordinate).val : ℂ) * mass target) = _
  rw [moved]
  ring

abbrev Coordinates (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :=
  (Fin (cutoff runtime index steps + 1) → ℂ) × ℂ × ℂ

def decode (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Window runtime index steps →ₗ[ℂ] Coordinates runtime index steps :=
  (LinearMap.pi (hilbertRead runtime index steps)).prod ((massRead runtime index steps).prod (clockRead runtime index steps))

def sourceRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] Coordinates runtime index steps where
  toFun target := (fun coordinate => hilbert target coordinate.val, mass target, SourceJointClockGraph.clock target)
  map_add' left right := by
    ext coordinate <;> simp [hilbert, mass, map_add]
  map_smul' scalar target := by
    ext coordinate <;> simp [hilbert, mass, map_smul]

theorem decode_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    decode runtime index steps (recordedPrefix runtime index steps (windowBound runtime index steps) target) =
      sourceRead runtime index steps target := by
  apply Prod.ext
  · funext coordinate
    exact hilbert_source runtime index steps coordinate target
  · exact Prod.ext (mass_source runtime index steps target) (clock_source runtime index steps target)

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
