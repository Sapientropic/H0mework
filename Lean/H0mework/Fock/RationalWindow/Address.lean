import H0mework.Fock.RationalWindow.Moments

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRationalWindowReadout

def second (bound : Nat) : Fin (bound + 1) := ⟨min 1 bound, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def actorAt (bound stride : Nat) (coordinate : Fin ((bound + 1) * (stride + 1))) : Fin (bound + 1) :=
  ⟨coordinate.val / (stride + 1), (Nat.div_lt_iff_lt_mul (Nat.succ_pos stride)).mpr coordinate.isLt⟩

open Fin.NatCast

def phaseAt (stride coordinate : Nat) : Fin (stride + 1) := -(↑(coordinate + 1) : Fin (stride + 1))

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem second_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    second (inventoryBound runtime + steps) = SourceOperatorObservationAcquisition.secondColumn runtime index nonunit steps := by
  apply Fin.ext
  have included := (SourceOperatorObservationAcquisition.secondColumn runtime index nonunit steps).isLt
  change 1 < inventoryBound runtime + steps + 1 at included
  change min 1 (inventoryBound runtime + steps) = 1
  omega

def address (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index steps + 1)) : Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) :=
  ⟨coordinate.val, coordinate.isLt.trans_eq (by
    exact (SourceCopyProgram.index_exact (inventoryBound runtime) index (inventoryBound runtime + steps)).trans
      (by rw [SourceCopyProgram.scale_source]))⟩

theorem actor_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index steps + 1)) :
    actorAt (inventoryBound runtime + steps) index.val (address runtime index steps coordinate) =
      SourceCopySharedNext.columnAt runtime index steps coordinate := rfl

theorem phase_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (coordinate : Nat) :
    phaseAt index.val coordinate = SourceCopyTimeModel.phaseAt (inventoryBound runtime) index coordinate := rfl

end
end SourceRationalWindowReadout
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
