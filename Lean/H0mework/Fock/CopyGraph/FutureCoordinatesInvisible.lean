import H0mework.Fock.CopyGraph.FutureCoordinatesRead
import H0mework.Fock.CopyGraph.CurrentCoordinatesInvisible

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index indexAfter)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceSuccessorBoundary
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem column_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (invisible : sourceRead runtime index steps target = 0)
    (actor : Fin (inventoryBound runtime + steps + 1 + 1)) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, target⟫_ℂ = 0 :=
  SourceCopyCurrentCoordinates.column_zero runtime index (steps + 1) target invisible actor

theorem image_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (invisible : sourceRead runtime index steps target = 0)
    (source : SourceJointFiniteDecoder.Space (inventoryBound runtime + steps + 1)) :
    ⟪SourceCopyGraph.action (inventoryBound runtime) index
      (SourceJointFiniteDecoder.read (inventoryBound runtime + steps + 1) source), target⟫_ℂ = 0 :=
  SourceCopyCurrentCoordinates.image_zero runtime index (steps + 1) target invisible source

theorem observer_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (invisible : sourceRead runtime index steps target = 0) :
    observer runtime index (steps + 1) target = 0 :=
  SourceCopyCurrentCoordinates.observer_zero runtime index (steps + 1) target invisible

theorem source_zero_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (invisible : sourceRead runtime index steps target = 0) :
    sourceRead runtime index steps (SourceJointClockGraph.action target) = 0 :=
  SourceCopyCurrentCoordinates.source_zero_next runtime index (steps + 1) target invisible


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
