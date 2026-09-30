import H0mework.Fock.CopyFiniteComplete.Next

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteCompleteGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedJointClockGraph SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] windowMeasurable

theorem original_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : FieldSpace (inventoryBound runtime) (inventoryBound runtime)) :
    let depth := inventoryBound runtime
    let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
    let remaining := value - recovery runtime index target
    ‖residual runtime index target‖ ^ 2 =
      ‖remaining‖ ^ 2 + (depth + 1 : ℝ) *
        ‖∫ actor, Actor.currentPullback depth depth remaining actor ∂(historyPMF depth).toMeasure‖ ^ 2 +
      (SourceCopyProgram.scale depth index : ℝ) ^ 2 * ‖SourceClockComplex.clock (word depth depth remaining)‖ ^ 2 := by
  dsimp only
  rw [residual, ← map_sub, ← map_sub]
  exact SourceCopyGraph.original_copy_energy _ _ index _

theorem recovery_realization (round : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    let depth := inventoryBound runtime
    let copied := SourceCopyGraph.complexAction depth index (word depth depth (recovery runtime index target))
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (inventoryBound (sourceRound round copied)) (realizeWord round copied) + residual runtime index target = target := by
  dsimp only
  rw [SourceCopyGraph.original_copy_realization]
  exact reconstruction runtime index target

theorem residual_realization (round : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : FieldSpace (inventoryBound runtime) (inventoryBound runtime)) :
    let depth := inventoryBound runtime
    let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
    let remaining := value - recovery runtime index target
    let copied := SourceCopyGraph.complexAction depth index (word depth depth remaining)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (inventoryBound (sourceRound round copied)) (realizeWord round copied) = residual runtime index target := by
  dsimp only
  refine (SourceCopyGraph.original_copy_realization round _ _ _ _).trans ?_
  rw [map_sub, map_sub]
  rfl

theorem recovery_full_record (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    ∀ actor : Fin (inventoryBound runtime + 1),
      type_of% (SourceGeneratedConditionalInventory.full_record_read runtime (inventoryBound runtime)
        (Actor.currentPullback (inventoryBound runtime) (inventoryBound runtime) (recovery runtime index target)) actor) :=
  SourceGeneratedConditionalInventory.full_record_read runtime _ _

end
end SourceFiniteCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
