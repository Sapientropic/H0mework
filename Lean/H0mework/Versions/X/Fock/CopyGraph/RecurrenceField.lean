import H0mework.Versions.X.Fock.CopyGraph.RecurrenceEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRecurrence

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedAcquisitionContinuation
open SourceGeneratedJointClockGraph SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead sourceRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance fieldRecurrenceMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem original_minimum (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    let depth := inventoryBound runtime + steps
    let read := oldRead depth (sourceRead (inventoryBound runtime) index)
    let retained := SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps
    recovery runtime index steps value ∈ Set.range (SourceConditionalGraphDecoder.realizeObserved depth depth read) ∧
      IsMinOn (fun proposal : FieldSpace depth depth =>
        ‖value - SourceCopyGraph.action depth retained (fieldRead depth depth proposal)‖ ^ 2)
        (Set.range (SourceConditionalGraphDecoder.realizeObserved depth depth read)) (recovery runtime index steps value) := by
  rw [recovery_canonical]
  exact SourceConditionalGraphDecoder.original_minimum _ _ _ _ value

theorem original_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    let depth := inventoryBound runtime + steps
    let retained := SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps
    let target := SourceCopyGraph.action depth retained (fieldRead depth depth value)
    let remaining := value - recovery runtime index steps target
    ‖residual runtime index steps target‖ ^ 2 =
      ‖remaining‖ ^ 2 + (depth + 1 : ℝ) *
        ‖∫ actor, Actor.currentPullback depth depth remaining actor ∂(historyPMF depth).toMeasure‖ ^ 2 +
      (SourceCopyProgram.scale depth retained : ℝ) ^ 2 * ‖SourceClockComplex.clock (word depth depth remaining)‖ ^ 2 := by
  dsimp only
  rw [residual_canonical, recovery_canonical]
  with_reducible exact SourceConditionalGraphDecoder.original_residual_energy _ _ _ _ value

theorem recovery_zero_iff (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : Space (historyPMF (inventoryBound runtime + steps))) :
    let depth := inventoryBound runtime + steps
    residual runtime index steps (SourceConditionalGraph.copyRead depth depth
      (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps) value) = 0 ↔
        SourceWeightedRecovery.residual (historyPMF depth)
          (oldRead depth (sourceRead (inventoryBound runtime) index)) value = 0 := by
  dsimp only
  rw [residual_canonical]
  exact SourceConditionalGraphDecoder.recovery_zero_iff _ _ _ _ value

theorem original_residual_realization (round : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    let depth := inventoryBound runtime + steps
    let retained := SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps
    let target := SourceCopyGraph.action depth retained (fieldRead depth depth value)
    let remaining := value - recovery runtime index steps target
    let copied := SourceCopyGraph.complexAction depth retained (word depth depth remaining)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (inventoryBound (sourceRound round copied)) (realizeWord round copied) = residual runtime index steps target := by
  dsimp only
  refine (SourceCopyGraph.original_copy_realization round _ _ _ _).trans ?_
  rw [map_sub, map_sub]
  rfl

theorem recovery_record (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    ∀ actor : Fin (inventoryBound runtime + steps + 1),
      type_of% (SourceGraphGrowth.native_record_read (inventoryBound runtime + steps)
        (Actor.currentPullback (inventoryBound runtime + steps) (inventoryBound runtime + steps)
          (recovery runtime index steps value)) actor) :=
  SourceGraphGrowth.native_record_read _ _

end
end SourceGraphRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
